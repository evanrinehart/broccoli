{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
module Control.Broccoli.Eval where

import Control.Applicative
import Data.List
import Data.Ord
import Data.Monoid
import Data.Maybe
import Data.Traversable
import Control.Comonad
import Test.QuickCheck
import Test.QuickCheck.Function

-- | @E a@ represents events with values of type @a@.
-- 
-- > E a = [(Time, a)]
data E a where
  ConstantE :: [(Time, a)] -> E a
  FmapE :: forall a b . (b -> a) -> E b -> E a
  JustE :: E (Maybe a) -> E a
  UnionE :: E a -> E a -> E a
  DelayE :: E (a, Double) -> E a
  SnapshotE :: forall a b c . Bias -> (c -> b -> a) -> X c -> E b -> E a
  InputE :: ((a -> Time -> IO ()) -> IO ()) -> E a
  DebugE :: (a -> String) -> E a -> E a

-- | @X a@ represents time signals with values of type @a@.
-- 
-- > X a = Time -> a
data X a where
  PureX :: a -> X a
  TimeX :: a ~ Time => X a
  FmapX :: forall a b . (b -> a) -> X b -> X a
  ApplX :: forall a b . X (b -> a) -> X b -> X a
  TrapX :: a -> E a -> X a
  TimeWarpX :: (Time -> Time) -> (Time -> Time) -> X a -> X a
  --XF :: forall a b . ((Time -> b) -> (Time -> a)) -> X b -> X a

-- XF h x `at` t = h (x `at`) t

type Time = Double
type Handler a = a -> Time -> IO ()

data Bias = Now | NowMinus deriving (Eq, Ord, Show, Read)

toggleBias :: Bias -> Bias
toggleBias Now = NowMinus
toggleBias NowMinus = Now

instance Functor E where
  fmap f e = FmapE f e

instance Functor X where
  fmap f sig = FmapX f sig

instance Applicative X where
  pure x = PureX x
  ff <*> xx = ApplX ff xx

-- | mempty = 'never', mappend = 'unionE'
instance Monoid (E a) where
  mempty = never
  mappend = unionE
  
-- | extract = 'atZero', duplicate @x@ at @t@ is 'timeShift' @t x@
instance Comonad X where
  extract = atZero
  duplicate x = fmap (\t -> timeShift t x) time

-- | Seconds since start of simulation.
time :: X Time
time = TimeX

-- | An event that never happens.
never :: E a
never = ConstantE []

-- | Merge all the occurrences from two events together.
unionE :: E a -> E a -> E a
unionE = UnionE

-- | An event with occurrences explicitly specified in ascending order.
occurs :: [(Time, a)] -> E a
occurs = ConstantE

-- | > atZero x = x `at` 0
atZero :: X a -> a
atZero = (`at` 0)

-- | Shift a signal forward in time. A negative shift shifts back in time.
timeShift :: Double -> X a -> X a
timeShift delta sig = timeWarp (subtract delta) (+ delta) sig

-- | Time warp a signal. The inverse of the warp function must exist and
-- be provided.
timeWarp :: (Time -> Time) -> (Time -> Time) -> X a -> X a
timeWarp = TimeWarpX

-- | Like 'timeWarp' but doesn't require an inverse. Doesn't work with events.
timeWarp' :: (Time -> Time) -> X a -> X a
timeWarp' f x = if timeOnlyX x
  then TimeWarpX f undefined x
  else error "timeWarp': can't handle events. Try regular timeWarp."

timeOnlyX :: X a -> Bool
timeOnlyX arg = case arg of
  PureX _ -> True
  TimeX -> True
  FmapX _ x -> timeOnlyX x
  ApplX ff xx -> timeOnlyX ff && timeOnlyX xx
  TrapX _ _ -> False
  TimeWarpX _ _ x -> timeOnlyX x

-- | Measure the value of a signal at some time.
at :: X a -> Time -> a
at arg t = case arg of
  PureX v -> v
  TimeX -> t
  FmapX f x -> f (x `at` t)
  ApplX ff xx -> (ff `at` t) (xx `at` t)
  TrapX prim e -> case findOcc e t occZM of
    Nothing -> prim
    Just (_,x) -> x
  TimeWarpX g _ x -> x `at` (g t)

findOcc :: E a -> Time -> OccTest -> Maybe (Time, a)
findOcc arg t test = case arg of
  ConstantE os -> occHay test os t
  FmapE f e -> fmap (fmap f) (findOcc e t test) where
  JustE e -> findJust e t test
  UnionE e1 e2 -> case findOcc e1 t test of
    Nothing -> case findOcc e2 t test of
      Nothing -> Nothing
      Just (x2, t2) -> Just (x2, t2)
    Just (t1, x1) -> case findOcc e1 t1 test of
      Nothing -> Just (t1, x1)
      Just (t2, x2) -> Just (occUnion test (t1,x1) (t2,x2))
  DelayE e -> occHay test (map delay (occs e)) t
  SnapshotE bias cons sig e -> case findOcc e t test of
    Nothing -> Nothing
    Just (tOcc, x) -> let g = findPhase sig tOcc (occPhase test bias)
                      in Just (tOcc, cons (g tOcc) x)
  InputE _ -> Nothing
  DebugE _ e -> findOcc e t test

findPhase :: X a -> Time -> PhaseTest -> (Time -> a)
findPhase arg t test = case arg of
  PureX v -> const v
  TimeX -> id
  FmapX f sig -> f . (findPhase sig t test)
  ApplX ff xx -> (findPhase ff t test) <*> (findPhase xx t test)
  TrapX prim e -> case findOcc e t (phaseOcc test) of
    Nothing -> const prim
    Just (_,x) -> const x
  TimeWarpX g _ x -> case warp g of
    Forward  -> findPhase x (g t) test . g
    Backward -> findPhase x (g t) (phaseReverse test) . g

findJust :: E (Maybe a) -> Time -> OccTest -> Maybe (Time, a)
findJust e t test = case findOcc e t test of
  Nothing -> Nothing
  Just (tOcc, Nothing) -> findJust e tOcc test
  Just (tOcc, Just x) -> Just (tOcc, x)

-- | List of all the occurrences of an event.
occs :: E a -> [(Time, a)]
occs arg = case arg of
  ConstantE os -> os
  FmapE f e -> map (fmap f) (occs e)
  JustE e -> (catMaybes . map sequenceA) (occs e)
  UnionE e1 e2 -> merge (comparing fst) (occs e1) (occs e2)
  DelayE e -> sortBy (comparing fst) (map delay (occs e))
  SnapshotE bias cons x e -> map f (occs e) where
    f (t, ev) = case bias of
      Now -> (t, cons (x `at` t) ev)
      NowMinus ->
        let g = findPhase x t phaseMinus in
        let xv = g t in
        (t, cons xv ev)
  InputE _ -> []
  DebugE _ e -> occs e

foldOccs :: a -> [(Time, a)] -> [(Time, (a,a))]
foldOccs _ [] = []
foldOccs prev ((t,x):os) = (t,(prev,x)) : foldOccs x os

delay :: (Time, (a, Double)) -> (Time, a)
delay (t, (x, dt)) = (t + dt, x)

-- the occurrence test: what is the next/most recent occurrence on or before
-- or after or strict before or after time t
data OccTest = OccTest
  { occHay :: forall a . [(Time, a)] -> Time -> Maybe (Time, a)
  , occUnion :: forall a . (Time, a) -> (Time, a) -> (Time, a)
  , occPhase :: Bias -> PhaseTest
  , occLose :: OccTest }

tieBreakUnionForward :: (Time,a) -> (Time,a) -> (Time,a)
tieBreakUnionForward  (u,x) (v,y) = if u <= v then (u,x) else (v,y)

tieBreakUnionBackward :: (Time,a) -> (Time,a) -> (Time,a)
tieBreakUnionBackward (u,x) (v,y) = if v <= u then (v,x) else (u,y)

occForwardTime :: OccTest
occForwardTime = OccTest
  { occHay = undefined
  , occUnion = tieBreakUnionForward
  , occPhase = phaseTestFromBias
  , occLose = occM }

occBackwardTime :: OccTest
occBackwardTime = OccTest
  { occHay = undefined
  , occUnion = tieBreakUnionBackward
  , occPhase = phaseTestFromBias . toggleBias
  , occLose = occP }

occZM :: OccTest
occZM = occForwardTime
  { occHay = \hay t -> case span (\(t',_) -> t' <= t) hay of
      ([], _) -> Nothing
      (os, _) -> Just (last os)
  }

occM :: OccTest
occM = occForwardTime
  { occHay = \hay t -> case span (\(t',_) -> t' < t) hay of
      ([], _) -> Nothing
      (os, _) -> Just (last os)
  } 

occZP :: OccTest
occZP = occBackwardTime
  { occHay = \hay t -> case span (\(t',_) -> t' < t) hay of
      (_, []) -> Nothing
      (_, o:_) -> Just o
  }

occP :: OccTest
occP = occBackwardTime
  { occHay = \hay t -> case span (\(t',_) -> t' <= t) hay of
      (_, []) -> Nothing
      (_, o:_) -> Just o
  }

-- phase test: what is the time signal at time t unless a transition occurred
-- at t in which case use the previous or the next phase depending.
data PhaseTest = PhaseTest
  { phaseOcc :: OccTest
  , phaseReverse :: PhaseTest }

phaseMinus :: PhaseTest
phaseMinus = PhaseTest
  { phaseOcc = occM
  , phaseReverse = phasePlus }

phasePlus :: PhaseTest
phasePlus = PhaseTest
  { phaseOcc = occP
  , phaseReverse = phaseMinus }


-- merge two sorted lists into another sorted list lazily
merge :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
merge _ [] ys = ys
merge _ xs [] = xs
merge comp (x:xs) (y:ys) = case comp x y of
  EQ -> x:merge comp xs (y:ys)
  LT -> x:merge comp xs (y:ys)
  GT -> y:merge comp (x:xs) ys


primPhase :: X a -> (Time -> a)
primPhase arg = case arg of
  PureX v -> const v
  TimeX -> id
  FmapX f x -> f . primPhase x
  ApplX ff xx -> primPhase ff <*> primPhase xx
  TrapX prim _ -> const prim
  TimeWarpX g _ x -> case warp g of
    Forward  -> primPhase x . g
    Backward -> finalPhase x . g

finalPhase :: X a -> (Time -> a)
finalPhase arg = case arg of
  PureX v -> const v
  TimeX -> id
  FmapX f x -> f . finalPhase x
  ApplX ff xx -> finalPhase ff <*> finalPhase xx
  TrapX prim e -> case occs e of
    [] -> const prim
    os -> const (snd (last os))
  TimeWarpX g _ x -> case warp g of
    Forward  -> finalPhase x . g
    Backward -> primPhase x . g

phaseTestFromBias :: Bias -> PhaseTest
phaseTestFromBias Now = phaseMinus { phaseOcc = occZM }
phaseTestFromBias NowMinus = phaseMinus

srToPeriod :: Int -> Double
srToPeriod = abs . recip . realToFrac

data WarpDirection = Forward | Backward deriving (Eq, Show)

warp :: (Time -> Time) -> WarpDirection
warp g = case compare (g 0) (g 1) of
  LT -> Forward
  EQ -> error "bad time warp"
  GT -> Backward



{-
 -
data E a where
  ConstantE :: [(Time, a)] -> E a
  FmapE :: forall a b . (b -> a) -> E b -> E a
  JustE :: E (Maybe a) -> E a
  UnionE :: E a -> E a -> E a
  DelayE :: E (a, Double) -> E a
  SnapshotE :: forall a b c . Bias -> (c -> b -> a) -> X c -> E b -> E a
  InputE :: ((a -> Time -> IO ()) -> IO ()) -> E a
  DebugE :: (a -> String) -> E a -> E a

-- | @X a@ represents time signals with values of type @a@.
-- 
-- > X a = Time -> a
data X a where
  PureX :: a -> X a
  TimeX :: a ~ Time => X a
  FmapX :: forall a b . (b -> a) -> X b -> X a
  ApplX :: forall a b . X (b -> a) -> X b -> X a
  TrapX :: a -> E a -> X a
  TimeWarpX :: (Time -> Time) -> (Time -> Time) -> X a -> X a
  --XF :: forall a b . ((Time -> b) -> (Time -> a)) -> X b -> X a
-}

prop_occurs :: Eq a => [(Time,a)] -> Bool
prop_occurs os = occs (occurs os) == os

prop_fmap :: Eq b => Fun a b -> E a -> Bool
prop_fmap (Fun _ f) e = occs (f <$> e) == map (fmap f) (occs e)

prop_justE :: Eq a => E (Maybe a) -> Bool
prop_justE e = catMaybes (map f (occs e)) == occs (JustE e) where
  f (t, Nothing) = Nothing
  f (t, Just v) = Just (t,v)

prop_unionE :: Eq a => E a -> E a -> Bool
prop_unionE e1 e2 = merge (comparing fst) (occs e1) (occs e2) == occs (e1 <> e2)

-- not exactly true due to floating point
{-
prop_delayE :: Eq a => Double -> E a -> Bool
prop_delayE delta e = all id (zipWith f (occs e) (occs e')) where
  f (t1,v1) (t2,v2) = t2 - t1 == delta && v1 == v2
  e' = DelayE (fmap (,delta) e)
-}

prop_snapshot1 :: Eq a => X a -> E a -> Bool
prop_snapshot1 x e = occs (SnapshotE Now (,) x e) == fmap f (occs e) where
  f (t, v) = (t, (x `at` t, v))

prop_snapshot2 :: Bool
prop_snapshot2 = occs (SnapshotE Now (,) x e) == fmap f (occs e) where
  e = occurs [(0, 'a'), (1, 'b'), (2, 'c')]
  x = TrapX 'z' (occurs [(0,'d'), (1,'e'), (2,'f')])
  f (t, v) = (t, (x `at` t, v))

prop_snapshot3 :: Bool
prop_snapshot3 = occs (SnapshotE NowMinus (,) x e) == ans where
  e = occurs [(0, 'a'), (1, 'b'), (2, 'c')]
  x = TrapX 'z' (occurs [(0,'d'), (1,'e'), (2,'f')])
  f (t, v) = (t, (x `at` t, v))
  ans = [(0, ('z','a')), (1, ('d','b')), (2, ('e','c'))]

prop_snapshot4 :: Bool
prop_snapshot4 = occs (SnapshotE Now (,) x e) == ans where
  e = occurs [(-1, 'a'), (0, 'b'), (1, 'c')]
  x = TimeWarpX negate negate (TrapX 'z' (occurs [(-1,'d'), (0,'e'), (1,'f')]))
  f (t, v) = (t, (x `at` t, v))
  ans = [(-1, ('f','a')), (0, ('e','b')), (1, ('d','c'))]

prop_snapshot5 :: Bool
prop_snapshot5 = occs (SnapshotE NowMinus (,) x e) == ans where
  e = occurs [(-1, 'a'), (0, 'b'), (1, 'c')]
  x = TimeWarpX negate negate (TrapX 'z' (occurs [(-1,'d'), (0,'e'), (1,'f')]))
  f (t, v) = (t, (x `at` t, v))
  ans = [(-1, ('z','a')), (0, ('f','b')), (1, ('e','c'))]

prop_warp1 :: Eq a => Time -> X a -> Bool
prop_warp1 t x = (TimeWarpX f undefined x) `at` t == x `at` (f t) where
  f u = u**3

prop_warp2 :: Eq a => Time -> a -> E a -> Bool
prop_warp2 t v0 e = (TimeWarpX f undefined x) `at` t == x `at` (f t) where
  x = TrapX v0 e
  f u = -u**3

prop_applX :: Eq b => Time -> X (Fun Int b) -> X Int -> Bool
prop_applX t ff xx = (liftA2 app ff xx) `at` t == app (ff `at` t) (xx `at` t) where
  app (Fun _ f) x = f x


instance Show a => Show (E a) where
  show e = "occurs " ++ show (occs e)

instance Show (X a) where
  show arg = case arg of
    PureX _ -> "PureX ?"
    TimeX -> "TimeX"
    FmapX _ _ -> "FmapX ? ?"
    ApplX ff xx -> "ApplX ? ?"
    TrapX prim e -> "TrapX ? ?"
    TimeWarpX g gInv x -> "TimeWarpX ? ? ?"
    

instance Arbitrary a => Arbitrary (E a) where
  arbitrary = (occurs . sortBy (comparing fst)) <$> listOf o where
    o = do
      t <- choose (-100, 100)
      v <- arbitrary
      return (t, v)

instance Arbitrary a => Arbitrary (X a) where
  arbitrary = oneof [boringGen, trapGen]

boringGen :: Arbitrary a => Gen (X a)
boringGen = do
  vs <- listOf1 arbitrary
  let l = length vs
  return $ (\t -> vs !! (floor t `mod` l)) <$> TimeX

trapGen :: Arbitrary a => Gen (X a)
trapGen = do
  e <- arbitrary
  v0 <- arbitrary
  return (TrapX v0 e)
