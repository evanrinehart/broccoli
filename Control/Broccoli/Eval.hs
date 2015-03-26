{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
module Control.Broccoli.Eval where

import Control.Applicative
import Data.List
import Data.Function
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
  EdgeE :: forall a b . a ~ (b,b) => X b -> E a
  InputE :: InHook a -> E a
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

type Time = Double
type Handler a = a -> Time -> IO ()

data Bias = Now | NowMinus deriving (Eq, Ord, Show, Read)

type InHook a = Int -> [Int] -> (Time -> Time) -> ([a] -> Time -> IO ()) -> IO ()

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

instance Monoid a => Monoid (X a) where
  mempty = pure mempty
  mappend x1 x2 = liftA2 mappend x1 x2

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
never = occurs []

-- | Merge all the occurrences from two events together.
unionE :: E a -> E a -> E a
unionE = UnionE

-- | An event with occurrences explicitly specified in ascending order.
occurs :: [(Time, a)] -> E a
occurs = ConstantE

-- | > atZero x = x `at` 0
atZero :: X a -> a
atZero = (`at` 0)

-- | A signal that remembers the most recent occurrence of an event.
-- Takes a value to output prior to any events.
trap :: a -> E a -> X a
trap = TrapX

justE :: E (Maybe a) -> E a
justE = JustE

-- | Like 'delayE' but the amount of delay is determined on a per-event basis.
delayE' :: E (a, Double) -> E a
delayE' = DelayE

-- | Delay occurrences of an event.
delayE :: Double -> E a -> E a
delayE dt e = delayE' (fmap (,dt) e)


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
  then timeWarp f undefined x
  else error "timeWarp': can't handle events. Try regular timeWarp."

-- | Event occurs on transitions in a piecewise constant signal. Doesn't
-- work on continuously varying signals.
edge :: X a -> E (a, a)
edge x = if containsTimeX x
  then error "edge: input not piecewise constant"
  else EdgeE x

timeOnlyX :: X a -> Bool
timeOnlyX arg = case arg of
  PureX _ -> True
  TimeX -> True
  FmapX _ x -> timeOnlyX x
  ApplX ff xx -> timeOnlyX ff && timeOnlyX xx
  TrapX _ _ -> False
  TimeWarpX _ _ x -> timeOnlyX x

containsTimeX :: X a -> Bool
containsTimeX arg = case arg of
  PureX _ -> False
  TimeX -> True
  FmapX _ x -> containsTimeX x
  ApplX ff xx -> containsTimeX ff || containsTimeX xx
  TrapX _ _ -> False
  TimeWarpX _ _ x -> containsTimeX x

-- | Measure the value of a signal at some time.
at :: X a -> Time -> a
at arg t = case arg of
  PureX v -> v
  TimeX -> t
  FmapX f x -> f (x `at` t)
  ApplX ff xx -> (ff `at` t) (xx `at` t)
  TrapX prim e -> case occZMSearch (occs e) t of
    Nothing -> prim
    Just (_,x) -> x
  TimeWarpX g _ x -> x `at` (g t)

-- | List of all the occurrences of an event.
occs :: E a -> [(Time, a)]
occs arg = case arg of
  ConstantE os -> os
  FmapE f e -> map (fmap f) (occs e)
  JustE e -> (catMaybes . map sequenceA) (occs e)
  UnionE e1 e2 -> merge (comparing fst) (occs e1) (occs e2)
  DelayE e -> sortBy (comparing fst) (map delay (occs e))
  SnapshotE bias cons x e -> evalSnapshot bias cons ph0 phs (occs e) where
    (ph0, phs) = allPhases x
  EdgeE x -> allTrans x
  InputE _ -> []
  DebugE _ e -> occs e

evalSnapshot :: Bias
             -> (a -> b -> c)
             -> (Time -> a)
             -> [(Time, Time -> a)]
             -> [(Time, b)]
             -> [(Time, c)]
evalSnapshot _    _    _   _                 []             = []
evalSnapshot bias cons ph  []                ((t,v):os)     =
  (t, cons (ph t) v) : evalSnapshot bias cons ph [] os
evalSnapshot bias cons ph0 l1@((t1,ph1):phs) l2@((t2,v):os) =
  case compare t1 t2 of
    LT -> evalSnapshot bias cons ph1 phs l2
    GT -> (t2, cons (ph0 t2) v) : evalSnapshot bias cons ph0 l1 os
    EQ -> case bias of
      Now -> (t1, cons (ph1 t1) v) : evalSnapshot bias cons ph0 l1 os
      NowMinus -> (t1, cons (ph0 t1) v) : evalSnapshot bias cons ph0 l1 os

allPhases :: X a -> (Time -> a, [(Time, Time -> a)])
allPhases arg = case arg of
  PureX v -> (const v, [])
  TimeX -> (id, [])
  FmapX f x -> let (ph0, phs) = allPhases x in
    (f . ph0, map (\(t, ph) -> (t, f . ph)) phs)
  ApplX ff xx -> allApplPhases ff xx
  TrapX prim e -> (const prim, map f . groupBy (on (==) fst) . occs $ e) where
    f os = let (t, v) = last os in (t, const v)
  TimeWarpX w wi x -> case warp w of
    Forward -> let (ph0, phs) = allPhases x in
      (ph0 . w, map (\(t,ph) -> (wi t, ph . w)) phs)
    Backward -> case allPhases x of
      (ph0, []) -> (ph0 . w, [])
      (ph0, phs) ->
        let phs' = reverse (rezip ph0 phs) in
        let (_,final) = last phs in
        (final . w, map (\(ph, t) -> (wi t, ph . w))  phs')

allTrans :: X a -> [(Time, (a,a))]
allTrans arg = zipWith f ((undefined,ph0):phs) phs where
  (ph0, phs) = allPhases arg
  f (_,ph0') (t,ph1) = (t, (ph0' t, ph1 t))

allApplPhases :: X (a -> b) -> X a -> (Time -> b, [(Time, Time -> b)])
allApplPhases ff xx = ans where
  (f0,fphs) = allPhases ff
  (x0,xphs) = allPhases xx
  y0 = f0 <*> x0
  ans = (y0, k f0 x0 fphs xphs)
  k _ _ [] [] = []
  k f _ [] ((t, x'):xs) = (t, f <*> x') : k f x' [] xs
  k _ x ((t, f'):fs) [] = (t, f' <*> x) : k f' x fs []
  k f x l1@((t1, f'):fs) l2@((t2,x'):xs) = case compare t1 t2 of
    EQ -> (t1, f' <*> x') : k f' x' fs xs
    LT -> (t1, f' <*> x ) : k f' x fs l2
    GT -> (t2, f  <*> x') : k f x' l1 xs

rezip :: (Time -> a) -> [(Time, Time -> a)] -> [(Time -> a, Time)]
rezip _ [] = []
rezip ph0 ((t1,ph1):phs) = (ph0,t1) : rezip ph1 phs

w t = 10 - t/2
wi t = 20 - 2*t
e1 = occurs [(2, (1)), (4, (7)), (6, (5))]
e2 = occurs [(3, 0), (4, 1), (4, 2), (5, 10)]
x3 = (liftA2 (+) (trap (-1) e1) (trap (-1) e2))
e4 = edge x3
e5 = e4 <> occurs [(2.5, q 90), (4, q 40), (10,q 0), (10, q 2), (11, q 9)]
e6 = e4 <> delayE 1 (occurs [(3, q 40)])
q x = (x,x)

delay :: (Time, (a, Double)) -> (Time, a)
delay (t, (x, dt)) = (t + dt, x)

occZMSearch :: [(Time, a)] -> Time -> Maybe (Time, a)
occZMSearch hay t = case span (\(t',_) -> t' <= t) hay of
  ([], _) -> Nothing
  (os, _) -> Just (last os)

phaseMinusSearch :: (Time -> a) -> [(Time, Time -> a)] -> Time -> (Time -> a)
phaseMinusSearch ph0 hay t = case span (\(t',_) -> t' < t) hay of
  ([], _) -> ph0
  (phs, _) -> let (_,ph) = last phs in ph

primPhase :: X a -> (Time -> a)
primPhase x = fst (allPhases x)


-- merge two sorted lists into another sorted list lazily
merge :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
merge _ [] ys = ys
merge _ xs [] = xs
merge comp (x:xs) (y:ys) = case comp x y of
  EQ -> x:merge comp xs (y:ys)
  LT -> x:merge comp xs (y:ys)
  GT -> y:merge comp (x:xs) ys

srToPeriod :: Int -> Double
srToPeriod = abs . recip . realToFrac

data WarpDirection = Forward | Backward deriving (Eq, Show)

warp :: (Time -> Time) -> WarpDirection
warp g = case compare (g 0) (g 1) of
  LT -> Forward
  EQ -> error "bad time warp"
  GT -> Backward

prop_occurs :: Eq a => [(Time,a)] -> Bool
prop_occurs os = occs (occurs os) == os

prop_fmap :: Eq b => Fun a b -> E a -> Bool
prop_fmap (Fun _ f) e = occs (f <$> e) == map (fmap f) (occs e)

prop_justE :: Eq a => E (Maybe a) -> Bool
prop_justE e = catMaybes (map f (occs e)) == occs (JustE e) where
  f (_, Nothing) = Nothing
  f (t, Just v) = Just (t,v)

prop_unionE :: Eq a => E a -> E a -> Bool
prop_unionE e1 e2 = merge (comparing fst) (occs e1) (occs e2) == occs (e1 <> e2)

prop_unionE2 :: Bool
prop_unionE2 = merge (comparing fst) (occs e1) (occs e2) == occs (e1 <> e2) where
  e1 = occurs [(-1, 'a'), (0,'b'), (1,'c')]
  e2 = occurs [(0, 'd'), (1,'e'), (2,'f')]

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
  ans = [(0, ('z','a')), (1, ('d','b')), (2, ('e','c'))]

prop_snapshot4 :: Bool
prop_snapshot4 = occs (SnapshotE Now (,) x e) == ans where
  e = occurs [(-1, 'a'), (0, 'b'), (1, 'c')]
  x = TimeWarpX negate negate (TrapX 'z' (occurs [(-1,'d'), (0,'e'), (1,'f')]))
  ans = [(-1, ('f','a')), (0, ('e','b')), (1, ('d','c'))]

prop_snapshot5 :: Bool
prop_snapshot5 = occs (SnapshotE NowMinus (,) x e) == ans where
  e = occurs [(-1, 'a'), (0, 'b'), (1, 'c')]
  x = TimeWarpX negate negate (TrapX 'z' (occurs [(-1,'d'), (0,'e'), (1,'f')]))
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

{-
instance Show (X a) where
  show arg = case arg of
    PureX _ -> "PureX ?"
    TimeX -> "TimeX"
    FmapX _ _ -> "FmapX ? ?"
    ApplX _ _ -> "ApplX ? ?"
    TrapX _ _ -> "TrapX ? ?"
    TimeWarpX _ _ _ -> "TimeWarpX ? ? ?"
-}
    

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
