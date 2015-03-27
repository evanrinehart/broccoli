{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
module Control.Broccoli.Eval where

import Control.Applicative
import Data.List
import Data.Ord
import Data.Monoid
import Data.Maybe
import Control.Comonad
import Test.QuickCheck
import Test.QuickCheck.Function
import Data.Map (Map)
import qualified Data.Map as M

import Debug.Trace
import Unsafe.Coerce

-- | @E a@ represents events with values of type @a@.
-- 
-- > E a = [(Time, a)]
data E a where
  ConstantE :: [(Time, a)] -> E a
  FmapE :: forall a b . (b -> a) -> E b -> E a
  JustE :: E (Maybe a) -> E a
  UnionE :: E a -> E a -> E a
  DelayE :: Integer -> Double -> E a -> E a
  SnapshotE :: forall a b c . Integer -> Bias -> (c -> b -> a) -> X c -> E b -> E a
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


type Time = Double
type Handler a = a -> Time -> IO ()

data Bias = Now | NowMinus deriving (Eq, Ord, Show, Read)

type InHook a = Int -> [Int] -> (Time -> Time) -> ([a] -> Time -> IO ()) -> IO ()


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

-- | Delay occurrences of an event.
delayE :: Double -> E a -> E a
delayE dt e = DelayE 0 dt e 


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

-- | When the event occurs the value of the signal immediately before that
-- time will be captured. Therefore the output can feed back into the input.
snapshot :: (a -> b -> c) -> X a -> E b -> E c
snapshot = SnapshotE 0 NowMinus

-- | Like 'snapshot' but captures the value 'at' the time of the event.
-- Therefore the input cannot depend on the output.
snapshot' :: (a -> b -> c) -> X a -> E b -> E c
snapshot' = SnapshotE 0 Now

-- | Event occurs on transitions in a piecewise constant signal. Doesn't
-- work on continuously varying signals.
edge :: X a -> E (a, a)
edge x = if containsTimeX x
  then error "edge: input not piecewise constant"
  else EdgeE x


at :: X a -> Time -> a
at x t = case nextTimeX x of
  Nothing -> phaseX x t
  Just t' -> if t < t'
    then phaseX x t
    else let foo = tailX x in foo `at` t

occs :: E a -> [(Time, a)]
occs e = case nextTimeE e of
  Nothing -> []
  Just t -> let (v,e') = headE e in (t, v) : occs e'

-- divide a non-never event into first and rest occurrences
headE :: E a -> (a, E a)
headE arg = case arg of
  ConstantE [] -> error "headE []"
  ConstantE ((t,v):os) -> (v, ConstantE os)
  FmapE f e -> let (v,e') = headE e in (f v, FmapE f e')
  JustE e -> let (v, e') = headJustE e in (v, JustE e')
  UnionE e1 e2 ->
    let mt1 = nextTimeE e1 in
    let mt2 = nextTimeE e2 in
    if mLTE mt1 mt2
      then let (v,e') = headE e1 in (v, UnionE e' e2)
      else let (v,e') = headE e2 in (v, UnionE e1 e')
  DelayE _ delta e -> headE e
  SnapshotE name bias cons x e -> ans where
    (v2,e') = headE e
    Just t = nextTimeE e
    v1 = case nextTimeX x of
      Nothing -> phaseX x t
      Just t' -> if t <= t' then phaseX x t else error "fuck"
    x' = case nextTimeX x of
      Nothing -> x
      Just t' -> if t < t' then x else tailX x
    v = cons v1 v2
    ans = (v, SnapshotE name bias cons x' e')
  EdgeE x -> case nextTimeX x of
    Nothing -> error "headE nonsense 1"
    Just t -> ((ph t, ph' t), EdgeE (tailX x)) where
      ph = phaseX x
      ph' = phaseX (tailX x)
  InputE _ -> error "headE input"
  DebugE _ e -> headE e

-- drop the current phase and replace with next phase, unless that is nonsense
tailX :: X a -> X a
tailX arg = case arg of
  PureX v -> error "tailX pure"
  TimeX -> error "tailX time"
  FmapX f x -> FmapX f (tailX x)
  ApplX ff xx -> case nextTimeX ff of
    Nothing -> case nextTimeX xx of
      Nothing -> error "tailX nonsense 1"
      Just _ -> ApplX ff (tailX xx)
    Just t1 -> case nextTimeX xx of
      Nothing -> ApplX (tailX ff) xx
      Just t2 -> case compare t1 t2 of
        LT -> ApplX (tailX ff) xx
        GT -> ApplX ff (tailX xx)
        EQ -> ApplX (tailX ff) (tailX xx)
  TrapX v e -> case nextTimeE e of
    Nothing -> error "tailX nonsense 2"
    Just t -> let (v', e') = lastO e t in TrapX v' e'
  TimeWarpX w wi x -> TimeWarpX w wi (tailX x)

-- the "current phase" of a signal
phaseX :: X a -> Time -> a
phaseX arg t = case arg of
  PureX v -> v
  TimeX -> t
  FmapX f x -> f (phaseX x t)
  ApplX ff xx -> (phaseX ff t) (phaseX xx t)
  TrapX v e -> v
  TimeWarpX w _ x -> phaseX x (w t)

-- find next transition time if any
nextTimeX :: X a -> Maybe Time
nextTimeX arg = case arg of
  PureX v -> Nothing
  TimeX -> Nothing
  FmapX _ x -> nextTimeX x
  ApplX ff xx -> case catMaybes [nextTimeX ff, nextTimeX xx] of
    [] -> Nothing
    ts -> Just (minimum ts)
  TrapX v e -> nextTimeE e
  TimeWarpX _ wi x -> fmap wi (nextTimeX x)

-- find next occurrence time if any
nextTimeE :: E a -> Maybe Time
nextTimeE arg = case arg of
  ConstantE [] -> Nothing
  ConstantE ((t,v):_) -> Just t
  FmapE _ e -> nextTimeE e
  JustE e -> nextJust e
  UnionE e1 e2 -> case catMaybes [nextTimeE e1, nextTimeE e2] of
    [] -> Nothing
    ts -> Just (minimum ts)
  DelayE _ delta e -> fmap (+delta) (nextTimeE e)
  SnapshotE _ _ _ _ e -> nextTimeE e
  EdgeE x -> nextTimeX x
  InputE _ -> Nothing
  DebugE _ e -> nextTimeE e

nextJust :: E (Maybe a) -> Maybe Time
nextJust e = case nextTimeE e of
  Nothing -> Nothing
  Just t -> case headE e of
    (Just v, e') -> Just t
    (Nothing, e') -> nextJust e'

headJustE :: E (Maybe a) -> (a, E (Maybe a))
headJustE e = case headE e of
  (Just v, e') -> (v, e')
  (Nothing, e') -> headJustE e'

-- a trap takes the last of a series of occurrences happening at the same time
lastO :: E a -> Time -> (a, E a)
lastO e t =
  let (v,e') = headE e in
  case nextTimeE e' of
    Nothing -> (v,e')
    Just t' | t' == t -> lastO e' t
            | otherwise -> (v,e')

shX :: X a -> String
shX arg = case arg of
  PureX _ -> "Pure"
  TimeX -> "Time"
  FmapX _ x -> "Fmap"
  ApplX _ _ -> "Appl"
  TrapX _ _ -> "Trap"
  TimeWarpX _ _ _ -> "Warp"

shE :: E a -> String
shE arg = case arg of
  ConstantE _ -> "Constant"
  FmapE _ e -> "FmapE"
  JustE e -> "Just"
  UnionE e1 e2 -> "Union"
  DelayE _ delta e -> "Delay"
  SnapshotE _ _ _ _ e -> "Snap"
  EdgeE x -> "Edge"
  InputE _ -> "Input"
  DebugE _ e -> "Debug"

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

mLTE :: Ord a => Maybe a -> Maybe a -> Bool
mLTE (Just a) (Just b) = a <= b
mLTE (Just _) Nothing = True
mLTE Nothing (Just _) = False
mLTE Nothing Nothing = error "mLTE nonsense"


rezip :: (Time -> a) -> [(Time, Time -> a)] -> [(Time -> a, Time)]
rezip _ [] = []
rezip ph0 ((t1,ph1):phs) = (ph0,t1) : rezip ph1 phs

-- experiments
w t = 10 - t/2
wi t = 20 - 2*t
e1 = occurs [(2, (1)), (4, (7)), (6, (5))]
e2 = occurs [(3, 0), (4, 1), (4, 2), (5, 10)]
x3 = (liftA2 (+) (trap (-1) e1) (trap (-1) e2))
e4 = edge x3
e5 = e4 <> occurs [(2.5, q 90), (4, q 40), (10,q 0), (10, q 2), (11, q 9)]
e6 = e4 <> delayE 1 (occurs [(3, q 40)])
q x = (x,x)
e7 = edge (timeWarp w wi x3)

counter :: E () -> X Int
counter bump = out where
  out = trap 0 e2
  e2 = SnapshotE 0 NowMinus const next bump
  next = (+1) <$> out

counter' :: E () -> X Int
counter' bump = out where
  out = trap 0 e2
  e2 = SnapshotE 0 NowMinus const next bump
  next = (+1) <$> out
------


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
prop_snapshot1 x e = occs (SnapshotE 0 Now (,) x e) == fmap f (occs e) where
  f (t, v) = (t, (x `at` t, v))

prop_snapshot2 :: Bool
prop_snapshot2 = occs (SnapshotE 0 Now (,) x e) == fmap f (occs e) where
  e = occurs [(0, 'a'), (1, 'b'), (2, 'c')]
  x = TrapX 'z' (occurs [(0,'d'), (1,'e'), (2,'f')])
  f (t, v) = (t, (x `at` t, v))

prop_snapshot3 :: Bool
prop_snapshot3 = occs (SnapshotE 0 NowMinus (,) x e) == ans where
  e = occurs [(0, 'a'), (1, 'b'), (2, 'c')]
  x = TrapX 'z' (occurs [(0,'d'), (1,'e'), (2,'f')])
  ans = [(0, ('z','a')), (1, ('d','b')), (2, ('e','c'))]

prop_snapshot4 :: Bool
prop_snapshot4 = occs (SnapshotE 0 Now (,) x e) == ans where
  e = occurs [(-1, 'a'), (0, 'b'), (1, 'c')]
  x = TimeWarpX negate negate (TrapX 'z' (occurs [(-1,'d'), (0,'e'), (1,'f')]))
  ans = [(-1, ('f','a')), (0, ('e','b')), (1, ('d','c'))]

prop_snapshot5 :: Bool
prop_snapshot5 = occs (SnapshotE 0 NowMinus (,) x e) == ans where
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



data Progress = Progress
  { prDelayNames :: [Integer]
  , prSnapEvents :: (Map Integer (E Any)) }

prAddDN :: Progress -> Integer -> Progress
prAddDN pr i = pr { prDelayNames = i : prDelayNames pr }

prAddSnapEvent :: Progress -> Integer -> E a -> Progress
prAddSnapEvent pr name e = pr { prSnapEvents = f (prSnapEvents pr) } where
  f m = M.insert name (unsafeCoerce e) m

-- not type safe but it isn't visible to the client
prLookupEvent :: Progress -> Integer -> E a -> E a
prLookupEvent pr name eDef = case M.lookup name (prSnapEvents pr) of
  Nothing -> eDef
  Just e -> (unsafeCoerce e)

prEmpty :: Progress
prEmpty = Progress [] M.empty
