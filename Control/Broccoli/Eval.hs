{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Control.Broccoli.Eval where

import Control.Applicative
import Data.List
import Data.Ord
import Data.Monoid
import Data.Maybe
import Data.Traversable
import Control.Comonad

-- | @E a@ represents events with values of type @a@.
-- 
-- > E a = [(Time, a)]
data E a where
  ConstantE :: [(Time, a)] -> E a
  FmapE :: forall a b . (b -> a) -> E b -> E a
  JustE :: E (Maybe a) -> E a
  UnionE :: E a -> E a -> E a
  DelayE :: E (a, Double) -> E a
  SnapshotE :: forall a b c . (c -> b -> a) -> X c -> E b -> E a
  InputE :: ((a -> Time -> IO ()) -> IO ()) -> E a

-- | @X a@ represents time signals with values of type @a@.
-- 
-- > X a = Time -> a
data X a where
  PureX :: a -> X a
  TimeX :: a ~ Time => X a
  FmapX :: forall a b . (b -> a) -> X b -> X a
  ApplX :: forall a b . X (b -> a) -> X b -> X a
  TrapX :: a -> E a -> X a
  MultiX :: a ~ [b] => [X b] -> X a
  TimeWarpX :: (Time -> Time) -> (Time -> Time) -> X a -> X a
  --XF :: forall a b . ((Time -> b) -> (Time -> a)) -> X b -> X a

-- XF h x `at` t = h (x `at`) t

type Time = Double
type Handler a = a -> Time -> IO ()

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
  
-- | extract = 'atZero', duplicate @s@ at @t@ is 'timeShift' @t s@
instance Comonad X where
  extract = atZero
  duplicate x = fmap (\t -> timeShift t x) time

-- | Signal carrying the time since start of simulation in seconds.
time :: X Time
time = TimeX

-- | An event that never happens.
never :: E a
never = ConstantE []

-- | Merge all the occurrences from two events together.
unionE :: E a -> E a -> E a
unionE = UnionE

-- | An event with occurrences explicitly listed in ascending order.
occurs :: [(Time, a)] -> E a
occurs = ConstantE

-- | List of all the occurrences of an event.
occs :: E a -> [(Time, a)]
occs = allOccs

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
  then TimeWarpX f id x
  else error "timeWarp' can't handle events. Try timewarp."

timeOnlyX :: X a -> Bool
timeOnlyX arg = case arg of
  PureX _ -> True
  TimeX -> True
  FmapX _ x -> timeOnlyX x
  ApplX ff xx -> timeOnlyX ff && timeOnlyX xx
  TrapX _ _ -> False
  MultiX xs -> and (map timeOnlyX xs)
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
  MultiX xs -> map (`at` t) xs
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
  DelayE e -> occHay test (map delay (allOccs e)) t
  SnapshotE cons sig e -> case findOcc e t test of
    Nothing -> Nothing
    Just (tOcc, x) -> let g = findPhase sig tOcc (occPhase test)
                      in Just (tOcc, cons (g tOcc) x)
  InputE _ -> Nothing

findPhase :: X a -> Time -> PhaseTest -> (Time -> a)
findPhase arg t test = case arg of
  PureX x -> const x
  TimeX -> id
  FmapX f sig -> f . (findPhase sig t test)
  ApplX ff xx -> (findPhase ff t test) <*> (findPhase xx t test)
  TrapX prim e -> case findOcc e t (phaseOcc test) of
    Nothing -> const prim
    Just (_,x) -> const x
  MultiX sigs -> let phases = map (\sig -> findPhase sig t test) sigs
                 in \u -> map ($ u) phases
  TimeWarpX g _ x -> case compare (g 0) (g 1) of
    EQ -> const (x `at` (g 0))
    LT -> findPhase x (g t) test
    GT -> findPhase x (g t) (phaseReverse test)

findJust :: E (Maybe a) -> Time -> OccTest -> Maybe (Time, a)
findJust e t test = case findOcc e t test of
  Nothing -> Nothing
  Just (tOcc, Nothing) -> findJust e tOcc test
  Just (tOcc, Just x) -> Just (tOcc, x)

allOccs :: E a -> [(Time, a)]
allOccs arg = case arg of
  ConstantE os -> os
  FmapE f e -> map (fmap f) (allOccs e)
  JustE e -> (catMaybes . map sequenceA) (allOccs e)
  UnionE e1 e2 -> (allOccs e1) ++ (allOccs e2)
  DelayE e -> sortBy (comparing fst) (map delay (allOccs e))
  SnapshotE cons x e -> map f (allOccs e) where
    f (t, ev) = let g = findPhase x t phaseMinus
                    xv = g t
                in (t, cons xv ev)
  InputE _ -> []

foldOccs :: a -> [(Time, a)] -> [(Time, (a,a))]
foldOccs _ [] = []
foldOccs prev ((t,x):os) = (t,(prev,x)) : foldOccs x os

-- cast a discretely changing signal as an event if possible
unX :: X a -> Maybe (E a)
unX arg = case arg of
  PureX _ -> Just mempty
  TimeX -> Nothing
  FmapX f x -> fmap (FmapE f) (unX x)
  ApplX _ _ -> Nothing
  TrapX _ e -> Just e
  TimeWarpX _ _ _ -> Nothing
  MultiX _ -> Nothing
  
delay :: (Time, (a, Double)) -> (Time, a)
delay (t, (x, dt)) = (t + dt, x)

-- the occurrence test: what is the next/most recent occurrence on or before
-- or after or strict before or after time t
data OccTest = OccTest
  { occHay :: forall a . [(Time, a)] -> Time -> Maybe (Time, a)
  , occUnion :: forall a . (Time, a) -> (Time, a) -> (Time, a)
  , occPhase :: PhaseTest
  , occLose :: OccTest
  , occRast :: Time -> Time }

period :: Double
period = 0.02

tieBreakUnionForward :: (Time,a) -> (Time,a) -> (Time,a)
tieBreakUnionForward  (u,x) (v,y) = if u <= v then (u,x) else (v,y)

tieBreakUnionBackward :: (Time,a) -> (Time,a) -> (Time,a)
tieBreakUnionBackward (u,x) (v,y) = if v <= u then (v,x) else (u,y)

occForwardTime :: OccTest
occForwardTime = OccTest
  { occHay = undefined
  , occRast = undefined
  , occUnion = tieBreakUnionForward
  , occPhase = phaseMinus
  , occLose = occM }

occBackwardTime :: OccTest
occBackwardTime = OccTest
  { occHay = undefined
  , occRast = undefined
  , occUnion = tieBreakUnionBackward
  , occPhase = phasePlus
  , occLose = occP }

occZM :: OccTest
occZM = occForwardTime
  { occHay = \hay t -> case span (\(t',_) -> t' <= t) hay of
      ([], _) -> Nothing
      (os, _) -> Just (last os)
  , occRast = \t -> realToFrac (floor (t / period) :: Integer) * period } 

occM :: OccTest
occM = occForwardTime
  { occHay = \hay t -> case span (\(t',_) -> t' < t) hay of
      ([], _) -> Nothing
      (os, _) -> Just (last os)
  , occRast = \t -> let u = realToFrac (floor (t / period) :: Integer) * period 
                    in if u == t then u - period else u
  } 

occZP :: OccTest
occZP = occBackwardTime
  { occHay = \hay t -> case span (\(t',_) -> t' < t) hay of
      (_, []) -> Nothing
      (_, o:_) -> Just o
  , occRast = \t -> realToFrac (ceiling (t / period) :: Integer) * period } 

occP :: OccTest
occP = occBackwardTime
  { occHay = \hay t -> case span (\(t',_) -> t' <= t) hay of
      (_, []) -> Nothing
      (_, o:_) -> Just o
  , occRast = \t -> let u = realToFrac (ceiling (t / period) :: Integer) * period 
                    in if u == t then u + period else u
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

