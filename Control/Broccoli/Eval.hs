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

import Control.Broccoli.Types

-- | An event that never happens.
never :: E a
never = ConstantE []

-- | Merge all the occurrences from two events together.
unionE :: E a -> E a -> E a
unionE = UnionE


-- | Measure the value of a signal at some time.
at :: X a -> Time -> a
at = sampleX

-- | List of all the occurrences of an event.
occs :: E a -> [(Time, a)]
occs = allOccs

-- | The value of a signal at @t = 0@
atZero :: X a -> a
atZero = (`at` 0)

-- evaluate a program at a particular time assuming no external stimulus
sampleX :: X a -> Time -> a
sampleX arg t = case arg of
  PureX x -> x
  TimeX -> t
  FmapX f sig -> f (sampleX sig t)
  ApplX ff xx -> (sampleX ff t) (sampleX xx t)
  TrapX prim e -> case findOcc e t occZM of
    Nothing -> prim
    Just (_,x) -> x
  MultiX sigs -> map (\sig -> sampleX sig t) sigs
  TimeWarpX g _ sig -> sampleX sig (g t)

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
  RasterE -> Just (occRast test t, ())

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
  TimeWarpX g _ sig -> case compare (g 0) (g 1) of
    EQ -> const (sampleX sig (g 0))
    LT -> findPhase sig (g t) test
    GT -> findPhase sig (g t) (phaseReverse test)

findJust :: E (Maybe a) -> Time -> OccTest -> Maybe (Time, a)
findJust e t test = case findOcc e t test of
  Nothing -> Nothing
  Just (tOcc, Nothing) -> findJust e tOcc test
  Just (tOcc, Just x) -> Just (tOcc, x)

allOccs :: E a -> [(Time, a)]
allOccs arg = case arg of
  ConstantE os -> reverse os
  FmapE f e -> map (fmap f) (allOccs e)
  JustE e -> (catMaybes . map sequenceA) (allOccs e)
  UnionE e1 e2 -> (allOccs e1) ++ (allOccs e2)
  DelayE e -> sortBy (comparing fst) (map delay (allOccs e))
  SnapshotE cons sig e -> map f (allOccs e) where
    f (t, x) = let v = sampleX sig t in (t, cons v x)
  InputE _ -> []
  RasterE -> map (\i -> (i*period, ())) [0..]

foldOccs :: a -> [(Time, a)] -> [(Time, (a,a))]
foldOccs _ [] = []
foldOccs prev ((t,x):os) = (t,(prev,x)) : foldOccs x os

-- cast a discretely changing signal as an event if possible
unX :: X a -> Maybe (E a)
unX arg = case arg of
  PureX _ -> Just mempty
  TimeX -> Nothing
  FmapX f sig -> fmap (FmapE f) (unX sig)
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
  extract sig = sig `at` 0
  duplicate sig = f <$> sig <*> TimeX where
    f x t = TimeWarpX (subtract t) (+ t) sig
