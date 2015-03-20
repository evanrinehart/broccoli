{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Eval where

import Control.Applicative
import Data.List
import Data.Ord
import Data.Monoid
import Data.Maybe
import Data.Traversable

import Prog

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
  SnapshotE e sig -> case findOcc e t test of
    Nothing -> Nothing
    Just (tOcc, x) -> let g = findPhase sig tOcc (occPhase test)
                      in Just (tOcc, (x, g tOcc))
  InputE _ -> Nothing
  Accum1E prim e -> case findOcc e t test of
    Nothing -> Nothing
    Just (tOcc,b) -> case findOcc e tOcc (occLose test) of
      Nothing -> Just (tOcc, (prim, b))
      Just (_, a) -> Just (tOcc, (a,b))
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
  SnapshotE e sig -> map f (allOccs e) where
    f (t, x) = let v = sampleX sig t in (t, (x,v))
  InputE _ -> []
  Accum1E prim e -> foldOccs prim (allOccs e)
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

tieBreakUnionForward  (u,x) (v,y) = if u <= v then (u,x) else (v,y)
tieBreakUnionBackward (u,x) (v,y) = if v <= u then (v,x) else (u,y)

occForwardTime = OccTest
  { occHay = undefined
  , occRast = undefined
  , occUnion = tieBreakUnionForward
  , occPhase = phaseMinus
  , occLose = occM }

occBackwardTime = OccTest
  { occHay = undefined
  , occRast = undefined
  , occUnion = tieBreakUnionBackward
  , occPhase = phasePlus
  , occLose = occP }

occZM = occForwardTime
  { occHay = \hay t -> case span (\(t',_) -> t' <= t) hay of
      ([], _) -> Nothing
      (os, _) -> Just (last os)
  , occRast = \t -> realToFrac (floor (t / period) :: Integer) * period } 

occM = occForwardTime
  { occHay = \hay t -> case span (\(t',_) -> t' < t) hay of
      ([], _) -> Nothing
      (os, _) -> Just (last os)
  , occRast = \t -> let u = realToFrac (floor (t / period) :: Integer) * period 
                    in if u == t then u - period else u
  } 

occZP = occBackwardTime
  { occHay = \hay t -> case span (\(t',_) -> t' < t) hay of
      (_, []) -> Nothing
      (_, o:_) -> Just o
  , occRast = \t -> realToFrac (ceiling (t / period) :: Integer) * period } 

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

phaseMinus = PhaseTest
  { phaseOcc = occM
  , phaseReverse = phasePlus }

phasePlus = PhaseTest
  { phaseOcc = occP
  , phaseReverse = phaseMinus }
