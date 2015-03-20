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
  TrapX prim e -> case lastOcc e t of
    Nothing -> prim
    Just (_,x) -> x
  TimeWarpX g _ sig -> sampleX sig (g t)
  InputX prim _ -> prim

-- most recent occurrence of an event on or before t, if any
lastOcc :: E a -> Time -> Maybe (Time, a)
lastOcc arg t = case arg of
  ConstantE [] -> Nothing
  ConstantE (o:os) -> if fst o <= t then Just o else lastOcc (ConstantE os) t
  FmapE f e -> fmap (fmap f) (lastOcc e t) where
  JustE e -> lastJust e t
  UnionE e1 e2 -> case lastOcc e1 t of
    Nothing -> case lastOcc e2 t of
      Nothing -> Nothing
      Just (x2, t2) -> Just (x2, t2)
    Just (t1, x1) -> case lastOcc e1 t1 of
      Nothing -> Just (t1, x1)
      Just (t2, x2) -> if t1 <= t2 then Just (t1, x1) else Just (t2, x2)
  DelayE e -> case map delay . filter (\(tOcc,_) -> tOcc <= t) $ allOccs e of
    [] -> Nothing
    occs -> Just . maximumBy (comparing fst) . sortBy (comparing fst) $ occs
  SnapshotE e sig -> case lastOcc e t of
    Nothing -> Nothing
    Just (tOcc, x) -> let g = sigAt' sig tOcc in Just (tOcc, (x, g tOcc))
  InputE _ -> Nothing
  Accum1E prim e -> case lastOcc e t of
    Nothing -> Nothing
    Just (tOcc,b) -> case lastOcc' e tOcc of
      Nothing -> Just (tOcc, (prim, b))
      Just (_, a) -> Just (tOcc, (a,b))
  RasterE -> Just (tOcc, ()) where
    period = 0.02
    tOcc = realToFrac (floor (t / period) :: Integer) * period

lastJust :: E (Maybe a) -> Time -> Maybe (Time, a)
lastJust e t = case lastOcc e t of
  Nothing -> Nothing
  Just (tOcc, Nothing) -> lastJust e tOcc
  Just (tOcc, Just x) -> Just (tOcc, x)

lastJust' :: E (Maybe a) -> Time -> Maybe (Time, a)
lastJust' e t = case lastOcc' e t of
  Nothing -> Nothing
  Just (tOcc, Nothing) -> lastJust' e tOcc
  Just (tOcc, Just x) -> Just (tOcc, x)

lastOcc' :: E a -> Time -> Maybe (Time, a)
lastOcc' arg t = case arg of
  ConstantE [] -> Nothing
  ConstantE (o:os) -> if fst o < t then Just o else lastOcc (ConstantE os) t
  FmapE f e -> fmap (fmap f) (lastOcc e t) where
  JustE e -> lastJust' e t
  UnionE e1 e2 -> case lastOcc' e1 t of
    Nothing -> case lastOcc' e2 t of
      Nothing -> Nothing
      Just (x2, t2) -> Just (x2, t2)
    Just (t1, x1) -> case lastOcc' e1 t1 of
      Nothing -> Just (t1, x1)
      Just (t2, x2) -> if t1 <= t2 then Just (t1, x1) else Just (t2, x2)
  DelayE e -> case map delay . filter (\(tOcc,_) -> tOcc < t) $ allOccs e of
    [] -> Nothing
    occs -> Just . maximumBy (comparing fst) . sortBy (comparing fst) $ occs
  SnapshotE e sig -> case lastOcc e t of
    Nothing -> Nothing
    Just (tOcc, x) -> let g = sigAt' sig tOcc in Just (tOcc, (x, g tOcc))
  InputE _ -> Nothing
  Accum1E prim e -> case lastOcc' e t of
    Nothing -> Nothing
    Just (tOcc, b) -> case lastOcc' e tOcc of
      Nothing -> Just (tOcc, (prim, b))
      Just (_, a) -> Just (tOcc, (a,b))
  RasterE -> Just (tOcc', ()) where
    period = 0.02
    tOcc = realToFrac (floor (t / period) :: Integer) * period
    tOcc' = if tOcc == t then tOcc - period else tOcc

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
  RasterE -> let period = 0.02 in map (\i -> (i*period, ())) [0..]

foldOccs :: a -> [(Time, a)] -> [(Time, (a,a))]
foldOccs _ [] = []
foldOccs prev ((t,x):os) = (t,(prev,x)) : foldOccs x os

sigAt' :: X a -> Time -> (Time -> a)
sigAt' arg t = case arg of
  PureX x -> const x
  TimeX -> id
  FmapX f sig -> f . (sigAt' sig t)
  ApplX ff xx -> (sigAt' ff t) <*> (sigAt' xx t)
  TrapX prim e -> case lastOcc' e t of
    Nothing -> const prim
    Just (_,x) -> const x
  TimeWarpX g _ sig -> case compare (g 0) (g 1) of
    EQ -> const (sampleX sig (g 0))
    LT -> sigAt' sig (g t)
    GT -> sigAtRev' sig (g t) 
  InputX prim _ -> const prim

sigAtRev' :: X a -> Time -> (Time -> a)
sigAtRev' _ _ = undefined

lastTrans :: X a -> Time -> Maybe (Time, (a, a))
lastTrans arg t = case arg of
  PureX _ -> Nothing
  TimeX -> Just (t, (t, t))
  FmapX f sig -> fmap f' (lastTrans sig t) where
    f' (t', (a, b)) = (t', (f a, f b))
  ApplX ff xx -> case lastTrans ff t of
    Nothing -> case lastTrans xx t of
      Nothing -> Nothing
      Just (t2, (a2,b2)) -> let f = sampleX ff 0 in Just (t2, (f a2, f b2))
    Just (t1, (a1,b1)) -> case lastTrans xx t of
      Nothing -> let x = sampleX xx 0 in Just (t1, (a1 x, b1 x))
      Just (t2, (a2,b2)) -> if t1 < t2
        then let f = sampleX ff t1 in Just (t2, (f a2, f b2))
        else let x = sampleX xx t2 in Just (t1, (a1 x, b1 x))
  TrapX prim e -> case lastOcc e t of
    Nothing -> Nothing
    Just (tOcc, b) -> case lastOcc' e tOcc of
      Nothing -> Just (tOcc, (prim, b))
      Just (_, a) -> Just (tOcc, (a, b))
  TimeWarpX g ginv sig -> case compare (g 0) (g 1) of
    EQ -> Nothing
    LT -> fmap (\(tOcc,(a,b)) -> (ginv tOcc, (a,b))) (lastTrans sig (g t)) 
    GT -> fmap (\(tOcc,(a,b)) -> (ginv tOcc, (b,a))) (nextTrans sig (g t)) 
  InputX _ _ -> Nothing

lastTrans' :: X a -> Time -> Maybe (Time, (a, a))
lastTrans' _ _ = Nothing

nextTrans :: X a -> Time -> Maybe (Time, (a, a))
nextTrans arg t = case arg of
  PureX x -> Nothing
  _ -> Nothing

-- cast a discretely changing signal as an event if possible
unX :: X a -> Maybe (E a)
unX arg = case arg of
  PureX _ -> Just mempty
  TimeX -> Nothing
  FmapX f sig -> fmap (FmapE f) (unX sig)
  ApplX _ _ -> Nothing
  TrapX _ e -> Just e
  TimeWarpX _ _ _ -> Nothing
  InputX _ ref -> Just (InputE ref)
  
delay :: (Time, (a, Double)) -> (Time, a)
delay (t, (x, dt)) = (t + dt, x)
