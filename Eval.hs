{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Eval where

import Control.Applicative
import Data.List
import Data.Ord
import Data.Monoid

import Prog

-- evaluate a program at a particular time assuming no external stimulus

{-
  ConstantE :: [(a, Time)] -> E a
  FmapE :: forall a b . (b -> a) -> E b -> E a
  JustE :: E (Maybe a) -> E a
  UnionE :: E a -> E a -> E a
  DelayE :: E (a, Double) -> E a
  SnapshotE :: forall a b c . a ~ (b,c) => E b -> X c -> E a
  InputE :: Integer -> TVar [Handler a] -> E a
  RasterE :: E a

data X a where
  PureX :: a -> X a
  TimeX :: X a
  FmapX :: forall a b . (b -> a) -> X b -> X a
  ApplX :: forall a b . X (b -> a) -> X b -> X a
  TrapX :: a -> E a -> X a
  TimeWarpX :: (Time -> Time) -> (Time -> Time) -> X a -> X a
  TransX :: forall a b . a ~ (b,b) -> X b -> X a
  InputX :: Integer -> a -> TVar [Handler a] -> X a
-}

sampleX :: X a -> Time -> a
sampleX arg t = case arg of
  PureX x -> x
  TimeX -> t
  FmapX f sig -> f (sampleX sig t)
  ApplX ff xx -> (sampleX ff t) (sampleX xx t)
  TrapX prim e -> case lastOcc e t of
    Nothing -> prim
    Just (x,_) -> x
  TimeWarpX g _ sig -> sampleX sig (g t)
  InputX prim _ -> prim

-- most recent occurrence of an event on or before t, if any
lastOcc :: E a -> Time -> Maybe (a, Time)
lastOcc arg t = case arg of
  ConstantE [] -> Nothing
  ConstantE (o:os) -> if snd o <= t then Just o else lastOcc (ConstantE os) t
  FmapE f e -> fmap f' (lastOcc e t) where
    f' (x, tOcc) = (f x, tOcc)
  JustE e -> lastJust e t
  UnionE e1 e2 -> case lastOcc e1 t of
    Nothing -> case lastOcc e2 t of
      Nothing -> Nothing
      Just (x2, t2) -> Just (x2, t2)
    Just (x1, t1) -> case lastOcc e1 t1 of
      Nothing -> Just (x1, t1)
      Just (x2, t2) -> if t1 <= t2 then Just (x1, t1) else Just (x2, t2)
  DelayE e -> case filter (\(_,tOcc) -> tOcc <= t) (allOccs e) of
    [] -> Nothing
    occs -> answer where
      answer = Just (maximumBy (comparing snd) delayedOccs)
      delayedOccs = sortBy (comparing snd) (map delay occs)
      delay ((x,dt), t') = (x, t' + dt)
  SnapshotE e sig -> case lastOcc e t of
    Nothing -> Nothing
    Just (x,tOcc) -> let g = sigAt' sig tOcc in Just ((x, g tOcc), tOcc)
  InputE _ -> Nothing
  Accum1E prim e -> case lastOcc e t of
    Nothing -> Nothing
    Just (b,tOcc) -> case lastOcc' e tOcc of
      Nothing -> Just ((prim, b), tOcc)
      Just (a, _) -> Just ((a,b), tOcc)
  RasterE -> Just ((), tOcc) where
    period = 0.02
    tOcc = realToFrac (floor (t / period) :: Integer) * period

lastJust' :: E (Maybe a) -> Time -> Maybe (a, Time)
lastJust' e t = case lastOcc' e t of
  Nothing -> Nothing
  Just (Nothing, tOcc) -> lastJust' e tOcc
  Just (Just x, tOcc) -> Just (x, tOcc)

lastJust :: E (Maybe a) -> Time -> Maybe (a, Time)
lastJust e t = case lastOcc e t of
  Nothing -> Nothing
  Just (Nothing, tOcc) -> lastJust' e tOcc
  Just (Just x, tOcc) -> Just (x, tOcc)

lastOcc' :: E a -> Time -> Maybe (a, Time)
lastOcc' arg t = case arg of
  ConstantE [] -> Nothing
  ConstantE (o:os) -> if snd o < t then Just o else lastOcc (ConstantE os) t
  FmapE f e -> fmap f' (lastOcc e t) where
    f' (x, tOcc) = (f x, tOcc)
  JustE e -> lastJust' e t
  UnionE e1 e2 -> case lastOcc' e1 t of
    Nothing -> case lastOcc' e2 t of
      Nothing -> Nothing
      Just (x2, t2) -> Just (x2, t2)
    Just (x1, t1) -> case lastOcc' e1 t1 of
      Nothing -> Just (x1, t1)
      Just (x2, t2) -> if t1 <= t2 then Just (x1, t1) else Just (x2, t2)
  DelayE e -> case filter (\(_,tOcc) -> tOcc < t) (allOccs e) of
    [] -> Nothing
    occs -> answer where
      answer = Just (maximumBy (comparing snd) delayedOccs)
      delayedOccs = sortBy (comparing snd) (map delay occs)
      delay ((x,dt), t') = (x, t' + dt)
  SnapshotE e sig -> case lastOcc e t of
    Nothing -> Nothing
    Just (x,tOcc) -> let g = sigAt' sig tOcc in Just ((x, g tOcc), tOcc)
  InputE _ -> Nothing
  Accum1E prim e -> case lastOcc' e t of
    Nothing -> Nothing
    Just (b,tOcc) -> case lastOcc' e tOcc of
      Nothing -> Just ((prim, b), tOcc)
      Just (a, _) -> Just ((a,b), tOcc)
  RasterE -> Just ((), tOcc') where
    period = 0.02
    tOcc = realToFrac (floor (t / period) :: Integer) * period
    tOcc' = if tOcc == t then tOcc - period else tOcc

allOccs :: E a -> [(a, Time)]
allOccs _ = []

sigAt' :: X a -> Time -> (Time -> a)
sigAt' arg t = case arg of
  PureX x -> const x
  TimeX -> id
  FmapX f sig -> f . (sigAt' sig t)
  ApplX ff xx -> (sigAt' ff t) <*> (sigAt' xx t)
  TrapX prim e -> case lastOcc' e t of
    Nothing -> const prim
    Just (x,_) -> const x
  TimeWarpX g _ sig -> case compare (g 0) (g 1) of
    EQ -> const (sampleX sig (g 0))
    LT -> sigAt' sig (g t)
    GT -> sigAtRev' sig (g t) 
  InputX prim _ -> const prim

sigAtRev' :: X a -> Time -> (Time -> a)
sigAtRev' _ _ = undefined

lastTrans :: X a -> Time -> Maybe ((a, a), Time)
lastTrans arg t = case arg of
  PureX _ -> Nothing
  TimeX -> Just ((t, t), t)
  FmapX f sig -> fmap f' (lastTrans sig t) where
    f' ((a, b), t') = ((f a, f b), t')
  ApplX ff xx -> case lastTrans ff t of
    Nothing -> case lastTrans xx t of
      Nothing -> Nothing
      Just ((a2,b2), t2) -> let f = sampleX ff 0 in Just ((f a2, f b2), t2)
    Just ((a1,b1), t1) -> case lastTrans xx t of
      Nothing -> let x = sampleX xx 0 in Just ((a1 x, b1 x), t1)
      Just ((a2,b2), t2) -> if t1 < t2
        then let f = sampleX ff t1 in Just ((f a2, f b2), t2)
        else let x = sampleX xx t2 in Just ((a1 x, b1 x), t1)
  TrapX prim e -> case lastOcc e t of
    Nothing -> Nothing
    Just (b, tOcc) -> case lastOcc' e tOcc of
      Nothing -> Just ((prim, b), tOcc)
      Just (a, _) -> Just ((a, b), tOcc)
  TimeWarpX g ginv sig -> case compare (g 0) (g 1) of
    EQ -> Nothing
    LT -> fmap (\((a,b),tOcc) -> ((a,b), ginv tOcc)) (lastTrans sig (g t)) 
    GT -> fmap (\((a,b),tOcc) -> ((b,a), ginv tOcc)) (nextTrans sig (g t)) 
  InputX _ _ -> Nothing

lastTrans' :: X a -> Time -> Maybe ((a, a), Time)
lastTrans' _ _ = Nothing

nextTrans :: X a -> Time -> Maybe ((a, a), Time)
nextTrans arg t = case arg of
  PureX x -> Nothing
  _ -> Nothing

unX :: X a -> Maybe (E a)
unX arg = case arg of
  PureX _ -> Just mempty
  TimeX -> Nothing
  FmapX f sig -> fmap (FmapE f) (unX sig)
  ApplX _ _ -> Nothing
  TrapX _ e -> Just e
  TimeWarpX _ _ _ -> Nothing
  InputX _ ref -> Just (InputE ref)
  
