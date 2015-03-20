{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Control.Broccoli.Types where

import Data.IORef

-- | @E a@ represents events with values of type @a@.
-- 
-- > E a = [(Time, a)]
data E a where
  ConstantE :: [(Time, a)] -> E a
  FmapE :: forall a b . (b -> a) -> E b -> E a
  JustE :: E (Maybe a) -> E a
  UnionE :: E a -> E a -> E a
  DelayE :: E (a, Double) -> E a
  SnapshotE :: forall a b c . a ~ (b,c) => E b -> X c -> E a
  InputE :: IORef [Handler a] -> E a
  Accum1E :: forall a b . a ~ (b,b) => b -> E b -> E a
  RasterE :: a ~ () => E a

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

type Time = Double
type Handler a = a -> Time -> IO ()

