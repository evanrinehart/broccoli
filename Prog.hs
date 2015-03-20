{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Prog where

import Control.Applicative
import Data.Monoid
import Data.IORef

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

data X a where
  PureX :: a -> X a
  TimeX :: a ~ Time => X a
  FmapX :: forall a b . (b -> a) -> X b -> X a
  ApplX :: forall a b . X (b -> a) -> X b -> X a
  TrapX :: a -> E a -> X a
  TimeWarpX :: (Time -> Time) -> (Time -> Time) -> X a -> X a

type Time = Double
type Handler a = a -> Time -> IO ()

instance Functor E where
  fmap f e = FmapE f e

instance Functor X where
  fmap f sig = FmapX f sig

instance Applicative X where
  pure x = PureX x
  ff <*> xx = ApplX ff xx

instance Monoid (E a) where
  mempty = ConstantE []
  mappend = UnionE
  
