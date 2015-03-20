module Combinators where

import Data.Monoid
import Data.Maybe
import Data.Ord
import Data.List
import Control.Applicative

import Prog
import Eval

never :: E a
never = mempty

unionE :: E a -> E a -> E a
unionE = mappend

trap :: a -> E a -> X a
trap = TrapX

justE :: E (Maybe a) -> E a
justE = JustE

snapshot :: E a -> X b -> E (a,b)
snapshot e sig = SnapshotE e sig

snapshot_ :: E a -> X b -> E b
snapshot_ e sig = fmap snd (snapshot e sig)

timeWarp :: (Time -> Time) -> (Time -> Time) -> X a -> X a
timeWarp = TimeWarpX

edge :: (a -> a -> Maybe b) -> X a -> E b
edge diff sig = (justE . fmap (uncurry diff) . Accum1E v0) e where
  v0 = sampleX sig 0
  e = fromMaybe (snapshot_ RasterE sig) (unX sig)

accum :: s -> (a -> s -> s) -> E a -> X s
accum s0 trans e = out where
  out = trap s0 e'
  e' = fmap f (snapshot e out)
  f s x = trans x s

occurs :: [(Time, a)] -> E a
occurs = ConstantE . sortBy (comparing fst)

time :: X Time
time = TimeX

onBoot :: E ()
onBoot = occurs [(0, ())]

deriv :: Fractional a => X a -> X a
deriv sig = f <$> sig <*> timeWarp (subtract dt) (+dt) sig where
  dt = 0.001
  f y1 y0 = (y1 - y0) / dt

