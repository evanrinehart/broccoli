module Combinators where

import Data.Monoid
import Data.Maybe
import Data.Ord
import Data.List

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

occurs :: [(Time, a)] -> E a
occurs = ConstantE . sortBy (comparing fst)

time :: X Time
time = TimeX
