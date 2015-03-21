-- | Small experimental library for interactive functional programs.

{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
module Control.Broccoli (
  X,
  E,

  -- * Event and signal combinators
  time,
  once,
  never,
  unionE,
  trap,
  justE,
  delayE,
  snapshot,
  snapshot_,
  mealy,
  accum,
  edge,
  occurs,
  eitherE,
  maybeE,
  filterE,
  multiplex,
  dilate,
  timeShift,
  timeWarp,
  timeWarp',
  derivative,
  delayE',
  voidE,
  raster,
  rasterize,
  atZero,

  -- * Pure interface
  -- | These computations assume that no external input ever occurs.
  at,
  occs,

  -- * Running a simulation
  Setup,
  testE,
  testX,

  -- * Debug
  debugX,
  debugE,
) where

import Control.Broccoli.Types
import Control.Broccoli.Combinators
import Control.Broccoli.Eval
import Control.Broccoli.Exec
