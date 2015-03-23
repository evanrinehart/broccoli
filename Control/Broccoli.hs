-- | Small experimental library for interactive functional programs.

{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
module Control.Broccoli (
  X,
  E,
  Time,

  -- * Event and signal combinators
  time,
  never,
  unionE,
  trap,
  justE,
  delayE,
  snapshot,
  snapshot_,
  once,
  mealy,
  accum,
  edge,
  occurs,
  boot,
  pulse,
  eitherE,
  maybeE,
  filterE,
  multiplex,
  whenE,
  dilate,
  timeShift,
  timeWarp,
  timeWarp',
  delayE',
  voidE,

  -- * Evaluation
  -- | These operations assume that no external input ever happens.
  at,
  occs,
  atZero,

  -- * Execution
  simulate,
  testE,
  testX,
  hang,

  -- * Debug
  debugX,
  debugE,
) where

import Control.Broccoli.Eval
import Control.Broccoli.Combinators
import Control.Broccoli.Exec
