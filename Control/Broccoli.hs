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
  mealy,
  occurs,
  boot,
  pulse,
  edge,
  accum,
  pairE,
  once,
  eitherE,
  maybeE,
  filterE,
  multiplex,
  whenE,
  voidE,
  dilate,
  timeShift,
  timeWarp,
  delayE',
  snapshot_,
  snapshot',
  timeWarp',

  -- * Evaluation
  -- | These operations assume that no external input ever happens.
  at,
  occs,
  atZero,

  -- * Execution
  simulate,
  testX,
  testE,
  hang,

  -- * Debug
  debugX,
  debugE,
  showTime
) where

import Control.Broccoli.Eval
import Control.Broccoli.Combinators
import Control.Broccoli.Exec
