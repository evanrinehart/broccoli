{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Control.Broccoli.Exec where

import Control.Applicative
import Control.Concurrent
import Data.IORef
import Control.Monad
import Data.Time
import System.Mem.StableName
import Data.Map (Map)
import qualified Data.Map as M
import Control.Exception

import GHC.Prim (Any)
import Unsafe.Coerce

import Control.Broccoli.Eval
import Control.Broccoli.IVar
import Control.Broccoli.Dispatch
import Control.Broccoli.Combinators

-- Take a program and execute it in real time with real inputs.

-- The justification for why this ought to work goes here.

data Context = Context
  { cxDeferIO :: [(Time, IO ())] -> IO ()
  , cxDeferredHookups :: IORef [IO ()]
  , cxVisitedVars :: IORef (Map Int Any)  -- Any = IORef (Time -> a)
  }

-- | Does nothing and never completes with any result.
hang :: IO a
hang = do
  threadDelay (100 * 10^(6::Int))
  hang

-- execute effects to setup runtime handler
magicE :: Context -> E a -> (a -> Time -> IO ()) -> IO ()
magicE cx e0 k = case e0 of
  ConstantE os -> cxDeferIO cx (map (\(t,x) -> (t, k x t)) os)
  FmapE f e -> magicE cx e (\x t -> k (f x) t)
  JustE e -> magicE cx e $ \x t -> case x of
    Nothing -> return ()
    Just y -> k y t
  UnionE e1 e2 -> do
    magicE cx e1 k
    magicE cx e2 k
  DelayE e -> addToList (cxDeferredHookups cx) (magicDelayE cx e k)
  SnapshotE cons sig e -> do
    ref <- newMagicVar cx sig
    magicE cx e $ \x t -> do
      g <- readIORef ref
      k (cons (g t) x) t
  InputE hookup -> hookup k

magicDelayE :: Context -> E (a, Double) -> (a -> Time -> IO ()) -> IO ()
magicDelayE cx e k = magicE cx e $ \(x,dt) t -> do
  let t' = t + dt
  cxDeferIO cx [(t', k x t')]

magicX :: Context -> X a -> ((Time -> a) -> Time -> IO ()) -> IO ()
magicX cx arg k = case arg of
  PureX _ -> return ()
  TimeX -> return ()
  FmapX f sig -> magicX cx sig (\g t -> k (f . g) t)
  ApplX sig1 sig2 -> error "magicX ApplX"
  TrapX _ e -> magicE cx e (\x t -> k (const x) t)
  TimeWarpX tmap tmapInv sig -> magicX cx sig $ \g t -> do
    cxDeferIO cx [(tmapInv t, k g (tmap t))]

newMagicVar :: forall a . Context -> X a -> IO (IORef (Time -> a))
newMagicVar cx sig = do
  uid <- getNodeName sig
  saw <- readIORef (cxVisitedVars cx)
  case M.lookup uid saw of
    Nothing -> do
      let ph0Minus = findPhase sig 0 phaseMinus
      ref <- newIORef (ph0Minus)
      modifyIORef (cxVisitedVars cx) (M.insert uid (unsafeCoerce ref :: Any))
      addToList (cxDeferredHookups cx) (magicX cx sig (\g _ -> writeIORef ref g))
      return ref
    Just var -> return (unsafeCoerce var :: IORef (Time -> a))

addToList :: IORef [a] -> a -> IO ()
addToList ref x = modifyIORef ref (++[x])

listIsEmpty :: IORef [a] -> IO Bool
listIsEmpty ref = null <$> readIORef ref

whileM :: IO Bool -> IO a -> IO ()
whileM check action = do
  b <- check
  if b then action >> whileM check action else return ()

getNodeName :: X a -> IO Int
getNodeName sig = do
  sn <- sig `seq` makeStableName sig
  return (hashStableName sn)
  

-- | Run a program in real time with a source of external input and an
-- output handler. The computation never terminates.
simulate :: IO a -> (Time -> b -> IO ()) -> (E a -> E b) -> IO ()
simulate getIn doOut prog = do
  epochIv <- newIVar
  (deferIO, dispThread) <- newScheduler epochIv
  ref1 <- newIORef []
  ref2 <- newIORef M.empty
  let cx = Context deferIO ref1 ref2
  inputHandlersRef <- newIORef []
  let inE = InputE (addToList inputHandlersRef)
  magicE cx (prog inE) (flip doOut)
  repeatedlyExecuteDeferredHookups cx
  hds <- readIORef inputHandlersRef
  epoch <- getCurrentTime
  writeIVarIO epochIv epoch
  flip finally (killThread dispThread) $ forever $ do
    v <- getIn
    t <- getSimulationTime epoch
    mapM_ (\hd -> hd v t) hds


repeatedlyExecuteDeferredHookups :: Context -> IO ()
repeatedlyExecuteDeferredHookups cx = do
  let ref = cxDeferredHookups cx
  whileM (not <$> listIsEmpty ref) $ do
    ios <- readIORef ref
    writeIORef ref []
    sequence ios

-- bootup checklist (one output)
-- 1. create a blank context
-- 2. magicE with output action (populates deferred hookups)
-- 3. repeatedly execute deferred hookups
-- 4. spawn raster thread
-- 5. spawn input threads
-- 6. install the epoch which will cause the machine to go
-- 7. go to sleep


-- | Print out occurrences of events as they happen. Only for debugging.
debugE :: (a -> String) -> E a -> E a
debugE toString e = undefined

-- | Print out values of a signal at arbitrary times. Only for debugging.
debugX :: (a -> String) -> X a -> X a
debugX toString sig = undefined

-- | Simulate an event and print out the occurrences as they happen.
testE :: (a -> String) -> E a -> IO ()
testE toString e = simulate hang f (const e) where
  f t v = putStrLn (show t ++ " " ++ toString v)

-- | Simulate a signal and print out samples at arbitrary times.
testX :: (a -> String) -> X a -> IO ()
testX toString x = testE toString (snapshot_ x (pulse 0.05))
