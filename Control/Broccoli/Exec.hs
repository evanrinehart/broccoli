{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Control.Broccoli.Exec (
  Setup,
  testE,
  testX
) where

import Control.Applicative
import Control.Concurrent
import Data.IORef
import Control.Monad
import Data.Time
import System.Mem.StableName
import Data.Map (Map)
import qualified Data.Map as M

import GHC.Prim (Any)
import Unsafe.Coerce

import Control.Broccoli.Types
import Control.Broccoli.Eval
import Control.Broccoli.IVar
import Control.Broccoli.Dispatch
import Control.Broccoli.Combinators

-- Take a program and execute it in real time with real inputs.

-- The justification for why this ought to work goes here.

-- | A monad to connect inputs and outputs to a program for simulation.
newtype Setup a = Setup (Context -> IO a)

instance Monad Setup where
  return x = Setup (\_ -> return x)
  (Setup r) >>= f = Setup r' where
    r' mv = do
      x <- r mv
      let Setup r'' = f x
      r'' mv

instance Applicative Setup where
  pure = return
  (<*>) = ap

instance Functor Setup where
  fmap f (Setup io) = Setup (\mv -> f <$> io mv)

data Context = Context
  { cxDeferIO :: Time -> IO () -> IO ()
  , cxDeferredHookups :: IORef [IO ()]
  , cxRastActions :: IORef [Time -> IO ()]
  , cxVisitedVars :: IORef (Map Int Any) -- Any = IORef (Time -> a)
  , cxThreads :: IORef [ThreadId]
  , cxLock :: MVar ()
  , cxEpochIv :: IVar UTCTime }

newContext :: IO Context
newContext = do
  epochIv <- newIVar
  (deferIO, tid) <- newScheduler epochIv
  visitedRef <- newIORef (M.empty)
  threadsRef <- newIORef [tid]
  lockMv <- newMVar ()
  hookupsRef <- newIORef []
  rastActions <- newIORef []
  return (Context deferIO hookupsRef rastActions visitedRef threadsRef lockMv epochIv)

-- | Run through an event in real time, executing the IO action on each
-- occurrence. The computation never terminates.
testE :: (Time -> a -> IO ()) -> E a -> IO ()
testE action e = do
  cx <- newContext
  magicE cx e (flip action)
  let ref = cxDeferredHookups cx
  whileM (not <$> listIsEmpty ref) $ do
    ios <- readIORef ref
    writeIORef ref []
    sequence ios
  epoch <- getCurrentTime
  writeIVarIO (cxEpochIv cx) epoch
  hang -- finally cleanup

-- | Apply an IO action to arbitrary values of a signal in real time. The
-- computation never terminates.
testX :: (Time -> a -> IO ()) -> X a -> IO ()
testX action x = testE action (raster x)

-- execute effects to setup runtime handler
magicE :: Context -> E a -> (a -> Time -> IO ()) -> IO ()
magicE cx e0 k = case e0 of
  ConstantE [] -> return ()
  ConstantE occs' -> mapM_ (\(t,x) -> cxDeferIO cx t (k x t)) occs'
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
  InputE ref -> addToList ref k
  RasterE -> addToList (cxRastActions cx) (k ())

magicDelayE :: Context -> E (a, Double) -> (a -> Time -> IO ()) -> IO ()
magicDelayE cx e k = magicE cx e $ \(x,dt) t -> do
  let t' = t + dt
  cxDeferIO cx t' (k x t')

magicX :: Context -> X a -> ((Time -> a) -> Time -> IO ()) -> IO ()
magicX cx arg k = case arg of
  PureX _ -> return ()
  TimeX -> return ()
  FmapX f sig -> magicX cx sig (\g t -> k (f . g) t)
  ApplX sig1 sig2 -> error "appl"
  TrapX _ e -> magicE cx e (\x t -> k (const x) t)
  MultiX xs -> error "multix magicX"
  TimeWarpX tmap tmapInv sig -> magicX cx sig $ \g t -> do
    cxDeferIO cx (tmapInv t) (k g (tmap t))

-- here we generate a Var which will be updated during the simulation.
-- we only need to generate one per snapshot, if the program were implemented
-- as a graph behind the scenes. but it will still work just less efficiently
-- if the variable were copied for every handler that uses the snapshot.
-- every variable would generate a trigger on every input that the snapshot sees.
--
-- actually if we dont cull the number of variables here, then every client of
-- the component will replicate all the internal variables and related triggers
-- to update it, seems like a waste in a large program.
--
-- how do we do it? 
newMagicVar :: forall a . Context -> X a -> IO (IORef (Time -> a))
newMagicVar cx sig = do
  uid <- getNodeName sig
  saw <- readIORef (cxVisitedVars cx)
  case M.lookup uid saw of
    Nothing -> do
      putStrLn ("magic var " ++ show uid)
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

hang :: IO a
hang = do
  threadDelay (100 * 10^(6::Int))
  hang

getNodeName :: X a -> IO Int
getNodeName sig = do
  sn <- sig `seq` makeStableName sig
  return (hashStableName sn)

