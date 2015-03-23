{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Control.Broccoli.Exec where

import Control.Applicative
import Control.Concurrent
import Data.IORef
import Control.Monad
import Data.Time
import System.Mem.StableName
--import Data.Map (Map)
--import qualified Data.Map as M
import Control.Exception
import Numeric
import System.IO

import GHC.Prim (Any)
import Unsafe.Coerce

import Control.Broccoli.Eval
import Control.Broccoli.Dispatch
import Control.Broccoli.Combinators

-- Take a program and execute it in real time with real inputs.

-- The justification for why this ought to work goes here.

data Context = Context
  { cxDeferIO :: [(Time, IO ())] -> IO ()
  , cxDeferredHookups :: IORef [IO ()]
  , cxDebuggers :: IORef [NodeName]
  , cxVisitedVars :: IORef [(NodeName, Any)]  -- Any = IORef (Time -> a)
  }

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
  SnapshotE bias cons x e -> do
    ref <- newMagicVar cx bias x
    magicE cx e $ \v t -> do
      g <- readIORef ref
      k (cons (g t) v) t
  InputE hookup -> hookup k
  DebugE toString e -> do
    let ref = cxDebuggers cx
    name <- getNodeNameE e0
    saw <- readIORef ref
    when (not (name `elem` saw)) $ do
      addToList ref name
      magicE cx e $ \v t -> do
        hPutStrLn stderr (unwords [showFFloat (Just 5) t "", toString v])
        k v t

magicDelayE :: Context -> E (a, Double) -> (a -> Time -> IO ()) -> IO ()
magicDelayE cx e k = magicE cx e $ \(x,dt) t -> do
  let t' = t + dt
  cxDeferIO cx [(t', k x t')]

magicX :: Context -> X a -> ((Time -> a, Time -> a) -> Time -> IO ()) -> IO ()
magicX cx arg k = case arg of
  PureX _ -> return ()
  TimeX -> return ()
  FmapX f x -> magicX cx x (\(g1,g2) t -> k (f . g1, f . g2) t)
  ApplX ff xx -> do
    let f0 = primPhase ff
    let x0 = primPhase xx
    ffref <- newIORef (f0,f0)
    xxref <- newIORef (x0,x0)
    magicX cx ff $ \(g1, g2) t -> do
      writeIORef ffref (g1, g2)
      (h1, h2) <- readIORef xxref
      k (g1 <*> h1, g2 <*> h2) t
    magicX cx xx $ \(g1, g2) t -> do
      writeIORef xxref (g1, g2)
      (h1, h2) <- readIORef ffref
      k (h1 <*> g1, h2 <*> g2) t
  TrapX prim e -> do
    phaseRef <- newIORef (const prim)
    magicE cx e $ \x t -> do
      g1 <- readIORef phaseRef
      let g2 = const x
      writeIORef phaseRef g2
      k (g1, g2) t
  TimeWarpX tmap tmapInv sig -> magicX cx sig $ \(g1, g2) t -> do
    let t' = tmapInv t
    print t'
    case compare t' t of
      LT -> hPutStrLn stderr "Warning: an acausal influence was ignored."
      EQ -> k (g1 . tmap, g2 . tmap) t
      GT -> case warp tmap of
        Forward  -> cxDeferIO cx [(t', k (g1 . tmap, g2 . tmap) t')]
        Backward -> cxDeferIO cx [(t', k (g2 . tmap, g1 . tmap) t')]

newMagicVar :: forall a . Context -> Bias -> X a -> IO (IORef (Time -> a))
newMagicVar cx bias x = do
  uid <- getNodeNameX x
  saw <- readIORef (cxVisitedVars cx)
  case lookup uid saw of
    Nothing -> do
      let phase = primPhase x
      ref <- newIORef phase
      --modifyIORef (cxVisitedVars cx) (M.insert uid (unsafeCoerce ref :: Any))
      modifyIORef (cxVisitedVars cx) ((uid, unsafeCoerce ref :: Any):)
      let hookup = magicX cx x (\(_,g) _ -> writeIORef ref g)
      case bias of
        NowMinus -> addToList (cxDeferredHookups cx) hookup
        Now -> hookup
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

-- | Run a program in real time with a source of external input and an
-- output handler. The computation never terminates.
simulate :: (E a -> E b) -> IO a -> (Time -> b -> IO ()) -> IO ()
simulate prog getIn doOut = do
  epochMv <- newEmptyMVar
  (deferIO, dispThread) <- newScheduler epochMv
  ref1 <- newIORef []
  ref2 <- newIORef []
  ref3 <- newIORef []
  let cx = Context deferIO ref1 ref2 ref3
  inputHandlersRef <- newIORef []
  let inE = InputE (addToList inputHandlersRef)
  magicE cx (prog inE) (flip doOut)
  repeatedlyExecuteDeferredHookups cx
  hds <- readIORef inputHandlersRef
  epoch <- getCurrentTime
  putMVar epochMv epoch
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


-- | Simulate an event and print out the occurrences as they happen.
testE :: (a -> String) -> E a -> IO ()
testE toString e = simulate (const e) hang f where
  f t v = putStrLn (showFFloat (Just 5) t " " ++ toString v)

-- | Simulate a signal and print out values at the specified sample rate.
testX :: Int -> (a -> String) -> X a -> IO ()
testX 0 _ _ = error "testX: sample rate zero"
testX sr toString x = testE toString (snapshot' const x (pulse (srToPeriod sr)))

-- | Does nothing and never completes with any result. Useful as a dummy
-- input.
hang :: IO a
hang = do
  threadDelay (100 * 10^(6::Int))
  hang



getNodeNameX :: X a -> IO NodeName
getNodeNameX x = do
  sn <- x `seq` makeStableName x
  return (fromStableName sn)

getNodeNameE :: E a -> IO NodeName
getNodeNameE e = do
  sn <- e `seq` makeStableName e
  return (fromStableName sn)

data NodeName = NodeName (StableName Any) deriving (Eq)

instance Show NodeName where
  show (NodeName sn) = show (hashStableName sn)

fromStableName :: StableName a -> NodeName
fromStableName sn = NodeName (unsafeCoerce sn)
