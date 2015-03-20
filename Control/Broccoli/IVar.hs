module Control.Broccoli.IVar where

import Control.Concurrent.STM

-- write once variable -- reading before writing blocks until written
data IVar a = IVar (TVar (Maybe a))

newIVar :: IO (IVar a)
newIVar = do
  tv <- newTVarIO Nothing
  return (IVar tv)

readIVarIO :: IVar a -> IO a
readIVarIO iv = atomically (readIVar iv)

readIVar :: IVar a -> STM a
readIVar (IVar tv) = do
  mx <- readTVar tv
  case mx of
    Nothing -> retry
    Just x -> return x

writeIVar :: IVar a -> a -> STM ()
writeIVar (IVar tv) x = do
  mx <- readTVar tv
  case mx of
    Nothing -> writeTVar tv (Just x)
    Just _ -> error "tried to write an IVar twice"

writeIVarIO :: IVar a -> a -> IO ()
writeIVarIO iv x = atomically (writeIVar iv x)

dupIVar :: IVar a -> STM (IVar a)
dupIVar (IVar tv) = do
  prev <- readTVar tv
  tv' <- newTVar prev
  return (IVar tv')

isBlankIVar :: IVar a -> STM Bool
isBlankIVar (IVar tv) = do
  mx <- readTVar tv
  case mx of
    Nothing -> return True
    Just _ -> return False

