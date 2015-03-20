module Dispatch where

import Control.Monad
import Control.Concurrent
import Control.Concurrent.STM
import Data.Map (Map)
import qualified Data.Map as M
import Data.Time
import Data.Maybe

import Prog
import IVar


-- so there is one static dispatcher. its like got a [(Time, IO ())]
-- when you encounter a ConstantE you schedule all the events with all the
-- others your events go after any scheduled at the current time.
-- the type of the value being dispatched is hidden by partial application.
-- so the static dispatcher object is Time -> [IO ()]
--
-- since we are also going to want to schedule similar actions for the future
-- during the simulation, might as well merge this thing with the dynamic
-- dispatcher.

newScheduler :: IVar UTCTime -> IO (Time -> IO () -> IO (), ThreadId)
newScheduler epochIv = do
  tv <- newTVarIO M.empty
  wake <- newTChanIO
  tid <- forkIO (dispatcher epochIv tv wake)
  return (schedule tv wake, tid)

schedule :: TVar (Map Time [IO ()]) -> TChan () -> Time -> IO () -> IO ()
schedule tv wake target action = atomically $ do
  q <- readTVar tv
  let q' = M.alter (insertAction action) target q
  writeTVar tv q'
  writeTChan wake ()

-- we want new events at the same time to go last
insertAction :: a -> Maybe [a] -> Maybe [a]
insertAction x Nothing = Just [x]
insertAction x (Just xs) = Just (xs ++ [x])

dispatcher :: IVar UTCTime -> TVar (Map Time [IO ()]) -> TChan () -> IO ()
dispatcher epochIv tv wake = do
  epoch <- readIVarIO epochIv
  forever $ do
    now <- getSimulationTime epoch
    (nextWake, ios) <- atomically $ do
      q <- readTVar tv
      let (lt, eq, gt) = M.splitLookup now q
      let currents = fromMaybe [] eq
      return
        ( fmap (fst . fst) (M.minViewWithKey gt)
        , concatMap snd (M.assocs lt) ++ currents )
    sequence ios
    case nextWake of
      Nothing -> atomically (readTChan wake)
      Just tNext -> do
        let ms = ceiling (min (tNext - now) 10 * million)
        cancel <- cancellableThread $ do
          threadDelay ms
          atomically (writeTChan wake ())
        atomically (readTChan wake)
        cancel

million :: Double
million = toEnum (10^(6::Int))

cancellableThread :: IO () -> IO (IO ())
cancellableThread io = do
  mv <- newEmptyMVar
  tid <- forkIO $ do
    io
    _ <- tryTakeMVar mv
    return ()
  putMVar mv tid
  return $ do
    mtarget <- tryTakeMVar mv
    case mtarget of
      Nothing -> return ()
      Just target -> killThread target


getSimulationTime :: UTCTime -> IO Double
getSimulationTime epoch = do
  now <- getCurrentTime
  let time = diffUTCTime now epoch
  return (realToFrac time)
