module Demo where

import Data.Function
import Control.Monad
import Control.Monad.Trans
import Control.Concurrent

import Data.LensRef

main :: IO ()
main = do
    exit <- newEmptyMVar
    runRefCreatorT $ \unlift -> do

        a <- newRef False
        b <- newRef False

        _ <- onChangeEq (liftM2 (,) (readRef a) (readRef b)) $ lift . print

        lift $ void $ forkIO $ fix $ \cycle -> do
            l <- getLine
            case l of
                "" -> putMVar exit ()
                "a" -> unlift (modRef a not) >> cycle
                "b" -> unlift (modRef b not) >> cycle
                _ -> putStrLn "wrong input" >> cycle

    void $ takeMVar exit


