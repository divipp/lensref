module LensRef.Demo where

import Data.Function
import Control.Monad
import Control.Monad.Trans
import Control.Concurrent

import LensRef

main :: IO ()
main = do
    exit <- newEmptyMVar
    runRefCreator $ \runRefWriter -> do

        a <- newRef False
        b <- newRef False

        _ <- onChangeEq (liftM2 (,) (readRef a) (readRef b)) $ lift . print

        lift $ void $ forkIO $ fix $ \cycle -> do
            l <- getLine
            case l of
                "" -> putMVar exit ()
                "a" -> runRefWriter (modRef a not) >> cycle
                "b" -> runRefWriter (modRef b not) >> cycle
                _ -> putStrLn "wrong input" >> cycle

    void $ takeMVar exit

