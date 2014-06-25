module Demo where

import Data.Function
import Control.Monad
import Control.Concurrent

import Data.LensRef.Class
import Data.LensRef.Fast
--import Data.LensRef.Pure

main :: IO ()
main = do
    exit <- newEmptyMVar
    runRefCreatorT $ \unlift -> do

        a <- newRef False
        b <- newRef False

        _ <- onChangeEq (liftM2 (,) (readRef a) (readRef b)) $ liftEffectM . print

        liftEffectM $ void $ forkIO $ fix $ \cycle -> do
            l <- getLine
            case l of
                "" -> putMVar exit ()
                "a" -> unlift (modRef a not) >> cycle
                "b" -> unlift (modRef b not) >> cycle
                _ -> putStrLn "wrong input" >> cycle

    void $ takeMVar exit


