{-# LANGUAGE CPP #-}

#ifndef __TESTS__
main :: IO ()
main = fail "enable the tests flag"
#else
import Data.IORef
import Control.Monad
import Criterion.Main
import Criterion.Config

import Data.LensRef.Test

------------------

myConfig = defaultConfig
              -- Always GC between runs.
            { cfgPerformGC = ljust True
            , cfgReport    = ljust "lensref-performance-report.html"
            }

main = defaultMainWith myConfig (return ())
     $  [ bench ("ioref " ++ show i) $ ioRefTest i | i <- map (* 10) range]
     ++
        [ bench (imp ++ " " ++ name ++ " " ++ show i) $ f name i
        | (imp, f, corr) <- [("fast", runPerformanceTests, 1), ("pure", runPerformanceTestsPure, 10)]
        , (name, corr2) <- [("create", 1), ("mapchain", 1), ("joinchain", 2)]
        , n <- range
        , let i = n `div` (corr * corr2)
        ]
  where
    range = [2000,4000,6000]

-- for comparison
ioRefTest n = do
    rs <- replicateM n $ newIORef 'x'
    forM_ rs $ \r -> r ==> 'x'
    forM_ rs $ \r -> writeIORef r 'y'
    forM_ rs $ \r -> r ==> 'y'
  where
    r ==> v = readIORef r >>= (==? v)

    a ==? b | a == b = return ()
    a ==? b = fail $ show a ++ " /= " ++ show b
#endif
