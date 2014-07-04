{-# LANGUAGE CPP #-}

#ifndef __TESTS__
main :: IO ()
main = fail "enable the tests flag"
#else
import Numeric
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
     $  [ bench ("ioref create" ++ show i) $ ioRefTest i | i <- range]
     ++
        [ bench (imp ++ " " ++ name ++ " " ++ show i) $ f name i
        | (imp, f, corr) <- [("lensref", runPerformanceTests, 1)]
        , (name, corr2) <- [("create", 0.1), ("mapchain", 0.5), ("joinchain", 0.02)]
        , n <- range
        , let i = round $ fromIntegral n * corr * corr2
        ]
  where
    range = [20000,40000,60000]

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

