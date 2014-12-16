import Data.IORef
import Control.Applicative
import Control.Monad
import Criterion.Main
import Criterion.Types

import LensRef

--------------------------------------------------------------------------------

myConfig :: Config
myConfig = defaultConfig
            { reportFile    = Just "lensref-performance-report.html"
            }

main :: IO ()
main = defaultMainWith myConfig
     $  bgroup "ioref create" [ bench (show i) $ nfIO $ ioRefTest i | i <- range]
     :  [ bgroup (imp ++ " " ++ name)
            [ bench (show i) $ nfIO $ f name i
            | n <- range
            , let i = round $ fromIntegral n * corr * corr2
            ]
        | (imp, f, corr) <- [("lensref", runPerformanceTests, 1)]
        , (name, corr2) <- [("create", 0.1), ("mapchain", 0.5), ("joinchain", 0.02)]
        ]
  where
    range = [20000,40000,60000]

--------------------------------------------------------------------------------

-- for comparison
ioRefTest :: Int -> IO ()
ioRefTest n = do
    rs <- replicateM n $ newIORef 'x'
    forM_ rs $ \r -> r ==> 'x'
    forM_ rs $ \r -> writeIORef r 'y'
    forM_ rs $ \r -> r ==> 'y'
  where
    r ==> v = readIORef r >>= (==? v)

    a ==? b | a == b = return ()
    a ==? b = fail $ show a ++ " /= " ++ show b

--------------------------------------------------------------------------------

runPerformanceTests :: String -> Int -> IO ()
runPerformanceTests name n = do

    let a ==? b = when (a /= b) $ fail $ show a ++ " /= " ++ show b

        r ==> v = readerToWriter $ readRef r >>= (==? v)

    join $ runRefCreator $ \runRefWriter -> fmap runRefWriter $ case name of
        "create" -> do
            rs <- replicateM n $ newRef 'x'
            return $ do
                forM_ rs $ \r -> r ==> 'x'
                forM_ rs $ \r -> writeRef r 'y'
                forM_ rs $ \r -> r ==> 'y'

        "mapchain" -> do
            r <- newRef 'x'
            let q = iterate (lensMap id) r !! n
            return $ do
                q ==> 'x'
                writeRef q 'y'
                q ==> 'y'

        "joinchain" -> do
            rb <- newRef True
            r1 <- newRef 'x'
            r2 <- newRef 'y'
            let f (r1, r2) =
                    ( joinRef $ bool r1 r2 <$> readRef rb
                    , joinRef $ bool r2 r1 <$> readRef rb
                    )
                (r1', r2') = iterate f (r1, r2) !! (2*n)
            return $ do
                r1' ==> 'x'
                r2' ==> 'y'
                writeRef r1' 'X'
                r1' ==> 'X'
                r2' ==> 'y'
                writeRef r2' 'Y'
                r1' ==> 'X'
                r2' ==> 'Y'
                writeRef rb False
                r1' ==> 'X'
                r2' ==> 'Y'
                writeRef r1' 'x'
                r1' ==> 'x'
                r2' ==> 'Y'
                writeRef r2' 'y'
                r1' ==> 'x'
                r2' ==> 'y'

        _ -> error $ "No such test: " ++ name


bool :: a -> a -> Bool -> a
bool a _ True  = a
bool _ b False = b

