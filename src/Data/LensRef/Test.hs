{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
-- | Tests for the lens references interface.
module Data.LensRef.Test
    ( -- * Tests for the interface
      runTests
    ) where

import Data.Maybe
import Control.Applicative
import Control.Monad
import Control.Monad.ST
import Control.Monad.Writer hiding (Any)
import Control.Arrow ((***))
import Lens.Family2
import Lens.Family2.Stock
import Lens.Family2.Unchecked

import Data.LensRef.SimpleRef
import Data.LensRef

------------------------------------

type Prog s = WriterT [Maybe (Either String String)] (ST s)

--message :: String -> RefCreator Prog ()
message = lift . message_

message_ s = tell [Just $ Right $ "message: " ++ s]

send x y = lift (tell [Nothing]) >> writeRef x y
message' s = lift $ tell [Just $ Left $ "message: " ++ s]

runProg :: String -> (forall s . Prog s ()) -> IO ()
runProg name p = showRes . f [] . snd $ runST $ runWriterT p
  where
    showRes [] = return ()
    showRes xs = fail $ "\ntest " ++ name ++ " failed.\n" ++ unlines xs ++ "\n"

    f acc (Just (Right x): xs) = f (acc ++ [x]) xs
    f (s:acc) (Just (Left s'): xs) | s == s' = f acc xs
    f [] (Nothing: xs) = f [] xs
    f acc (Just (Left s'): _) = acc ++ ["Left " ++ s'] -- s == s' = f acc xs
    f acc _ = acc


-- | Look inside the sources for the tests.
runTests :: IO ()
runTests = do

    let runTest :: String -> (forall s . RefCreator (Prog s) (RefWriter (Prog s) ())) -> IO ()
        runTest name t = runProg name $ join $ runRefCreator $ \runRefWriter -> t <&> runRefWriter

        a ==? b = when (a /= b) $ message $ show a ++ " /= " ++ show b

        r ==> v = readerToWriter (readRef r) >>= (==? v)

    runTest "newRefTest" $ do
        r <- newRef (3 :: Int)
        return $ do
            r ==> 3

    runTest "writeRefsTest" $ do
        r1 <- newRef (3 :: Int)
        r2 <- newRef (13 :: Int)
        return $ do
            r1 ==> 3
            r2 ==> 13
            writeRef r1 4
            r1 ==> 4
            r2 ==> 13
            writeRef r2 0
            r1 ==> 4
            r2 ==> 0

{-
    runTest "traversalMap" $ do
        r <- newRef ["a","b","c"]
        let q = traversalMap traverse r
        q ==> "abc"
        writeRef q "x"
        q ==> "xxx"
        r ==> ["x","x","x"]
-}
    runTest "extRefTest" $ do
        r <- newRef $ Just (3 :: Int)
        q <- extendRef r maybeLens (False, 0)
        let q1 = _1 `lensMap` q
            q2 = _2 `lensMap` q
        return $ do
            r ==> Just 3
            q ==> (True, 3)
            writeRef r Nothing
            r ==> Nothing
            q ==> (False, 3)
            q1 ==> False
            writeRef q1 True
            q1 ==> True
            r ==> Just 3
            writeRef q2 1
            r ==> Just 1

    runTest "joinTest" $ do
        r2 <- newRef (5 :: Int)
        r1 <- newRef 8
        rr <- newRef r1
        return $ do
            r1 ==> 8
            let r = joinRef $ readRef rr
            r ==> 8
            writeRef r1 4
            r ==> 4
            writeRef r 3
            r1 ==> 3
            r2 ==> 5
            writeRef rr r2
            r2 ==> 5
            r ==> 5
            writeRef r1 4
            r ==> 5
            writeRef r2 14
            r ==> 14
            writeRef r 10
            r1 ==> 4
            r2 ==> 10
            writeRef rr r1
            r ==> 4
            r1 ==> 4
            r2 ==> 10
            writeRef r 11
            r ==> 11
            r1 ==> 11
            r2 ==> 10

    runTest "join + ext" $ do
        r2 <- newRef $ Just (5 :: Int)
        r1 <- newRef (Nothing :: Maybe Int)
        rr <- newRef r1
        let r = joinRef $ readRef rr
        q <- extendRef r maybeLens (False, 0)
        let q1 = _1 `lensMap` q
        return $ do
            q ==> (False, 0)
            writeRef r1 $ Just 4
            q ==> (True, 4)
            writeRef q1 False
            r1 ==> Nothing
            writeRef rr r2
            q ==> (True, 5)
            writeRef r1 $ Just 6
            q ==> (True, 5)
            r2 ==> Just 5
            writeRef r2 $ Just 7
            q ==> (True, 7)
            r1 ==> Just 6
            writeRef q1 False
            r2 ==> Nothing
            r1 ==> Just 6
            writeRef q1 True
            r2 ==> Just 7
            r1 ==> Just 6
            writeRef r2 Nothing
            r1 ==> Just 6
            q ==> (False, 7)
            writeRef r1 Nothing
            q ==> (False, 7)

{-
    runTest "join + lensMap id + ext" $ do
        r2 <- newRef $ Just (5 :: Int)
        r1 <- newRef Nothing
        rr <- newRef $ lensMap id r1
        let r = lensMap id $ join $ readRef $ lensMap id rr
        q <- extendRef r maybeLens (False, 0)
        let q1 = _1 `lensMap` q
            q2 = _2 `lensMap` q
        q ==> (False, 0)
        writeRef r1 $ Just 4
        q ==> (True, 4)
        writeRef q1 False
        r1 ==> Nothing
        writeRef rr r2
        q ==> (True, 5)
        writeRef r1 $ Just 6
        q ==> (True, 5)
        r2 ==> Just 5
        writeRef q1 False
        r2 ==> Nothing
        r1 ==> Just 6
        writeRef q1 True
        r2 ==> Just 5
        r1 ==> Just 6
        writeRef r2 Nothing
        r1 ==> Just 6
        q ==> (True, 5)
-}
    runTest "join + ext 2" $ do
        r2 <- newRef $ Just (5 :: Int)
        r1 <- newRef Nothing
        rr <- newRef True
        let r = joinRef $ do
                b <- readRef rr
                pure $ if b then r1 else r2
        q <- extendRef r maybeLens (False, 0)
        let q1 = _1 `lensMap` q
        return $ do
            q ==> (False, 0)
            writeRef r1 $ Just 4
            q ==> (True, 4)
            writeRef q1 False
            r1 ==> Nothing
            writeRef rr False
            q ==> (True, 5)
            writeRef r1 $ Just 6
            q ==> (True, 5)
            r2 ==> Just 5
            writeRef q1 False
            r2 ==> Nothing
            r1 ==> Just 6
            writeRef q1 True
            r2 ==> Just 5
            r1 ==> Just 6
            writeRef r2 Nothing
            r1 ==> Just 6
            q ==> (False, 5)

    runTest "joinTest2" $ do
        r1 <- newRef (3 :: Int)
        rr <- newRef r1
        r2 <- newRef 5
        return $ do
            writeRef rr r2
            joinRef (readRef rr) ==> 5

    runTest "chainTest0" $ do
        r <- newRef (1 :: Int)
        q <- extendRef r id 0
        s <- extendRef q id 0
        return $ do
            r ==> 1
            q ==> 1
            s ==> 1
            writeRef r 2
            r ==> 2
            q ==> 2
            s ==> 2
            writeRef q 3
            r ==> 3
            q ==> 3
            s ==> 3
            writeRef s 4
            r ==> 4
            q ==> 4
            s ==> 4

    runTest "forkTest" $ do
        r <- newRef (1 :: Int)
        q <- extendRef r id 0
        s <- extendRef r id 0
        return $ do
            r ==> 1
            q ==> 1
            s ==> 1
            writeRef r 2
            r ==> 2
            q ==> 2
            s ==> 2
            writeRef q 3
            r ==> 3
            q ==> 3
            s ==> 3
            writeRef s 4
            r ==> 4
            q ==> 4
            s ==> 4

    runTest "forkTest2" $ do
        r <- newRef $ Just (1 :: Int)
        q <- extendRef r maybeLens (False, 0)
        s <- extendRef r maybeLens (False, 0)
        return $ do
            r ==> Just 1
            q ==> (True, 1)
            s ==> (True, 1)
            writeRef r $ Just 2
            r ==> Just 2
            q ==> (True, 2)
            s ==> (True, 2)
            writeRef r Nothing
            r ==> Nothing
            q ==> (False, 2)
            s ==> (False, 2)
            writeRef (_1 `lensMap` q) True
            r ==> Just 2
            q ==> (True, 2)
            s ==> (True, 2)
            writeRef (_2 `lensMap` q) 3
            r ==> Just 3
            q ==> (True, 3)
            s ==> (True, 3)
            writeRef (_1 `lensMap` q) False
            r ==> Nothing
            q ==> (False, 3)
            s ==> (False, 3)
            writeRef (_2 `lensMap` q) 4
            r ==> Nothing
            q ==> (False, 4)
            s ==> (False, 3)
            writeRef (_1 `lensMap` q) True
            r ==> Just 4
            q ==> (True, 4)
            s ==> (True, 4)
            writeRef q (False, 5)
            r ==> Nothing
            q ==> (False, 5)
            s ==> (False, 4)
            writeRef (_1 `lensMap` s) True
            r ==> Just 4
            q ==> (True, 4)
            s ==> (True, 4)

    runTest "chainTest" $ do
        r <- newRef $ Just Nothing
        q <- extendRef r maybeLens (False, Nothing)
        s <- extendRef (_2 `lensMap` q) maybeLens (False, 3 :: Int)
        return $ do
            writeRef (_1 `lensMap` s) False
            r ==> Just Nothing
            q ==> (True, Nothing)
            s ==> (False, 3)
            writeRef (_1 `lensMap` q) False
            r ==> Nothing
            q ==> (False, Nothing)
            s ==> (False, 3)

    runTest "chainTest1" $ do
        r <- newRef $ Just $ Just (3 :: Int)
        q <- extendRef r maybeLens (False, Nothing)
        s <- extendRef (_2 `lensMap` q) maybeLens (False, 0 :: Int)
        return $ do
            r ==> Just (Just 3)
            q ==> (True, Just 3)
            s ==> (True, 3)
            writeRef (_1 `lensMap` s) False
            r ==> Just Nothing
            q ==> (True, Nothing)
            s ==> (False, 3)
            writeRef (_1 `lensMap` q) False
            r ==> Nothing
            q ==> (False, Nothing)
            s ==> (False, 3)
            writeRef (_1 `lensMap` s) True
            r ==> Nothing
            q ==> (False, Just 3)
            s ==> (True, 3)
            writeRef (_1 `lensMap` q) True
            r ==> Just (Just 3)
            q ==> (True, Just 3)
            s ==> (True, 3)

    runTest "mapchain" $ do
        r <- newRef 'x'
        let q = iterate (lensMap id) r !! 10
        return $ do
            q ==> 'x'
            writeRef q 'y'
            q ==> 'y'

    runTest "joinchain" $ do
        rb <- newRef True
        r1 <- newRef 'x'
        r2 <- newRef 'y'
        let f (r1, r2) = (r1', r2') where
                r1' = joinRef $ readRef rb <&> \b -> if b then r1 else r2
                r2' = joinRef $ readRef rb <&> \b -> if b then r2 else r1
            (r1', r2') = iterate f (r1, r2) !! 10
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

    runTest "undoTest" $ do
        r <- newRef (3 :: Int)
        q <- extendRef r (lens head $ flip (:)) []
        return $ do
            writeRef r 4
            q ==> [4, 3]

    runTest "undoTest2" $ do
        r <- newRef (3 :: Int)
        q <- extendRef r (lens head $ flip (:)) []
        return $ do
            q ==> [3]


    let
        perform m = m >>= maybe (pure ()) id
        m === t = m >>= \x -> isJust x ==? t

    runTest "undoTest3" $ do
        r <- newRef (3 :: Int)
        (undo, redo) <- fmap (readerToWriter *** readerToWriter) $ undoTr (==) r
        return $ do
            r ==> 3
            redo === False
            undo === False
            writeRef r 4
            r ==> 4
            redo === False
            undo === True
            writeRef r 5
            r ==> 5
            redo === False
            undo === True
            perform undo
            r ==> 4
            redo === True
            undo === True
            perform undo
            r ==> 3
            redo === True
            undo === False
            perform redo
            r ==> 4
            redo === True
            undo === True
            writeRef r 6
            r ==> 6
            redo === False
            undo === True

    runTest "time" $ do
        t1 <- newRef "z"
        r <- newRef "a"
        q_ <- extendRef r (lens fst (\_ x -> (x, ""))) ("","")
        let q = lensMap _2 q_
        t2 <- newRef "z"
        return $ do
            writeRef q "."
            q ==> "."
            writeRef t2 "q"
            q ==> "."
            writeRef t1 "q"
            q ==> "."

{- TODO
    runTest "recursion" $ do
        r <- newRef "x"
        rr <- newRef r
        let r' = join $ readRef rr
        r' ==> "x"
        writeRef rr r'
        r' ==> "x"
-}

    runTest "trivial" $ return $ return ()

    runTest "message" $ do
        message "Hello"
        return $ do
            message' "Hello"


{- not valid
    runTest "listeners" (do
        listen 1 $ \s -> message $ "Hello " ++ s
        listen 2 $ \s -> message $ "Hi " ++ s
        listen 3 $ \s -> do
            message $ "H_ " ++ s
            listen 4 $ \s' ->
                message $ "H " ++ s'
      ) $ do
        message' "listener #0"
        message' "listener #1"
        message' "listener #2"
        pure $ (,) () $ do
            send 1 "d"
            message' "Hello d"
            send 1 "f"
            message' "Hello f"
            send 2 "f"
            message' "Hi f"
            send 3 "f"
            message' "H_ f"
            message' "listener #3"
            send 4 "f"
            message' "H f"
-}

    runTest "onChangeEq" $ do
        r <- newRef "x"
        _ <- onChangeEq (readRef r) message
        return $ do
            message' "x"
            send r "x"
            send r "y"
            message' "y"

    runTest "onChangeEq + listener" $ do
        r1 <- newRef "x"
        r2 <- newRef "y"
        _ <- onChangeEq (liftA2 (++) (readRef r1) (readRef r2)) message
        return $ do
            message' "xy"
            send r1 "x"
            send r2 "y"
            send r1 "y"
            message' "yy"
            send r2 "y"
            send r2 "x"
            message' "yx"

    runTest "onChangeEq + join" $ do
        r1 <- newRef "x"
        r2 <- newRef "y"
        rr <- newRef r1
        _ <- onChangeEq (readRef $ joinRef $ readRef rr) message
        return $ do
            message' "x"
            send r1 "x"
            send r2 "y"
            send r1 "y"
            message' "y"
            send r2 "y"
            send r2 "x"
            send rr r2
            message' "x"
            send r1 "a"
            send r2 "b"
            message' "b"
            send r2 "c"
            message' "c"

    let showStatus msg = onRegionStatusChange $ \s -> message_ $ show s ++ " " ++ msg

    runTest "kill & block" $ do
        r <- newRef (0 :: Int)
        _ <- onChangeMemo (readRef r) $ \i -> case i of
            0 -> return $ showStatus "#0"
            1 -> do
                showStatus "#1"
                return $ return ()
            _ -> error $ "Unexpected value for r in kill & block: " ++ show i

        return $ do
            send r 0
            send r 1
            message' "Kill #0"
            send r 1
            send r 0
            message' "Block #1"
            send r 1
            message' "Kill #0"
            message' "Unblock #1"


    runTest "bla2" $ do
        r <- newRef $ Just (3 :: Int)
        q <- extendRef r maybeLens (False, 0)
        let q1 = _1 `lensMap` q
            q2 = _2 `lensMap` q
        _ <- onChangeEq (readRef r) $ message . show
        _ <- onChangeEq (readRef q) $ message . show
        return $ do
            message' "Just 3"
            message' "(True,3)"
            send r (Nothing :: Maybe Int)
            message' "Nothing"
            message' "(False,3)"
            send q1 True
            message' "Just 3"
            message' "(True,3)"
            send q2 (1 :: Int)
            message' "Just 1"
            message' "(True,1)"

    runTest "onChangeEq value" $ do
        r <- newRef (0 :: Int)
        q <- onChangeEq (readRef r) pure
        _ <- onChangeEq q $ message . show
        return $ do
            message' "0"
            send r (1 :: Int)
            message' "1"
            send r (2 :: Int)
            message' "2"
            send r (3 :: Int)
            message' "3"
            send r (3 :: Int)
            send r (4 :: Int)
            message' "4"
{-
    runTest "schedule" (do
        r <- newRef "a"
        q <- newRef "b"
        _ <- onChangeEq (readRef r) message
        _ <- onChangeEq (readRef q) message
        listen 0 $ \(x,y) -> writeRef r x >> writeRef q y
        listen 1 $ \(x,y) -> writeRef q y >> writeRef r x
        ) $ do
        message' "a"
        message' "b"
        message' "listener #0"
        message' "listener #1"
        pure $ (,) () $ do
            send 0 ("x", "y")
            message' "x"
            message' "y"
            send 1 ("1", "2")
            message' "2"
            message' "1"
-}
{- TODO
    runTest "diamond" (do
        r <- newRef "a"
        q <- newRef "b"
        rq <- onChangeEq (liftA2 (++) (readRef r) (readRef q)) $ pure . pure
        _ <- onChangeEq (join rq) message
        postponeModification $ message "." >> writeRef r "x" >> writeRef q "y"
        postponeModification $ message ".." >> writeRef q "1" >> writeRef r "2"
        ) $ do
        message' "ab"
        pure $ (,) () $ do
            message' "."
            message' "xy"
            message' ".."
            message' "21"
-}
    runTest "ordering" $ do
        t1 <- newRef $ Just (3 :: Int)
        t <- newRef t1
        let r = joinRef $ readRef t
        q <- extendRef r maybeLens (False, 0)
        let q1 = _1 `lensMap` q
            q2 = _2 `lensMap` q
        t2 <- newRef $ Just (3 :: Int)
        return $ do
            r ==> Just 3
            q ==> (True, 3)
            writeRef r Nothing
            r ==> Nothing
            q ==> (False, 3)
            q1 ==> False
            writeRef q1 True
            r ==> Just 3
            writeRef q2 1
            r ==> Just 1
            writeRef t t2
            r ==> Just 3
            q ==> (True, 3)
            writeRef r Nothing
            r ==> Nothing
            q ==> (False, 3)
            q1 ==> False
            writeRef q1 True
            r ==> Just 3
            writeRef q2 1
            r ==> Just 1

{- not ready
    runTest "notebook" $ do 
        buttons <- newRef ("",[])
        let ctrl = lens fst (\(_,xs) x -> ("",x:xs)) `lensMap` buttons

            h b = do
                q <- extendRef b listLens (False, ("", []))
                onChangeMemo (fst <$> readRef q) $ \bb -> return $ case bb of
                    False -> pure $ pure []
                    _ -> do
                        r <- h $ _2 . _2 `lensMap` q
                        pure $ ((_2 . _1 `lensMap` q) :) <$> join r

        r <- fmap join $ h $ _2 `lensMap` buttons

        let act i f = do
                xs <- readRef r
                when (length xs <= i) $ fail' "nootebook error"
                f $ xs !! i

        writeRef ctrl "a"
        buttons ==> ("", ["a"])
        act 0 $ \rr -> writeRef ctrl "a"
-}

{- not valid
    runTest "listen-listen" (do
        listen 1 $ \s -> case s of
            "x" -> listen 2 message
            _ -> pure ()
        ) $ do
        message' "listener #0"
        pure $ (,) () $ do
            send 1 "d"
            send 2 "hi"
            error' "message is not received: 2 \"hi\""
            send 1 "d"
            send 1 "x"
            message' "listener #1"
            send 2 "hi"
            message' "hi"
            send 1 "x"
            message' "listener #2"
            send 2 "hi"
            message' "hi"
            message' "hi"
            send 2 "hi"
            message' "hi"
            message' "hi"
            send 1 "d"
            send 2 "hi"
            message' "hi"
            message' "hi"
            send 1 "x"
            message' "listener #3"
            send 2 "hi"
            message' "hi"
            message' "hi"
            message' "hi"

    runTest "listen-onChangeEq" (do
        r <- newRef "k"
        listen 1 $ \s -> case s of
            "x" -> onChangeEq (readRef r) message >> pure ()
            _ -> writeRef r s
        ) $ do
        message' "listener #0"
        pure $ (,) () $ do
            send 1 "d"
            send 1 "x"
            message' "d"
            send 1 "d"
            send 1 "e"
            send 1 "x"
            message' "e"
--            message' "x"
            send 1 "f"
--            message' "f"
-}
    
    runTest "onChange + onChange + onRegionStatusChange" $ do
        a <- newRef True
        b <- newRef ()
        _ <- onChange (readRef a) $ \v -> case v of
            True -> do
                void $ onChange (readRef b) $ const $ onRegionStatusChange $ message_ . (++ "1") . show
                void $ onChangeEq (readRef b) $ const $ onRegionStatusChange $ message_ . (++ "2") . show
                void $ onChangeEq_ (readRef b) $ const $ onRegionStatusChange $ message_ . (++ "3") . show
                void $ onChangeMemo (readRef b) $ const $ do
                    onRegionStatusChange $ message_ . (++ "4") . show
                    return $ onRegionStatusChange $ message_ . (++ "5") . show
            False -> return ()
        return $ do
            writeRef a False
            message' "Kill1"
            message' "Kill2"
            message' "Kill3"
            message' "Kill4"
            message' "Kill5"

    runTest "issue1" $ do
        r <- newRef (0 :: Int)
        le <- onChangeEq (fmap (min 1) $ readRef r) $ \b -> do
            case b of
                0 -> return $ pure 0
                1 -> onChange (readRef r) return
                _ -> error "impossible"

        _ <- onChange (liftM2 (,) (readRef r) (join le)) $ message . show

        return $ do
            message' "(0,0)"
            send r 1
            message' "(1,1)"
            send r 2
            message' "(2,2)"

    runTest "issue2" $ do
        r <- newRef ()
        _ <- onChange (readRef r) $ \_ -> void $ extendRef r id ()
        return $ writeRef r ()

    runTest "issue3" $ do
        let
            undo (x: xs@(_:_), ys) = (xs, x: ys)
            undo _ = error "impossible"

            undoLens = lens get set where
                get = head . fst
                set (xs, _) x = (x : xs, [])
        list_ <- newRef True
        ku <- extendRef list_ undoLens ([], [])

        _ <- onChange (readRef list_) $ message . show

        return $ do
            message' "True"
            writeRef list_ False
            message' "False"
            modRef ku undo
            message' "True"

    runTest "issue4" $ do
        r <- newRef False
        b <- onChange (readRef r) $ \b -> do
          case b of
            False -> pure $ pure True
            True -> do
                r' <- onChange (readRef r) return
                onChange r' return

        void $ onChange (join b) $ const $ message "y"

        return $ do
            message' "y"
            writeRef r True
            message' "y"
            writeRef r False
            message' "y"

    return ()


-------------------------- auxiliary definitions

maybeLens :: Lens' (Bool, a) (Maybe a)
maybeLens = lens (\(b,a) -> if b then Just a else Nothing)
              (\(_,a) -> maybe (False, a) (\a' -> (True, a')))

-- | Undo-redo state transformation.
undoTr
    :: (RefContext m)
    => (a -> a -> Bool)     -- ^ equality on state
    -> Ref m a             -- ^ reference of state
    -> RefCreator m ( RefReader m (Maybe (RefWriter m ()))
           , RefReader m (Maybe (RefWriter m ()))
           )  -- ^ undo and redo actions
undoTr eq r = do
    ku <- extendRef r (undoLens eq) ([], [])
    let try f = fmap (fmap (writeRef ku) . f) $ readRef ku
    pure (try undo, try redo)
  where
    undo (x: xs@(_:_), ys) = Just (xs, x: ys)
    undo _ = Nothing

    redo (xs, y: ys) = Just (y: xs, ys)
    redo _ = Nothing

undoLens :: (a -> a -> Bool) -> Lens' ([a],[a]) a
undoLens eq = lens get set where
    get = head . fst
    set (x' : xs, ys) x | eq x x' = (x: xs, ys)
    set (xs, _) x = (x : xs, [])

