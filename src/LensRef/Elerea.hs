{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE RecursiveDo #-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
module LensRef.Elerea
    (
      elerea
    , IO'
    , neutral
    , postpone
    , rev

    -- * The signal abstraction
    , Signal
    , SignalGen
    -- * Embedding into I/O
    , start
    , external
    , externalMulti
    -- * Basic building blocks
    , delay
    , snapshot
    , generator
    , memo
    , until
    -- * Derived combinators
    , stateful
    , transfer
    , transfer2
    , transfer3
    , transfer4
    -- * Signals with side effects
    , execute
    , effectful
    , effectful1
    , effectful2
    , effectful3
    , effectful4

    , test, test2
    ) where

import Data.IORef
import Control.Applicative
import Control.Arrow
import Control.Monad.Reader

--import Lens.Family2
--import Lens.Family2.State
--import Lens.Family2.Unchecked
--import Lens.Family2.Stock

--import Debug.Trace
import Prelude hiding (until)

import LensRef
    ( {-Monad'
    , -}MonadTrace (..), SimpleRefs(..), modSimpleRef
    , Reversible(..), ReversibleT, runRev, postponed, reversible, neut
    , Ref
    , RefWriter, writeRef, creatorToWriter
    , RefReader, readRef
    , RefCreator, readerToCreator, newRef, delayPrev, generator', joinCreator -- , stabilize_
    , runRefCreator
    )

infixl 1 <&>
(<&>) = flip (<$>)


type Signal = RefReader IO_
type SignalGen = ReaderT (Ref IO_ ()) (RefCreator IO_)
type IO' = RefWriter IO_

--newtype IO_ a = IO_ { runBase :: ReaderT BaseRun IO a }
newtype IO_ a = IO_ { runBase :: ReaderT BaseRun (ReversibleT IO) a }
    deriving (Functor, Applicative, Monad, MonadFix)

newtype BaseRun = BaseRun { runBaseRun :: forall a . IO' a -> IO_ a }

instance MonadTrace IO_ where
    traceM = IO_ . traceM

instance Reversible IO_ where
    restore m = IO_ $ restore $ runBase m <&> (runBase +++ id)

neutral :: IO a -> IO' a
neutral = lift . IO_ . lift . neut

postpone :: IO () -> IO' ()
postpone = lift . IO_ . lift . postponed

rev :: IO (a, IO ()) -> IO' a
rev = lift . IO_ . lift . reversible

instance SimpleRefs IO_ where
    type SimpleRef IO_ = IORef
    newSimpleRef     = IO_ . newSimpleRef
    readSimpleRef    = IO_ . readSimpleRef
    writeSimpleRef r = IO_ . writeSimpleRef r

down_ :: IO' a -> IO_ a
down_ m = do
    br <- IO_ ask
    runBaseRun br m

elerea :: IO' a -> IO a
elerea m = mdo
    let run :: forall a . IO_ a -> IO a
        run = runRev . flip runReaderT br . runBase
    br <- run $ runRefCreator $ \w -> return $ BaseRun w
    run $ down_ m

-------------------------------------------------------------------------------- core

start :: SignalGen (Signal a) -> IO' (IO' a)
start s = creatorToWriter $ do
    t <- newRef ()
    x <- runReaderT s t
    i <- newSimpleRef True
    return $ do
        init <- modSimpleRef i $ \x -> return (False, x)
        when (not init) $ writeRef t ()
        creatorToWriter $ readerToCreator x

external :: a -> IO' (Signal a, a -> IO' ())
external init = creatorToWriter $ do
    r <- newRef init
    return (readRef r, writeRef r)

externalMulti :: IO' (SignalGen (Signal [a]), a -> IO' ())
externalMulti = creatorToWriter $ do
    r <- newSimpleRef []
    let mk = ReaderT $ \t -> joinCreator $ readRef t <&> \() -> modSimpleRef r $ \x -> return ([], x)
    return (mk, \a -> modSimpleRef r $ \as -> return (a:as, ()))

delay :: a -> Signal a -> SignalGen (Signal a)
delay x s = ReaderT $ \t -> delayPrev x (const id <$> readRef t) s

snapshot :: Signal a -> SignalGen a
snapshot = lift . readerToCreator

generator :: Signal (SignalGen a) -> SignalGen (Signal a)
generator s = ReaderT $ \t -> generator' $ readRef t <&> \() -> join $ flip runReaderT t <$> readerToCreator s

-- TODO: try to break this
execute :: IO' a -> SignalGen a
execute = lift . lift . down_

-------------------------------------------------------------------------------- for efficiency

-- TODO: optimize
until :: Signal Bool -> SignalGen (Signal Bool)
until s = do
    step <- transfer False (||) s
    dstep <- delay False step
    memo (liftA2 (/=) step dstep)

-- TODO: optimize
memo :: Signal a -> SignalGen (Signal a)
memo r = return r --lift $ readerToCreator r >>= \a -> readRef <$> stabilize_ (\_ _ -> False) a r

-------------------------------------------------------------------------------- derived

stateful :: a -> (a -> a) -> SignalGen (Signal a)
stateful x0 f = mfix $ \sig -> delay x0 (f <$> sig)

transfer :: a -> (t -> a -> a) -> Signal t -> SignalGen (Signal a)
transfer x0 f s = mfix $ \sig -> do
    sig' <- delay x0 sig
    memo $ f <$> s <*> sig'     -- TODO: why memo?

transfer2 :: a -> (t1 -> t2 -> a -> a) -> Signal t1 -> Signal t2 -> SignalGen (Signal a)
transfer2 x0 f s1 s2 = transfer x0 ($) $ f <$> s1 <*> s2

transfer3 :: a -> (t1 -> t2 -> t3 -> a -> a) -> Signal t1 -> Signal t2 -> Signal t3 -> SignalGen (Signal a)
transfer3 x0 f s1 s2 s3 = transfer x0 ($) $ f <$> s1 <*> s2 <*> s3

transfer4 :: a -> (t1 -> t2 -> t3 -> t4 -> a -> a) -> Signal t1 -> Signal t2 -> Signal t3 -> Signal t4 -> SignalGen (Signal a)
transfer4 x0 f s1 s2 s3 s4 = transfer x0 ($) $ f <$> s1 <*> s2 <*> s3 <*> s4

effectful :: IO' a -> SignalGen (Signal a)
effectful = generator . return . execute

effectful1 :: (t -> IO' a) -> Signal t -> SignalGen (Signal a)
effectful1 m s = generator $ execute . m <$> s

effectful2 :: (t1 -> t2 -> IO' a) -> Signal t1 -> Signal t2 -> SignalGen (Signal a)
effectful2 m s1 s2 = generator $ execute <$> (m <$> s1 <*> s2)

effectful3 :: (t1 -> t2 -> t3 -> IO' a) -> Signal t1 -> Signal t2 -> Signal t3 -> SignalGen (Signal a)
effectful3 m s1 s2 s3 = generator $ execute <$> (m <$> s1 <*> s2 <*> s3)

effectful4 :: (t1 -> t2 -> t3 -> t4 -> IO' a) -> Signal t1 -> Signal t2 -> Signal t3 -> Signal t4 -> SignalGen (Signal a)
effectful4 m s1 s2 s3 s4 = generator $ execute <$> (m <$> s1 <*> s2 <*> s3 <*> s4)

--------------------------------------------------------------------------------

test = elerea $ do
    smp <- start $ mdo
        let fib'' = liftA2 (+) fib' fib
        fib' <- delay 1 fib''
        fib <- delay 1 fib'
        return fib
    res <- replicateM 8 smp
    neutral $ print res


test2 = elerea $ do
    smp <- start $ do
        keys <- fmap head <$> flip stateful tail (map Just $ "d d d\n" ++ repeat ' ')
        game (pure 0) renderMenu close keys
    res <- replicateM 8 smp
    sequence_ res
  where
    close = neutral $ print "close!"
    renderMenu _score items i = do
        neutral $ print ("item", items !! i)

    game
      :: Functor f =>
         Signal a1
         -> (a1 -> [[Char]] -> Int -> f ())
         -> f a
         -> Signal (Maybe Char)
         -> SignalGen (Signal (f ()))
    game highScore renderMenu closeAction keys = do
      let firstTrue s = do
            mask <- delay False =<< transfer False (||) s
            return (liftA2 (&&) (not <$> mask) s)

          mkGame 0 = error "evaluated"
          mkGame _ = return (pure (void closeAction),pure True)

          items = ["QUIT","ONE PLAYER GAME","TWO PLAYER GAME","QUIT"]

      (output,_) <- switcher . flip fmap highScore $ \score -> do
        pick <- displayMenu (length items) keys
        let menu = (renderMenu score items <$> pick, pure False)
        picked <- firstTrue ((== Just '\n') <$> keys)
        gameSource <- generator (toMaybe <$> picked <*> (mkGame <$> pick))
        fullOutput <- menu --> gameSource
        return (fst =<< fullOutput,snd =<< fullOutput)

      return output

    displayMenu
      :: Int -> Signal (Maybe Char) -> SignalGen (Signal Int)
    displayMenu n keys = do
      up <- edge ((==Just 'u') <$> keys)
      down <- edge ((==Just 'd') <$> keys)
      item <- transfer2 0 (\u d i -> (i + fromEnum d - fromEnum u) `mod` n) up down

      return item



edge :: Signal Bool -> SignalGen (Signal Bool)
edge s = do
  s' <- delay False s
  return $ s' >>= \x -> if x then return False else s

infix 2 -->

(-->) :: a -> Signal (Maybe a) -> SignalGen (Signal a)
x0 --> s = transfer x0 store s
    where store Nothing  x = x
          store (Just x) _ = x

collection
  :: Signal [Signal b]
     -> Signal (b -> Bool) -> SignalGen (Signal [b])
collection source isAlive = mdo
  sig <- delay [] (map snd <$> collWithVals')
  coll <- memo (liftA2 (++) source sig)
  let collWithVals = zip <$> (sequence =<< coll) <*> coll
  collWithVals' <- memo (filter <$> ((.fst) <$> isAlive) <*> collWithVals)
  return $ map fst <$> collWithVals'

switcher
  :: Signal (SignalGen (Signal b, Signal Bool))
     -> SignalGen (Signal b, Signal Bool)
switcher gen = mdo
  trig <- memo (snd =<< pw)
  trig' <- delay True trig
  ss <- generator (toMaybe <$> trig' <*> gen)
  pw <- undefined --> ss
  return (fst =<< pw,trig)

toMaybe :: Applicative f => Bool -> f a -> f (Maybe a)
toMaybe b s = if b then Just <$> s else pure Nothing

