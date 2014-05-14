{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_HADDOCK hide #-}
module Data.LensRef.TestEnv where

import Control.Monad.State
import Control.Monad.Writer hiding (listen, Any)
import Control.Monad.Operational
import qualified Data.Sequence as Seq
import Control.Lens hiding ((|>), view)

import Unsafe.Coerce

import Data.LensRef
import Data.LensRef.Common

----------------------


class MonadRegister tm => MonadRegisterRun tm where

    type AsocT tm :: *

    runReg :: (m ~ EffectM tm)
        => m (AsocT tm)
        -> (AsocT tm -> m ())
        -> tm a
        -> m (a, m ())



--------------------------

newtype Id = Id Int deriving Eq

instance Show Id where show (Id i) = "#" ++ show i

newtype Port a = Port { unPort :: Int } deriving (Eq, Num)

instance Show (Port a) where show (Port i) = show i

data Inst t a where
    Message  :: String -> Inst t ()
    Listen   :: Show b => Port b -> (b -> Prog t ()) -> Inst t Id
    SetStatus  :: Id -> RegionStatusChange -> Inst t ()

    ReadI :: Inst t t
    WriteI :: t -> Inst t ()
    NewRef :: a -> Inst t (Morph (StateT a (Prog t)) (Prog t))

type Prog t = ProgramT (Inst t) (State (Seq.Seq Any))


---------------------------------------------------

instance NewRef (Prog t) where
    newRef' = singleton . NewRef

message :: (MonadRegister m, EffectM m ~ Prog t) => String -> m ()
message = liftEffectM . singleton . Message

listen :: (MonadRegister m, EffectM m ~ Prog t, Show a) => Port a -> (a -> Modifier m ()) -> m ()
listen i m = do
    f <- registerCallback m
    id <- liftEffectM . singleton $ Listen i f
    message $ "listener " ++ show id
    onRegionStatusChange $ \s -> do
        liftEffectM . singleton $ SetStatus id s
        when (s == Kill) $ message $ show s ++ " " ++ show id


data Inst' a where
    Message' :: String -> Inst' ()
    Error'   :: String -> Inst' ()
    Send     :: forall a . Show a => Port a -> a -> Inst' ()

type Prog' = Program Inst'

message' = singleton . Message'
error' = singleton . Error'
send i s = singleton $ Send i s

--getProg' :: MonadError String m => Prog' b -> m b
getProg' :: Prog' b
    -> StateT s Er b
getProg' p = case runIdentity . viewT $ p of
    Return x -> return x
    Send i s :>>= p -> do
        fail' $ "end expected instead of send " ++ show i ++ " " ++ show s
        getProg' $ p ()
    Message' s :>>= p -> do
        fail' $ "end expected instead of message' " ++ s
        getProg' $ p ()
    Error' s :>>= p -> do
        fail' $ "end expected instead of unfail " ++ s
        getProg' $ p ()
  

type Er = Writer [Either (Either String String) String] --ErrorT String (Writer [String])

tell_ s = tell [Right s]
fail' s = tell [Left $ Right s]
unfail s = tell [Left $ Left s]
handEr name = showRes name . runWriter -- . runErrorT
showRes name ((),l) = case f [] l of
    [] -> []
    xs -> ("test " ++ name ++ " failed.") : xs ++ [""]
  where
    f acc (Right x: xs) = f (x:acc) xs
    f acc (Left (Right s): Left (Left s'): xs) | s == s' = f (("unfail " ++ s'): acc) xs
    f acc (Left e: _) = reverse $ either id id e: acc
    f _ [] = []

data Any = forall x . Any x

data Listener m = forall a . Show a => Listener
    { _listenerId :: Id
    , _listenerPort :: Port a
    , _listenerStatus :: RegionStatusChange
    , _listenerCallback :: a -> Prog m ()
    }
makeLenses ''Listener

data ST m = ST
    { _postponed :: [m]
    , _listeners :: [Listener m]
    , _idcounter :: Int
    , _vars :: Seq.Seq Any
    }
makeLenses ''ST


coeval_ :: forall a b m
     . (Prog m () -> m)
    -> Prog m a
    -> Prog' b
    -> StateT (ST m) Er (Maybe a, Prog' b)
coeval_ lift_ q p = do
    op <- zoom vars $ mapStateT lift $ viewT q
    coeval__ lift_ op p

coeval__ :: forall a b m
     . (Prog m () -> m)
    -> ProgramViewT (Inst m) (State (Seq.Seq Any)) a
    -> Prog' b
    -> StateT (ST m) Er (Maybe a, Prog' b)
coeval__ lift_ op p = do
  nopostponed <- use $ postponed . to null
  case (op, view p) of

    (_, Error' s :>>= k) -> do
        unfail s
        coeval__ lift_ op $ k ()

    (Message s :>>= k, Return x) -> do
        fail' $ "the following message expected: " ++ s ++ " instead of return"
        coeval_ lift_ (k ()) (return x)

    (Message s :>>= k, Message' s' :>>= k')
        | s == s' -> do
            tell_ ("message: " ++ s)
            coeval_ lift_ (k ()) (k' ())
        | otherwise -> do
            fail' $ "the following message expected: " ++ s ++ " instead of " ++ s'
            coeval__ lift_ op $ k' ()

    (Message s :>>= _, Send _i s' :>>= k') -> do
        fail' $ "the following message expected: " ++ s ++ " instead of send " ++ show s'
        coeval__ lift_ op (k' ())

    (SetStatus i status :>>= k, _) -> do
        listeners %= case status of
            Kill -> filter ((/=i) . (^. listenerId))
            Block -> map f where
                f (Listener i' c Unblock x) | i' == i = Listener i c Block x
                f x = x
            Unblock -> map f where
                f (Listener i' c Block x) | i' == i = Listener i c Unblock x
                f x = x
        coeval_ lift_ (k ()) p

    (Listen i lr :>>= k, _) -> do
        co <- use idcounter
        listeners %= (Listener (Id co) i Unblock lr :)
        idcounter %= (+1)
        coeval_ lift_ (k $ Id co) p

    (ReadI :>>= k, _) | not nopostponed -> do
        x <- use $ postponed . to head
        postponed %= tail
        coeval_ lift_ (k x) p

    (WriteI x :>>= k, _) -> do
        postponed %= (++[x])
        coeval_ lift_ (k ()) p

    (NewRef a :>>= k, _) -> do
        n <- use $ vars . to Seq.length

        let ff :: forall aa bb . aa -> StateT aa (Prog m) bb -> Prog m bb
            ff _ (StateT f) = do
                v <- gets (`Seq.index` n)
                modify $ Seq.update n $ error "recursive reference modification"
                case v of
                  Any w -> do
                    (x, w') <- f $ unsafeCoerce w
                    modify $ Seq.update n $ Any w'
                    return x
        vars %= (Seq.|> Any a)
        coeval_ lift_ (k $ Morph $ ff a) p

    (_, Send i@(Port pi) s :>>= k) -> do
        tell_ $ "send " ++ show i ++ " " ++ show s
        if not nopostponed
          then do
            fail' $ "early send of " ++ show s
          else do
            li' <- use $ listeners . to (\li -> [lift_ $ lr $ unsafeCoerce s | Listener _ (Port pi') Unblock lr <- li, pi == pi'])
            if (null li')
              then do
                fail' $ "message is not received: " ++ show i ++ " " ++ show s
              else do
                postponed %= (++ li')
        coeval__ lift_ op (k ())

    (ReadI :>>= _, _) | nopostponed -> return (Nothing, p)

    (Return x, _) -> return (Just x, p)



runTest_ :: (Eq a, Show a, m ~ Prog n)
    => String
    -> (Prog n () -> n)
    -> (m n -> (n -> m ()) -> tm a -> m (a, m ()))
    -> tm a
    -> Prog' (a, Prog' ())
    -> IO ()
runTest_ name lift runRegister_ r p0 = putStr $ unlines $ handEr name $ flip evalStateT (ST [] [] 0 Seq.empty) $ do
    (Just (a1,c),pe) <- coeval_ lift (runRegister_ (singleton ReadI) (singleton . WriteI) r) p0
    (a2,p) <- getProg' pe
    when (a1 /= a2) $ fail' $ "results differ: " ++ show a1 ++ " vs " ++ show a2
    (_, pr) <- coeval_ lift c p
    getProg' pr

------------------------------------------------

-- | Check an equality.
(==?) :: (Eq a, Show a, MonadRegisterRun m, EffectM m ~ Prog (AsocT m)) => a -> a -> m ()
rv ==? v = when (rv /= v) $ message $ "runTest failed: " ++ show rv ++ " /= " ++ show v

-- | Check the current value of a given reference.
(==>) :: (Eq a, Show a, MonadRegisterRun m, EffectM m ~ Prog (AsocT m)) => Ref m a -> a -> m ()
r ==> v = readRef r >>= (==? v)

infix 0 ==>, ==?




