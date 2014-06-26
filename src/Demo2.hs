{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Demo2 where

import Data.Function
import Data.List
import Data.Maybe
import Data.Traversable hiding (mapM)
import qualified Data.IntMap as Map
import Control.Applicative
import Control.Monad
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Lens.Simple
import System.Posix.IO
--import System.Posix.Types (Fd)

import Data.LensRef
import Data.LensRef.Common
--import Data.LensRef.Fast
import Data.LensRef.Pure

--------------------------------------------------------------------------------

type RefCreator m = RefCreatorT (ReaderT (St m) m)
type RefReader  m = RefReaderT  (ReaderT (St m) m)
type RefWriter  m = RefWriterT  (ReaderT (St m) m)

type Ref   m a = RefOf   (RefCreator m) a
type EqRef m a = EqRefOf (RefCreator m) a

data St m = St
    { newControlId      :: m ControlId
    , registerControl   :: ControlId -> [Action m] -> m ()
    , unregisterControl :: ControlId -> m ()
    , logfun            :: Maybe (Doc -> m ())
    }

type ControlId = Int

data Action m
    = Click (RefWriter m ())             -- button and checkbox
    | Put   (String -> RefWriter m ())   -- entry
    | Get   (RefReader m String)         -- entry and dynamic label

type Widget m = RefCreator m (Layout m)

data Layout m
    = Leaf Doc
    | Node Dir [Layout m]
    | Dyn (RefReader m (Layout m))

data Dir = Horiz | Vert


--------------------------------------------------------------------------------

type Doc = (Int, [String])

text s = (length s, [s])

emptyDoc = (0, [])

horiz, vert :: Doc -> Doc -> Doc

vert (n, s) (m, t) = (k, map (pad (k-n)) s ++ map (pad (k-m)) t)
  where
    k = max n m
    pad n l = l ++ replicate n ' '

horiz (0, _) ys = ys
horiz (n, xs) (m, ys) = (n + m + 1, zipWith (++) (ext n xs) (map (' ':) $ ext m ys))
  where
    h = max (length xs) (length ys)

    ext n l = take h $ l ++ repeat (replicate n ' ')

--------------------------------------------------------------------------------

dyn :: SimpleRefClass m => RefReader m (Layout m) -> Widget m
dyn v = do
    fd <- liftEffectM $ asks logfun
    maybe (pure ()) (void . onChangeEq (v >>= mk) . redraw') fd
    return $ Dyn v
  where
    redraw' out ss = liftEffectM $ lift $ out ss

    mk :: SimpleRefClass m => Layout m -> RefReader m Doc
    mk (Leaf s) = return s
    mk (Node Horiz l) = mapM mk l <&> foldr horiz emptyDoc
    mk (Node Vert l) = mapM mk l <&> foldr vert emptyDoc
    mk (Dyn m) = m >>= mk --return ["*"]


ctrl :: SimpleRefClass m => [Action m] -> RefCreator m ControlId
ctrl c = do
    st <- liftEffectM ask
    i <- liftEffectM $ lift $ newControlId st
    liftEffectM $ lift $ registerControl st i c
    onRegionStatusChange $ \msg -> lift $ do
        maybe (pure ()) ($ text (show msg ++ " " ++ show i)) $ logfun st
        case msg of
            Unblock -> registerControl st i c
            _ -> unregisterControl st i
    return i

label :: SimpleRefClass m => String -> Widget m
label = pure . Leaf . text

color :: Int -> String -> String
color c s = "\x1b[" ++ show c ++ "m" ++ s ++ "\x1b[0m"

red = color 31

leaf :: Int -> Int -> String -> Layout m
leaf c i s = Leaf (length n + length s, [red n ++ color c s])
  where
    n = if i >= 0 then show (i :: Int) else "-"

dynLabel :: SimpleRefClass m => RefReader m String -> Widget m
dynLabel r = do
    i <- ctrl [Get r]
    dyn $ r <&> \s -> leaf 44 i s

primButton
    :: SimpleRefClass m
    => RefReader m String     -- ^ dynamic label of the button
    -> RefReader m Bool       -- ^ the button is active when this returns @True@
    -> RefWriter m ()        -- ^ the action to do when the button is pressed
    -> Widget m
primButton name vis act = dyn . join =<< do
    onChangeMemo vis $ \v -> case v of
        True -> do
            i <- ctrl [Click act]
            return $ return $ name <&> \name -> leaf 45 i name
        False -> return $ return $ name <&> \n -> leaf 45 (-1) n

checkbox :: SimpleRefClass m => Ref m Bool -> Widget m
checkbox r = do
    i <- ctrl [Click $ modRef r not]
    dyn $ readRef r <&> \s -> leaf 46 i $ show s

primEntry :: SimpleRefClass m => (RefClass r, RefReaderSimple r ~ RefReader m)  => (String -> Bool) -> RefSimple r String -> Widget m
primEntry ok r = do
    i <- ctrl [Put $ writeRef r, Get $ readRef r]
    dyn $ readRef r <&> \s -> leaf 42 i $ brack (ok s) s
          where
            brack True s = s
            brack _ s = "{" ++ s ++ "}"

vertically :: SimpleRefClass m => [Widget m] -> Widget m
vertically ws = sequenceA ws <&> Node Vert

horizontally :: SimpleRefClass m => [Widget m] -> Widget m
horizontally ws = sequenceA ws <&> Node Horiz

cell :: SimpleRefClass m => Eq a => RefReader m a -> (a -> Widget m) -> Widget m
cell r f = onChangeMemo r (\v -> f v <&> pure) >>= dyn

runWidget
    :: forall m
    .  SimpleRefClass m
    => Maybe (Doc -> m ())
    -> Maybe (Doc -> m ())
    -> Widget m
    -> m (Int -> m (), Int -> String -> m (), Int -> m String, m Doc)
runWidget log autodraw cw = do
  controlmap <- newSimpleRef mempty
  counter <- newSimpleRef (0 :: Int)
  let st = St
        { newControlId = modSimpleRef counter $ state $ \c -> (c, succ c)
        , registerControl = \i cs -> modSimpleRef controlmap $ modify $ Map.insert i cs
        , unregisterControl = \i -> modSimpleRef controlmap $ modify $ Map.delete i
        , logfun = log
        }
      rr :: SimpleRefClass m => ReaderT (St m) m a -> m a
      rr = flip runReaderT st
  rr $ runRefCreatorT $ \runRefWriter -> do
    w <- cw

    maybe (pure ()) (\out -> void $ onChangeEq (mk w) $ liftEffectM . lift . out) autodraw

    let click cs = head $ [rr $ runRefWriter act | Click act <- cs] ++ [fail "not a button or checkbox"]
        put cs s = head $ [rr $ runRefWriter $ act s | Put act <- cs] ++ [fail "not an entry"]
        get cs   = head $ [rr $ runRefWriter $ liftRefReader act | Get act <- cs] ++ [fail "not an entry or label"]

        lookup_ :: Int -> m [Action m]
        lookup_ i = readSimpleRef controlmap >>= \m -> case Map.lookup i m of
            Just cs -> pure cs
            _ -> fail "control not registered"

        draw = rr $ runRefWriter $ liftRefReader $ mk w

    return (lookup_ >=> click, flip $ \s -> lookup_ >=> (`put` s), lookup_ >=> get, draw)
  where

    mk :: Layout m -> RefReader m Doc
    mk (Leaf s) = return s
    mk (Node Horiz l) = mapM mk l <&> foldr horiz emptyDoc
    mk (Node Vert l) = mapM mk l <&> foldr vert emptyDoc
    mk (Dyn m) = m >>= mk

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

notebook :: SimpleRefClass m => [(String, Widget m)] -> Widget m
notebook ws = do
    i <- newRef (0 :: Int)
    vertically
        [ horizontally [ button (readRef i <&> \v -> ['*'| v == n] ++ s) $ pure $ Just $ writeRef i n
                       | (n, (s,_)) <- zip [0..] ws]
        , label $ replicate 40 '-'
        , cell (readRef i) $ \i -> snd (ws !! i)
        ]

-- | Click.
button
    :: SimpleRefClass m
    => RefReader m String     -- ^ dynamic label of the button
    -> RefReader m (Maybe (RefWriter m ()))     -- ^ when the @Maybe@ readRef is @Nothing@, the button is inactive
    -> Widget m
button r fm = primButton r (fmap isJust fm) (liftRefReader fm >>= maybe (pure ()) id)

-- | Click which inactivates itself automatically.
smartButton
    :: SimpleRefClass m => RefReader m String     -- ^ dynamic label of the button
    -> EqRef m a              -- ^ underlying reference
    -> (a -> a)   -- ^ The button is active when this function is not identity on readRef of the reference. When the button is pressed, the readRef of the reference is modified with this function.
    -> Widget m
smartButton s r f
    = primButton s (hasEffect r f) (modRef r f)

emptyWidget :: SimpleRefClass m => Widget m
emptyWidget = horizontally []

-- | Text entry.
entry :: SimpleRefClass m => (RefClass r, RefReaderSimple r ~ RefReader m)  => RefSimple r String -> Widget m
entry r = primEntry (const True) r

entryShow :: forall a r m . (Show a, Read a, RefClass r, RefReaderSimple r ~ RefReader m, SimpleRefClass m) => RefSimple r a -> Widget m
entryShow r_ = primEntry isOk r
  where
    r = showLens `lensMap` r_
    isOk s = case (reads s :: [(a, String)]) of
        ((_,""):_) -> True
        _ -> False

showLens :: (Show a, Read a) => Lens' a String
showLens = lens show $ \def s -> maybe def fst $ listToMaybe $ reads s

--------------------------------------------------------------------------------

type B = SimpleRefT ErrorOr

data ErrorOr a
    = Error String
    | Ok a
        deriving (Show)

instance Functor ErrorOr where
    fmap f (Ok a) = Ok (f a)
    fmap f (Error s) = Error s

instance Applicative ErrorOr where
    pure = return
    (<*>) = (. (<&>)) . (>>=)

instance Monad ErrorOr where
    return = Ok
    fail = Error
    Ok a >>= f = f a
    Error e >>= _ = Error e

test :: ErrorOr ()
test = runSimpleRefT $ do
    (click, put, get, draw) <- runWidget Nothing Nothing $ do
        s <- newRef True
        st <- newRef []
        intListEditor (0 :: Int, True) 15 st s
    click 1
    click 3

demo :: Bool -> Bool -> IO (Int -> IO (), Int -> String -> IO (), Int -> IO String, IO ())
demo log autodraw = do
    log' <- if log
          then do
            fd <- openFd "out" WriteOnly Nothing defaultFileFlags
            return $ Just $ void . mapM_ (fdWrite fd . (++ "\n")) . snd
          else return Nothing
    (click, put, get, draw) <- runWidget log' (if autodraw then Just $ mapM_ putStrLn . snd else Nothing) $ do
        s <- newRef True
        st <- newRef []
        intListEditor (0 :: Int, True) 15 st s
    return (click, put, get, draw >>= mapM_ putStrLn . snd)


intListEditor
    :: forall a m
    .  (Read a, Show a, Integral a, SimpleRefClass m)
    => (a, Bool)            -- ^ default element
    -> Int                  -- ^ maximum number of elements
    -> Ref m [(a, Bool)]    -- ^ state reference
    -> Ref m Bool           -- ^ settings reference
    -> Widget m
intListEditor def maxi list_ range = do
    (undo, redo)  <- undoTr ((==) `on` map fst) list_
    notebook
        [ (,) "Editor" $ vertically
            [ horizontally
                [ entryShow len
                , label "items"
                , vertically
                    [ horizontally
                        [ smartButton (pure "AddItem") len (+1)
                        , smartButton (pure "RemoveItem") len (+(-1))
                        , smartButton (fmap (("RemoveAll-" ++) . show) $ readRef len) len $ const 0
                        ]
                    , horizontally
                        [ button (pure "Undo") undo
                        , button (pure "Redo") redo
                        ]
                    ]
                ]
            , horizontally
                [ smartButton (pure "+1")         list $ map $ over _1 (+1)
                , smartButton (pure "-1")         list $ map $ over _1 (+(-1))
                , smartButton (pure "Sort")       list $ sortBy (compare `on` fst)
                ]
            , horizontally
                [ smartButton (pure "SelectAll")  list $ map $ set _2 True
                , smartButton (pure "SelectPos")  list $ map $ \(a,_) -> (a, a>0)
                , smartButton (pure "SelectEven") list $ map $ \(a,_) -> (a, even a)
                , smartButton (pure "InvertSel")  list $ map $ over _2 not
                ]
            , horizontally
                [ smartButton (fmap (("DelSel-" ++) . show . length) sel) list $ filter $ not . snd
                , smartButton (pure "CopySel") safeList $ concatMap $ \(x,b) -> (x,b): [(x,False) | b]
                , smartButton (pure "+1 Sel")     list $ map $ mapSel (+1)
                , smartButton (pure "-1 Sel")     list $ map $ mapSel (+(-1))
                ]
            , horizontally
                [ label "selected sum"
                , dynLabel $ sel <&> show . sum . map fst
                ]
            , listEditor def (map itemEditor [0..]) list_
            ]
        , (,) "Settings" $ horizontally
            [ label "create range"
            , checkbox range
            ]
        ]
 where
    list = toEqRef list_

    itemEditor i r = horizontally
        [ label $ show (i+1) ++ "."
        , entryShow $ _1 `lensMap` r
        , button (readRef r <&> bool "unselect" "select" . snd) $ pure $ Just $ modRef (_2 `lensMap` r) not
        , button (pure "Del")  $ pure $ Just $ modRef list $ \xs -> take i xs ++ drop (i+1) xs
        , button (pure "Copy") $ pure $ Just $ modRef list $ \xs -> take (i+1) xs ++ drop i xs
        ]

    safeList = lens id (const $ take maxi) `lensMap` list

    sel = fmap (filter snd) $ readRef list

    len = joinRef $ readRef range <&> \r -> ll r `lensMap` safeList   -- todo
    ll :: Bool -> Lens' [(a, Bool)] Int
    ll r = lens length extendList where
        extendList xs n = take n $ (reverse . drop 1 . reverse) xs ++
            (uncurry zip . (iterate (+ if r then 1 else 0) *** repeat)) (head $ reverse xs ++ [def])

    mapSel f (x, y) = (if y then f x else x, y)

    (f *** g) (a, b) = (f a, g b)

listEditor :: SimpleRefClass m =>  a -> [Ref m a -> Widget m] -> Ref m [a] -> Widget m
listEditor def (ed: eds) r = do
    q <- extendRef r listLens (False, (def, []))
    cell (fmap fst $ readRef q) $ \b -> case b of
        False -> emptyWidget
        True -> vertically 
            [ ed $ _2 . _1 `lensMap` q
            , listEditor def eds $ _2 . _2 `lensMap` q
            ]

bool a b True = a
bool a b False = b

--------------------------------------------------------------------------------

listLens :: Lens' (Bool, (a, [a])) [a]
listLens = lens get set where
    get (False, _) = []
    get (True, (l, r)) = l: r
    set (_, x) [] = (False, x)
    set _ (l: r) = (True, (l, r))


-- | Undo-redo state transformation.
undoTr
    :: SimpleRefClass m => (a -> a -> Bool)     -- ^ equality on state
    -> Ref m a             -- ^ reference of state
    -> RefCreator m
           ( RefReader m (Maybe (RefWriter m ()))
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

{-
--notebook :: SimpleRefClass m => RefCreatorT m Widget m
notebook_ = runWidget $ do
    buttons <- newRef ("",[])
    let h i b = horizontally
           [ label $ pure b
           , button (pure "Del") $ pure $ Just $ modRef (_2 `lensMap` buttons) $ \l -> take i l ++ drop (i+1) l
           ]
        set (a,xs) x
            | a /= x = ("",x:xs)
            | otherwise = (a,xs)
    vertically
        [ entry $ lens fst set `lensMap` buttons
        , cell (fmap snd $ readRef buttons) $ vertically . zipWith h [0..]    -- cellNoMemo
        ]

-}

