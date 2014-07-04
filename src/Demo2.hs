{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Demo2 where

import Data.Function
import Data.List
import Data.Maybe
import Data.Traversable hiding (mapM)
import qualified Data.IntMap as Map
import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Lens.Simple

import Data.LensRef.Common
import qualified Data.LensRef as Ref
import Data.LensRef hiding (readRef, writeRef, lensMap, modRef, joinRef, Ref)

class RefClass r where
    readRef :: r a -> RefReader a
    writeRef :: r a -> a -> RefWriter ()
    lensMap :: Lens' a b -> r a -> r b
    joinRef :: RefReader (r a) -> r a

r `modRef` f = readerToWriter (readRef r) >>= writeRef r . f

infixr 8 `lensMap`

instance RefClass Ref where
    readRef = Ref.readRef
    writeRef = Ref.writeRef
    lensMap = Ref.lensMap
    joinRef = Ref.joinRef

data EqRef a = EqRef
    { runEqRef :: Ref a
    , changing :: a -> RefReader Bool
    }

instance RefClass EqRef where
    readRef = readRef . runEqRef
    writeRef r = writeRef (runEqRef r)
    lensMap k (EqRef r c) = EqRef
        { runEqRef = lensMap k r
        , changing = \b -> readRef r >>= \a -> c $ set k b a
        }
    joinRef m = EqRef
        { runEqRef = joinRef $ m <&> runEqRef
        , changing = \a -> m >>= \(EqRef _ k) -> k a
        }

hasEffect ::
    EqRef a
    -> (a -> a)
    -> RefReader Bool
hasEffect (EqRef r c) f = readRef r >>= c . f

toEqRef :: (Eq a) => Ref a -> EqRef a
toEqRef r = EqRef r $ \x -> readRef r <&> (/= x)



--------------------------------------------------------------------------------

type Base = IO

type Rt = ReaderT St Base

type RefCreator = RefCreatorT (Rt)
type RefReader  = RefReaderT  (Rt)
type RefWriter  = RefWriterT  (Rt)

type Ref = Ref.Ref (Rt)

data St = St
    { newControlId      :: Base ControlId
    , registerControl   :: ControlId -> [Action] -> Base ()
    , unregisterControl :: ControlId -> Base ()
    , logfun            :: Maybe (Doc -> Base ())
    }

type ControlId = Int

data Action
    = Click (RefWriter ())             -- button and checkbox
    | Put   (String -> RefWriter ())   -- entry
    | Get   (RefReader String)         -- entry and dynamic label

type Widget = RefCreator (Layout)

data Layout
    = Leaf Doc
    | Node Dir [Layout]
    | Dyn (RefReader (Layout))
    | Keret (Layout)

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

keret :: Doc -> Doc
keret (n, s) = (n+2, [x] ++ map f s {- ++ [x] -}) where
    x = "  " ++ replicate n ' ' -- ++ "+"
    f s = "  " ++ s -- ++ "|"

--------------------------------------------------------------------------------

dyn :: RefReader (Layout) -> Widget
dyn v = do
    fd <- lift $ asks logfun
    maybe (pure ()) (void . onChangeEq (v >>= mk) . redraw') fd
    return $ Dyn v
  where
    redraw' out ss = lift $ lift $ out ss

    mk :: Layout -> RefReader Doc
    mk (Leaf s) = return s
    mk (Node Horiz l) = mapM mk l <&> foldr horiz emptyDoc
    mk (Node Vert l) = mapM mk l <&> foldr vert emptyDoc
    mk (Dyn m) = m >>= mk --return ["*"]
    mk (Keret l) = mk l <&> keret

ctrl :: [Action] -> RefCreator ControlId
ctrl c = do
    st <- lift ask
    i <- lift $ lift $ newControlId st
    lift $ lift $ registerControl st i c
    onRegionStatusChange $ \msg -> lift $ do
        maybe (pure ()) ($ text (show msg ++ " " ++ show i)) $ logfun st
        case msg of
            Unblock -> registerControl st i c
            _ -> unregisterControl st i
    return i

label :: String -> Widget
label = pure . leaf'

keret' :: Widget -> Widget
keret' w = w <&> Keret

color :: Int -> String -> String
color (-1) s = s
color c s = "\x1b[" ++ show c ++ "m" ++ s ++ "\x1b[0m"

red = color 31

leaf :: Int -> Int -> String -> Layout
leaf c i s = Leaf (length n + length s, [red n ++ color c s])
  where
    n = if i >= 0 then show (i :: Int) else "-"

leaf' s = Leaf (length s, [color 35 s])

dynLabel :: RefReader String -> Widget
dynLabel r = do
    i <- ctrl [Get r]
    dyn $ r <&> \s -> leaf 44 i $ " " ++ s ++ " "

primButton
    :: RefReader String     -- ^ dynamic label of the button
    -> RefReader Bool       -- ^ the button is active when this returns @True@
    -> RefWriter ()        -- ^ the action to do when the button is pressed
    -> Widget
primButton name vis act = dyn . join =<< do
    i <- ctrl [Click act, Get name]
    onChangeMemo vis $ \v -> case v of
        True -> do
            return $ return $ name <&> leaf 37 i
        False -> return $ return $ name <&> leaf 35 i

checkbox :: Ref Bool -> Widget
checkbox r = primButton (readRef r <&> show) (pure True) $ modRef r not

primEntry :: (RefClass r) => (String -> Bool) -> r String -> Widget
primEntry ok r = do
    i <- ctrl [Put $ writeRef r, Get $ readRef r]
    dyn $ readRef r <&> \s -> leaf 42 i $ brack (ok s) $ " " ++ s ++ " "
          where
            brack True s = s
            brack _ s = "{" ++ s ++ "}"

vertically :: [Widget] -> Widget
vertically ws = sequenceA ws <&> Node Vert

horizontally :: [Widget] -> Widget
horizontally ws = sequenceA ws <&> Node Horiz

cell :: Eq a => RefReader a -> (a -> Widget) -> Widget
cell r f = onChangeMemo r (\v -> f v <&> pure) >>= dyn

runWidget
    :: Maybe (Doc -> Base ())
    -> Maybe (Doc -> Base ())
    -> Widget
    -> Base (Int -> Base (), Int -> String -> Base (), Int -> Base String, Base Doc)
runWidget log autodraw cw = do
  controlmap <- newSimpleRef mempty
  counter <- newSimpleRef (0 :: Int)
  let st = St
        { newControlId = modSimpleRef counter $ state $ \c -> (c, succ c)
        , registerControl = \i cs -> modSimpleRef controlmap $ modify $ Map.insert i cs
        , unregisterControl = \i -> modSimpleRef controlmap $ modify $ Map.delete i
        , logfun = log
        }
      rr :: ReaderT (St) Base a -> Base a
      rr = flip runReaderT st
  rr $ runRefCreatorT $ \runRefWriter -> do
    w <- keret' cw

    maybe (pure ()) (\out -> void $ onChangeEq (mk w) $ lift . lift . out) autodraw

    let click cs = head $ [rr $ runRefWriter act | Click act <- cs] ++ [fail "not a button or checkbox"]
        put cs s = head $ [rr $ runRefWriter $ act s | Put act <- cs] ++ [fail "not an entry"]
        get cs   = head $ [rr $ runRefWriter $ readerToWriter act | Get act <- cs] ++ [fail "not an entry or label"]

        lookup_ :: Int -> Base [Action]
        lookup_ i = readSimpleRef controlmap >>= \m -> case Map.lookup i m of
            Just cs -> pure cs
            _ -> fail "control not registered"

        draw = rr $ runRefWriter $ readerToWriter $ mk w

    return (lookup_ >=> click, flip $ \s -> lookup_ >=> (`put` s), lookup_ >=> get, draw)
  where

    mk :: Layout -> RefReader Doc
    mk (Leaf s) = return s
    mk (Node Horiz l) = mapM mk l <&> foldr horiz emptyDoc
    mk (Node Vert l) = mapM mk l <&> foldr vert emptyDoc
    mk (Dyn m) = m >>= mk
    mk (Keret l) = mk l <&> keret

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

notebook :: [(String, Widget)] -> Widget
notebook ws = do
    i <- newRef (0 :: Int)
    vertically
        [ horizontally [ button (readRef i <&> \v -> ['*'| v == n] ++ s) $ pure $ Just $ writeRef i n
                       | (n, (s,_)) <- zip [0..] ws]
        , keret' $ cell (readRef i) $ \i -> snd (ws !! i)
        ]

-- | Click.
button
    :: RefReader String     -- ^ dynamic label of the button
    -> RefReader (Maybe (RefWriter ()))     -- ^ when the @Maybe@ readRef is @Nothing@, the button is inactive
    -> Widget
button r fm = primButton r (fmap isJust fm) (readerToWriter fm >>= maybe (pure ()) id)

-- | Click which inactivates itself automatically.
smartButton
    :: RefReader String     -- ^ dynamic label of the button
    -> EqRef a              -- ^ underlying reference
    -> (a -> a)   -- ^ The button is active when this function is not identity on readRef of the reference. When the button is pressed, the readRef of the reference is modified with this function.
    -> Widget
smartButton s r f
    = primButton s (hasEffect r f) (modRef r f)

emptyWidget :: Widget
emptyWidget = horizontally []

-- | Text entry.
entry :: Ref String -> Widget
entry r = primEntry (const True) r

entryShow :: forall a r. (Show a, Read a, RefClass r) => r a -> Widget
entryShow r_ = primEntry isOk r
  where
    r = showLens `lensMap` r_
    isOk s = case (reads s :: [(a, String)]) of
        ((_,""):_) -> True
        _ -> False

showLens :: (Show a, Read a) => Lens' a String
showLens = lens show $ \def s -> maybe def fst $ listToMaybe $ reads s

--------------------------------------------------------------------------------

demo :: Bool -> Bool -> IO (Int -> IO (), Int -> String -> IO (), Int -> IO String, IO ())
demo log autodraw = do
{-
    log' <- if log
          then do
            fd <- openFd "out" WriteOnly Nothing defaultFileFlags
            return $ Just $ void . mapM_ (fdWrite fd . (++ "\n")) . snd
          else return Nothing
-}
    let log' = Nothing
    (click, put, get, draw) <- runWidget log' (if autodraw then Just $ mapM_ putStrLn . (++ [[]]) . snd else Nothing) $ do
        s <- newRef True
        st <- newRef []
        intListEditor (0, True) 15 st s
    return (click, put, get, draw >>= mapM_ putStrLn . snd)


intListEditor
    :: (Integer, Bool)            -- ^ default element
    -> Int                  -- ^ maximum number of elements
    -> Ref [(Integer, Bool)]    -- ^ state reference
    -> Ref Bool           -- ^ settings reference
    -> Widget
intListEditor def maxi list_ range = do
    (undo, redo)  <- undoTr ((==) `on` map fst) list_
    op <- newRef sum
    notebook
        [ (,) "Editor" $ vertically
            [ horizontally
                [ entryShow len
                , label "items"
                , vertically
                    [ horizontally
                        [ smartButton (pure "AddItem") len (+1)
                        , smartButton (pure "RemoveItem") len (+(-1))
                        , smartButton (readRef len <&> \n -> "RemoveAll(" ++ show n ++ ")") len $ const 0
                        ]
                    , horizontally
                        [ button (pure "Undo") undo
                        , button (pure "Redo") redo
                        ]
                    ]
                ]
            , horizontally
                [ smartButton (pure "All+1")         list $ map $ over _1 (+1)
                , smartButton (pure "All-1")         list $ map $ over _1 (+(-1))
                , smartButton (pure "Sort")       list $ sortBy (compare `on` fst)
                ]
            , horizontally
                [ smartButton (pure "SelectAll")  list $ map $ set _2 True
                , smartButton (pure "SelectPos")  list $ map $ \(a,_) -> (a, a>0)
                , smartButton (pure "SelectEven") list $ map $ \(a,_) -> (a, even a)
                , smartButton (pure "InvertSel")  list $ map $ over _2 not
                ]
            , horizontally
                [ smartButton (sel <&> \s -> "DelSel(" ++ show (length s) ++ ")") list $ filter $ not . snd
                , smartButton (pure "CopySel") safeList $ concatMap $ \(x,b) -> (x,b): [(x,False) | b]
                , smartButton (pure "Sel+1")     list $ map $ mapSel (+1)
                , smartButton (pure "Sel-1")     list $ map $ mapSel (+(-1))
                ]
            , horizontally
                [ dynLabel $ liftA2 ($) (readRef op) (sel <&> map fst) <&> show
                , label "selected sum"
                ]
            , keret' $ listEditor def (map itemEditor [0..]) list_
            ]
        , (,) "Settings" $ horizontally
            [ label "create range"
            , checkbox range
            ]
        ]
 where
    list = toEqRef list_

    itemEditor :: Int -> Ref (Integer, Bool) -> Widget
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
    ll :: Bool -> Lens' [(Integer, Bool)] Int
    ll r = lens length extendList where
        extendList xs n = take n $ (reverse . drop 1 . reverse) xs ++
            (uncurry zip . (iterate (+ if r then 1 else 0) *** repeat)) (head $ reverse xs ++ [def])

    mapSel f (x, y) = (if y then f x else x, y)

    (f *** g) (a, b) = (f a, g b)

listEditor ::  a -> [Ref a -> Widget] -> Ref [a] -> Widget
listEditor _ [] _ = error "not enought editors for listEditor"
listEditor def (ed: eds) r = do
    q <- extendRef r listLens (False, (def, []))
    cell (fmap fst $ readRef q) $ \b -> case b of
        False -> emptyWidget
        True -> vertically 
            [ ed $ _2 . _1 `lensMap` q
            , listEditor def eds $ _2 . _2 `lensMap` q
            ]

bool a _ True = a
bool _ b False = b

--------------------------------------------------------------------------------

listLens :: Lens' (Bool, (a, [a])) [a]
listLens = lens get set where
    get (False, _) = []
    get (True, (l, r)) = l: r
    set (_, x) [] = (False, x)
    set _ (l: r) = (True, (l, r))


-- | Undo-redo state transformation.
undoTr
    :: (a -> a -> Bool)     -- ^ equality on state
    -> Ref a             -- ^ reference of state
    -> RefCreator
           ( RefReader (Maybe (RefWriter ()))
           , RefReader (Maybe (RefWriter ()))
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
--notebook :: RefCreatorT m Widget
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

