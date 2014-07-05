{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Demo2 where

import Data.Monoid
import Data.Function
import Data.List
import Data.Maybe
import qualified Data.IntMap as Map
import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import Control.Lens.Simple

import Data.LensRef hiding (readRef, writeRef, lensMap, modRef, joinRef, Ref, RefReader, RefWriter, RefCreator)
import qualified Data.LensRef as Ref

----------------------------

type Base = IO

type Rt = ReaderT St Base

type RefCreator = Ref.RefCreator Rt
type RefReader  = Ref.RefReader Rt
type RefWriter  = Ref.RefWriter Rt

type Ref = Ref.Ref Rt

---------------------------------

class RefClass r where
    readRef  :: r a ->      RefReader a
    writeRef :: r a -> a -> RefWriter ()
    lensMap  :: Lens' a b -> r a -> r b
    joinRef  :: RefReader (r a) -> r a
    toRef :: r a -> Ref a

infixr 8 `lensMap`

r `modRef` f = readerToWriter (readRef r) >>= writeRef r . f

instance RefClass Ref where
    readRef  = Ref.readRef
    writeRef = Ref.writeRef
    lensMap  = Ref.lensMap
    joinRef  = Ref.joinRef
    toRef = id

data EqRef a = EqRef
    { runEqRef :: Ref a
    , changing :: a -> RefReader Bool
    }

instance RefClass EqRef where
    readRef  = readRef  . runEqRef
    writeRef = writeRef . runEqRef
    lensMap k (EqRef r c) = EqRef (lensMap k r) $ \b -> readRef r >>= c . set k b
    joinRef m = EqRef (joinRef $ m <&> runEqRef) $ \a -> m >>= (`changing` a)
    toRef = runEqRef

toEqRef :: Eq a => Ref a -> EqRef a
toEqRef r = EqRef r $ \x -> readRef r <&> (/= x)

-----------------

data St = St
    { newControl        :: Base ControlId
    , setControlActions :: ControlId -> [Action] -> Base ()
    }

type ControlId = Int

data Action
    = Click (RefWriter ())             -- button and checkbox
    | Put   (String -> RefWriter ())   -- entry
    | Get   (RefReader String)         -- entry and dynamic label

--------------------------------------------------------------------------------

type Widget = RefCreator Layout

data Layout
    = Label String
    | Control ControlId Color String
    | Horiz [Layout]
    | Vert  [Layout]
    | Dyn (RefReader Layout)
    | Keret Layout

type Color = Int

render :: Layout -> RefReader [String]
render = fmap snd . f
  where
    f (Label s) = return (length s, [color 35 s])
    f (Control i c s) = return (length n + length s, [color 31 n ++ color c s])
      where n = show i
    f (Horiz l) = mapM f l <&> foldr horiz (0, [])
      where
        horiz (0, _) ys = ys
        horiz (n, xs) (m, ys) = (n + m + 1, zipWith (++) (ext n xs) (map (' ':) $ ext m ys))
          where
            h = max (length xs) (length ys)
            ext n l = take h $ l ++ repeat (replicate n ' ')
    f (Vert l) = mapM f l <&> foldr vert (0, [])
      where
        vert (n, s) (m, t) = (k, map (pad (k-n)) s ++ map (pad (k-m)) t)
          where
            k = max n m
            pad n l = l ++ replicate n ' '
    f (Dyn m) = m >>= f
    f (Keret l) = f l <&> \(n, s) -> (n+2, map ("  " ++) $ replicate n ' ' : s)

    color :: Color -> String -> String
    color (-1) s = s
    color c s = "\x1b[" ++ show c ++ "m" ++ s ++ "\x1b[0m"

--------------------------------------------------------------------------------

ctrl :: [Action] -> RefCreator ControlId
ctrl c = do
    st <- lift ask
    i <- lift $ lift $ newControl st
    lift $ lift $ setControlActions st i c
    onRegionStatusChange $ \msg -> lift $ setControlActions st i $ case msg of
        Unblock -> c
        _ -> []
    return i

label :: String -> Widget
label = pure . Label

keret' :: Widget -> Widget
keret' w = w <&> Keret

dynLabel :: RefReader String -> Widget
dynLabel r = do
    i <- ctrl [Get r]
    return $ Dyn $ r <&> \s -> Control i 44 $ " " ++ s ++ " "

primButton
    :: RefReader String     -- ^ dynamic label of the button
    -> Maybe (RefReader Color)
    -> RefReader Bool       -- ^ the button is active when this returns @True@
    -> RefWriter ()        -- ^ the action to do when the button is pressed
    -> Widget
primButton name col vis act = do
    i <- ctrl [Click act, Get name]
    _ <- onChange vis $ \v -> lift $ do
        f <- asks setControlActions
        lift $ f i $ if v then [Click act, Get name] else []
    return . Dyn $ Control i <$> (fromMaybe (pure 37) col >>= \c -> vis <&> bool c 35) <*> name

primEntry :: (RefClass r) => RefReader Bool -> r String -> Widget
primEntry ok r = do
    i <- ctrl [Put $ writeRef r, Get $ readRef r]
    return $ Dyn $ Control i <$> (ok <&> bool 42 41) <*> (readRef r <&> \s -> " " ++ s ++ " ")

vertically :: [Widget] -> Widget
vertically ws = sequence ws <&> Vert

horizontally :: [Widget] -> Widget
horizontally ws = sequence ws <&> Horiz

cell :: Eq a => RefReader a -> (a -> Widget) -> Widget
cell r f = onChangeMemo r (\v -> f v <&> pure) <&> Dyn

runWidget
    :: Maybe ([String] -> Base ())
    -> Widget
    -> Base (Int -> Base (), Int -> String -> Base (), Int -> Base String, Base [String])
runWidget autodraw cw = do
    controlmap <- newSimpleRef mempty
    counter <- newSimpleRef (0 :: Int)
    let rr :: Rt a -> Base a
        rr = flip runReaderT St
            { newControl = modSimpleRef counter $ state $ \c -> (c, succ c)
            , setControlActions = \i cs -> modSimpleRef controlmap $ modify $ case cs of
                [] -> Map.delete i
                _ -> Map.insert i cs
            }
    rr $ runRefCreator $ \runRefWriter -> do
        w <- cw <&> render

        maybe (pure ()) (\out -> void $ onChangeEq w $ lift . lift . out) autodraw

        let click cs = head $ [rr $ runRefWriter act | Click act <- cs] ++ [fail "not a button or checkbox"]
            put cs s = head $ [rr $ runRefWriter $ act s | Put act <- cs] ++ [fail "not an entry"]
            get cs   = head $ [rr $ runRefWriter $ readerToWriter act | Get act <- cs] ++ [fail "not an entry or label"]

            lookup_ :: Int -> Base [Action]
            lookup_ i = readSimpleRef controlmap >>= maybe (fail "control not registered") pure . Map.lookup i

            draw = rr $ runRefWriter $ readerToWriter w

        return (lookup_ >=> click, flip $ \s -> lookup_ >=> (`put` s), lookup_ >=> get, draw)

--------------------------------------------------------------------------------

checkbox :: Ref Bool -> Widget
checkbox r = primButton (readRef r <&> show) Nothing (pure True) $ modRef r not

notebook :: [(String, Widget)] -> Widget
notebook ws = do
    i <- newRef (0 :: Int)
    vertically
        [ horizontally
            [ primButton (pure s) (Just $ readRef i <&> bool 32 37 . (== n)) (pure True) $ writeRef i n
            | (n, (s,_)) <- zip [0..] ws
            ]
        , keret' $ cell (readRef i) $ \i -> snd (ws !! i)
        ]

-- | Click.
button
    :: RefReader String     -- ^ dynamic label of the button
    -> RefReader (Maybe (RefWriter ()))     -- ^ when the @Maybe@ readRef is @Nothing@, the button is inactive
    -> Widget
button r fm = primButton r Nothing (fmap isJust fm) $ readerToWriter fm >>= fromMaybe (pure ())

-- | Click which inactivates itself automatically.
smartButton
    :: RefReader String     -- ^ dynamic label of the button
    -> EqRef a              -- ^ underlying reference
    -> (a -> a)   -- ^ The button is active when this function is not identity on readRef of the reference. When the button is pressed, the readRef of the reference is modified with this function.
    -> Widget
smartButton s r f
    = primButton s Nothing (readRef r >>= changing r . f) (modRef r f)

emptyWidget :: Widget
emptyWidget = horizontally []

-- | Label entry.
entry :: Ref String -> Widget
entry r = primEntry (pure True) r

entryShow :: (Show a, Read a, RefClass r) => r a -> Widget
entryShow r = do
    x <- readerToCreator $ readRef r
    v <- extendRef (toRef r) (lens fst set') (x, Nothing)
    primEntry (readRef v <&> isNothing . snd) $ lens get set `lensMap` v
  where
    set' t@(v',_) v | show v == show v' = t
    set' _ v = (v, Nothing)

    get (_, Just s) = s
    get (v, _) = show v

    set (v, _) s = case reads s of
        ((x,""):_) -> (x, Nothing)
        _ -> (v, Just s)

--------------------------------------------------------------------------------

demo :: Bool -> IO (Int -> IO (), Int -> String -> IO (), Int -> IO String, IO ())
demo autodraw = do
    (click, put, get, draw) <- runWidget (if autodraw then Just $ mapM_ putStrLn . (++ [[]]) else Nothing) $ do
        s <- newRef True
        st <- newRef []
        keret' $ intListEditor (0, True) 15 st s
    return (click, put, get, draw >>= mapM_ putStrLn)


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
                [ button (pure "Undo") undo
                , button (pure "Redo") redo
                ]
            , horizontally
                [ entryShow len
                , label "items"
                , smartButton (pure "AddItem") len (+1)
                , smartButton (pure "RemoveItem") len (+(-1))
                , smartButton (readRef len <&> \n -> "RemoveAll(" ++ show n ++ ")") len $ const 0
                ]
            , horizontally
                [ smartButton (pure "All+1")      list $ map $ over _1 (+1)
                , smartButton (pure "All-1")      list $ map $ over _1 (+(-1))
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
--notebook :: RefCreator m Widget
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

