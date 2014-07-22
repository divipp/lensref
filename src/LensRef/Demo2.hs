{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module LensRef.Demo2 where

import Numeric
import Data.Monoid
import Data.Function
import Data.List
import Data.Maybe
import qualified Data.IntMap as Map
import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Lens.Family2
import Lens.Family2.Stock
import Lens.Family2.Unchecked

import LensRef.Context
import LensRef.EqRef

--------------------------------------------------------------------------------

counter :: WidgetContext s => RefCreator s ()
counter = do
    -- model
    r <- newRef (0 :: Int)
    let inc = modRef r (+1)
    -- view
    horizontally $ do
        dynLabel $ show <$> readRef r
        button "Count" $ pure $ Just inc

--------------------------------------------------------------------------------

temperatureConverter :: WidgetContext s => RefCreator s ()
temperatureConverter = do
    -- model
    celsius <- newRef (0 :: Double2)
    let fahrenheit = multiplying 1.8 . adding 32 `lensMap` celsius
    -- view
    horizontally $ do
        void $ entryShow (pure True) celsius
        label "Celsius = "
        void $ entryShow (pure True) fahrenheit
        label "Fahrenheit"

---------------

adding :: Num a => a -> Lens' a a
adding n = iso (+n) (subtract n)

multiplying :: (Fractional a, Eq a) => a -> Lens' a a
multiplying 0 = error "multiplying: factor 0"
multiplying n = iso (*n) (/n)

--------------------------------------------------------------------------------

type Time = Int

booker :: WidgetContext s => RefCreator s ()
booker = do
    -- model
    booked       <- newRef False
    startdate    <- newRef (0 :: Time)
    maybeenddate <- newRef (Nothing :: Maybe Time)
    boolenddate  <- extendRef maybeenddate maybeLens (False, 0)
    let isreturn = lensMap _1 boolenddate
        bookaction ok = f <$> readRef startdate <*> readRef maybeenddate <*> ok
          where
            f _ _        False     = Nothing
            f i (Just j) _ | i > j = Nothing
            f _ _        _         = Just $ writeRef booked True
    -- view
    void $ cell (readRef booked) $ \case
      True -> do
        let showbooking i (Just j) = "You have booked a return flight on " ++ show i ++ "-" ++ show j
            showbooking i _        = "You have booked a one-way flight on " ++ show i
        dynLabel $ showbooking <$> readRef startdate <*> readRef maybeenddate
      False -> do
        combobox [("one-way flight", False), ("return flight", True)] isreturn
        startok <- entryShow (pure True) startdate
        endok   <- entryShow (readRef isreturn) $ lensMap _2 boolenddate
        button "Book" $ bookaction $ (&&) <$> startok <*> endok

----------

maybeLens :: Lens' (Bool, a) (Maybe a)
maybeLens = lens (\(b,a) -> if b then Just a else Nothing)
                 (\(_,a) -> maybe (False, a) (\a' -> (True, a')))

--------------------------------------------------------------------------------

fps :: Rational
fps = 50

timer :: WidgetContext s => RefCreator s ()
timer = do
    -- model
    duration <- newRef (10.0 :: Double2)
    elapsed  <- lensMap _2 <$> extendRef duration (lens fst $ \(_, t) d -> (d, min t d)) (0, 0)
    let ratio = min 1 . max 0 <$> ((/) <$> readRef elapsed <*> readRef duration)
        reset = writeRef elapsed 0
    void $ onChange ratio $ const $ do
        t <- readerToCreator $ readRef elapsed
        d <- readerToCreator $ readRef duration
        when (t < d) $ asyncWrite (1/fps) $ writeRef elapsed $ min d $ t + 1/realToFrac fps
    -- view
    vertically $ do
        horizontally $ do
            label "Elapsed Time: "
            dynLabel $ (++"%") . show . (*100) <$> ratio
        dynLabel $ (++"s") . show <$> readRef elapsed
        horizontally $ do
            label "Duration: "
            void $ entryShow (pure True) duration
        button "Reset" $ pure $ Just reset

--------------------------------------------------------------------------------

crud :: WidgetContext s => RefCreator s ()
crud = do
    --------- model
    names   <- newRef [("Emil", "Hans"), ("Mustermann", "Max"), ("Tisch", "Roman")]
    name    <- newRef ("Romba", "John")
    prefix  <- newRef ""
    sel     <- lensMap _1 <$> extendRef prefix (iso snd ((,) Nothing)) (Nothing, "")
    let create = do
            n <- readerToWriter $ readRef name
            modRef names (++ [n])
        update s i =
            modRef names $ \l -> take i l ++ [s] ++ drop (i+1) l
        delete i = do
            writeRef sel Nothing
            modRef names $ \l -> take i l ++ drop (i+1) l
        filterednames
            =   (readRef prefix <&> \p -> filter (isPrefixOf p . fst . snd))
            <*> (zip [0..] <$> readRef names)
    --------- view
    vertically $ do
        horizontally $ label "Filter prefix:" >> entry prefix
        listbox sel $ map (\(i, (s, n)) -> (i, s ++ ", " ++ n)) <$> filterednames
        horizontally $ label "Name:"    >> entry (lensMap _2 name)
        horizontally $ label "Surname:" >> entry (lensMap _1 name)
        horizontally $ do
            button "Create" $ pure $ Just create
            button "Update" $ fmap <$> (update <$> readRef name) <*> readRef sel
            button "Delete" $ fmap delete <$> readRef sel

---------------

listbox :: (WidgetContext s, Eq a) => Ref s (Maybe a) -> RefReader s [(a, String)] -> RefCreator s ()
listbox sel as = void $ cell (null <$> as) $ \case
    True -> return ()
    False -> vertically $ do
        primButton (snd . head <$> as)
                   (Just $ (as <&> \x -> maybe grey (bool green grey . (== fst (head x)))) <*> readRef sel)
                   (pure True)
                   (writeRef sel . Just . fst . head =<< readerToWriter as)
        listbox sel $ drop 1 <$> as    -- TODO: should work with tail instead of drop 1

--------------------------------------------------------------------------------

editor :: WidgetContext s => RefCreator s ()
editor = do
    s <- newRef True
    st <- newRef []
    intListEditor (0, True) 15 st s

intListEditor
    :: forall s
    .  WidgetContext s
    => (Integer, Bool)          -- ^ default element
    -> Int                      -- ^ maximum number of elements
    -> Ref s [(Integer, Bool)]  -- ^ state reference
    -> Ref s Bool               -- ^ settings reference
    -> RefCreator s ()
intListEditor def maxi list_ range = do
    (undo, redo)  <- undoTr ((==) `on` map fst) list_
    op <- newRef sum
    notebook $ do
        nameditem "Editor" $ do
            horizontally $ do
                button "Undo" undo
                button "Redo" redo
            horizontally $ do
                void $ entryShow (pure True) len
                label "items"
                smartButton "AddItem" len (+1)
                smartButton "RemoveItem" len (+(-1))
                smartButton (readRef len <&> \n -> "RemoveAll(" ++ show n ++ ")") len $ const 0
            horizontally $ do
                smartButton "All+1"      list $ map $ over _1 (+1)
                smartButton "All-1"      list $ map $ over _1 (+(-1))
                smartButton "Sort"       list $ sortBy (compare `on` fst)
            horizontally $ do
                smartButton "SelectAll"  list $ map $ set _2 True
                smartButton "SelectPos"  list $ map $ \(a,_) -> (a, a>0)
                smartButton "SelectEven" list $ map $ \(a,_) -> (a, even a)
                smartButton "InvertSel"  list $ map $ over _2 not
            horizontally $ do
                smartButton (sel <&> \s -> "DelSel(" ++ show (length s) ++ ")") list $ filter $ not . snd
                smartButton "CopySel" safeList $ concatMap $ \(x,b) -> (x,b): [(x,False) | b]
                smartButton "Sel+1"     list $ map $ mapSel (+1)
                smartButton "Sel-1"     list $ map $ mapSel (+(-1))
            horizontally $ do
                dynLabel $ show <$> (readRef op <*> (map fst <$> sel))
                label "selected sum"
            padding $ listEditor def (map itemEditor [0..]) list_
        nameditem "Settings" $ horizontally $ do
            label "create range"
            checkbox range
 where
    list = toEqRef list_

    itemEditor :: Int -> Ref s (Integer, Bool) -> RefCreator s ()
    itemEditor i r = horizontally $ do
        label $ show (i+1) ++ "."
        void $ entryShow (pure True) $ _1 `lensMap` r
        button (bool "unselect" "select" . snd <$> readRef r) $ pure $ Just $ modRef (_2 `lensMap` r) not
        button "Del"  $ pure $ Just $ modRef list $ \xs -> take i xs ++ drop (i+1) xs
        button "Copy" $ pure $ Just $ modRef list $ \xs -> take (i+1) xs ++ drop i xs

    safeList = lens id (const $ take maxi) `lensMap` list

    sel = filter snd <$> readRef list

    len = joinRef $ readRef range <&> \r -> ll r `lensMap` safeList   -- todo
    ll :: Bool -> Lens' [(Integer, Bool)] Int
    ll r = lens length extendList where
        extendList xs n = take n $ (reverse . drop 1 . reverse) xs ++
            (uncurry zip . (iterate (+ if r then 1 else 0) *** repeat)) (head $ reverse xs ++ [def])

    mapSel f (x, y) = (if y then f x else x, y)

    (f *** g) (a, b) = (f a, g b)

-----------

listEditor :: WidgetContext s => a -> [Ref s a -> RefCreator s ()] -> Ref s [a] -> RefCreator s ()
listEditor _ [] _ = error "not enought editors for listEditor"
listEditor def (ed: eds) r = do
    q <- extendRef r listLens (False, (def, []))
    void $ cell (fst <$> readRef q) $ \case
        False -> return ()
        True -> vertically $ do
            ed $ _2 . _1 `lensMap` q
            listEditor def eds $ _2 . _2 `lensMap` q

listLens :: Lens' (Bool, (a, [a])) [a]
listLens = lens get set where
    get (False, _) = []
    get (True, (l, r)) = l: r
    set (_, x) [] = (False, x)
    set _ (l: r) = (True, (l, r))

-- | Undo-redo state transformation.
undoTr
    :: RefContext s
    => (a -> a -> Bool)    -- ^ equality on state
    -> Ref s a             -- ^ reference of state
    -> RefCreator s
           ( RefReader s (Maybe (RefWriter s ()))
           , RefReader s (Maybe (RefWriter s ()))
           )  -- ^ undo and redo actions
undoTr eq r = do
    ku <- extendRef r (undoLens eq) ([], [])
    let try f = fmap (writeRef ku) . f <$> readRef ku
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


--------------------------------------------------------------------------------

checkbox :: WidgetContext s => Ref s Bool -> RefCreator s ()
checkbox r = primButton (show <$> readRef r) Nothing (pure True) $ modRef r not

combobox :: (WidgetContext s, Eq a) => [(String, a)] -> Ref s a -> RefCreator s ()
combobox as i = horizontally $ sequence_
    [ primButton (pure s) (Just $ bool green grey . (== n) <$> readRef i) (pure True) $ writeRef i n
    | (s, n) <- as
    ]

-- | Button.
button
    :: WidgetContext s
    => RefReader s String     -- ^ dynamic label of the button
    -> RefReader s (Maybe (RefWriter s ()))     -- ^ when the @Maybe@ readRef is @Nothing@, the button is inactive
    -> RefCreator s ()
button r fm
    = primButton r Nothing (fmap isJust fm) $ readerToWriter fm >>= fromMaybe (pure ())

-- | Button which inactivates itself automatically.
smartButton
    :: WidgetContext s
    => RefReader s String     -- ^ dynamic label of the button
    -> EqRef s a              -- ^ underlying reference
    -> (a -> a)   -- ^ The button is active when this function is not identity on readRef of the reference. When the button is pressed, the readRef of the reference is modified with this function.
    -> RefCreator s ()
smartButton s r f
    = primButton s Nothing (readRef r >>= changing r . f) (modRef r f)

-- | Label entry.
entry :: WidgetContext s => Ref s String -> RefCreator s ()
entry = primEntry (pure True) (pure True)

entryShow :: (Show a, Read a, RefClass r, WidgetContext s) => RefReader s Bool -> r s a -> RefCreator s (RefReader s Bool)
entryShow active r = do
    x <- readerToCreator $ readRef r
    v <- extendRef (toRef r) (lens fst set') (x, Nothing)
    let ok = isNothing . snd <$> readRef v
    primEntry active ok $ lens get set `lensMap` v
    return ok
  where
    set' t@(v',_) v | show v == show v' = t
    set' _ v = (v, Nothing)

    get (_, Just s) = s
    get (v, _) = show v

    set (v, _) s = case reads s of
        ((x,""):_) -> (x, Nothing)
        _ -> (v, Just s)

type NamedWidgets s = WriterT [(String, RefCreator s ())] (RefCreator s) ()

notebook :: WidgetContext s => NamedWidgets s -> RefCreator s ()
notebook m = do
    ws <- execWriterT m
    i <- newRef (0 :: Int)
    vertically $ do
        horizontally $ sequence_
            [ primButton (pure s) (Just $ bool green grey . (== n) <$> readRef i) (pure True) $ writeRef i n
            | (n, (s,_)) <- zip [0..] ws
            ]
        padding $ void $ cell (readRef i) $ \i -> snd (ws !! i)

nameditem :: WidgetContext s => String -> RefCreator s () -> NamedWidgets s
nameditem s m = tell [(s, vertically m)]


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

class RefContext s => WidgetContext s where
    addLayout      :: RefCreator s (a, Layout s) -> RefCreator s a
    collectLayouts :: RefCreator s [Layout s]
    addControl     :: RefReader s [Action s] -> RefReader s Color -> RefReader s String -> RefCreator s ()
    asyncWrite     :: Rational -> RefWriter s () -> RefCreator s ()

type Layout s = RefReader s Doc

type Doc = (Int, [String])

data Action s
    = Click (RefWriter s ())             -- button and checkbox
    | Put   (String -> RefWriter s ())   -- entry
    | Get   (RefReader s String)         -- entry and dynamic label

--------------------------------------------------------------------------------

label :: WidgetContext s => String -> RefCreator s ()
label s = addLayout $ pure ((), pure (length s, [color magenta s]))

padding :: WidgetContext s => RefCreator s a -> RefCreator s a
padding w = addLayout $ (,) <$> w <*> (fmap (\(n, s) -> (n+4, map (color red "  | " ++) s)) <$> getLayout)

dynLabel :: WidgetContext s => RefReader s String -> RefCreator s ()
dynLabel r = addControl (pure [Get r]) (pure bluebackground) $ (" " ++) . (++ " ") <$> r

primButton
    :: WidgetContext s
    => RefReader s String     -- ^ dynamic label of the button
    -> Maybe (RefReader s Color)
    -> RefReader s Bool       -- ^ the button is active when this returns @True@
    -> RefWriter s ()        -- ^ the action to do when the button is pressed
    -> RefCreator s ()
primButton name col vis act =
    addControl (vis <&> \case True -> [Click act, Get name]; False -> [])
         (fromMaybe (pure grey) col >>= \c -> bool c magenta <$> vis)
         name

primEntry :: (RefClass r, WidgetContext s) => RefReader s Bool -> RefReader s Bool -> r s String -> RefCreator s ()
primEntry active ok r =
    addControl (active <&> \case True -> [Put $ writeRef r, Get $ readRef r]; False -> [])
         (active >>= bool (bool greenbackground redbackground <$> ok) (pure magenta))
         (pad 7 . (++ " ") <$> readRef r)
  where
    pad n s = replicate (n - length s) ' ' ++ s

vertically :: WidgetContext s => RefCreator s a -> RefCreator s a
vertically ms = addLayout $ (,) <$> ms <*> getLayout

getLayout :: WidgetContext s => RefCreator s (Layout s)
getLayout = vert_ <$> collectLayouts
  where
    vert_ l = foldr vert (0, []) <$> sequence l
      where
        vert (n, s) (m, t) = (k, map (pad (k-n)) s ++ map (pad (k-m)) t)
          where
            k = max n m
            pad n l = l ++ replicate n ' '

horizontally :: WidgetContext s => RefCreator s a -> RefCreator s a
horizontally ms = addLayout $ (,) <$> ms <*> (horiz_ <$> collectLayouts)
  where
    horiz_ l = foldr horiz (0, []) <$> sequence l
      where
        horiz (0, _) ys = ys
        horiz (n, xs) (m, ys) = (n + m + 1, zipWith (++) (ext n xs) (map (' ':) $ ext m ys))
          where
            h = max (length xs) (length ys)
            ext n l = take h $ l ++ repeat (replicate n ' ')

cell :: (Eq a, WidgetContext s) => RefReader s a -> (a -> RefCreator s b) -> RefCreator s (RefReader s b)
cell r f = addLayout $ h <$> onChangeMemo r g
  where
    g v = return <$> ((,) <$> f v <*> getLayout)
    h v = (fst <$> v, join $ snd <$> v)


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

type WContext m = ReaderT (WidgetContextDict m) m

data WidgetContextDict m = WidgetContextDict
    { addControlDict   :: RegisterControl (WContext m)
    , asyncWriteDict   :: Rational -> RefWriter (WContext m) () -> RefCreator (WContext m) ()
    , widgetCollection :: SimpleRef m [Layout (WContext m)]
    }

type RegisterControl s = RefReader s [Action s] -> RefReader s Color -> RefReader s String -> RefCreator s ()

instance RefContext m => WidgetContext (WContext m) where
    addControl acts col name = do
        f <- lift $ asks addControlDict
        f acts col name
    asyncWrite d w = do
        f <- lift $ asks asyncWriteDict
        f d w
    addLayout f = do
        c <- lift $ asks widgetCollection
        vs <- lift $ modSimpleRef c $ state $ \s -> (s, [])
        (a, v) <- f
        lift $ modSimpleRef c $ modify $ (++ v: vs)
        return a
    collectLayouts = do
        c <- lift $ asks widgetCollection
        lift $ modSimpleRef c $ state $ \s -> (reverse s, [])

--run :: IO (Int -> IO (), Int -> String -> IO (), Int -> IO String)
run = runWidget (putStr . unlines) . padding
run' = runWidget (appendFile "out" . unlines) . padding

runWidget
    :: forall m . RefContext m
    => ([String] -> m ())
    -> RefCreator (WContext m) ()
    -> m (Int -> m (), Int -> String -> m (), Int -> m (), Rational -> m ())
runWidget out buildwidget = do
    controlmap     <- newSimpleRef mempty
    controlcounter <- newSimpleRef 0
    delayedactions <- newSimpleRef mempty
    currentview    <- newSimpleRef mempty
    collection     <- newSimpleRef mempty

    let addControl acts col name = do
            i <- lift $ modSimpleRef controlcounter $ state $ \c -> (c, succ c)
            let setControlActions cs = modSimpleRef controlmap $ modify $ case cs of
                    [] -> Map.delete i
                    _ -> Map.insert i cs
                f Unblock = acts
                f _ = pure []
            void $ onChange acts $ lift . setControlActions
            onRegionStatusChange_ $ \msg -> setControlActions <$> f msg
            let n = show i
            addLayout $ return $ (,) () $ do
                c <- col
                s <- name
                return (length n + length s, [color c s ++ color yellow (map toSubscript n)])
        asyncWrite d _ | d < 0 = error "asyncWrite"
        asyncWrite d w = lift $ modSimpleRef delayedactions $ modify $ f d
          where
            f d [] = [(d, w)]
            f d ((d1,w1):as)
                | d < d1    = (d, w): (d1-d,w1): as
                | otherwise = (d1, w1): f (d-d1) as
        st = WidgetContextDict addControl asyncWrite collection

        delay d = lift (readSimpleRef delayedactions) >>= \case
            [] -> return ()
            ((d1, w1): as)
                | d1 <= d -> do
                    lift $ writeSimpleRef delayedactions as
                    w1
                    delay (d-d1)
                | otherwise ->
                    lift $ writeSimpleRef delayedactions $ (d1-d, w1): as

        lookup_ :: Int -> m [Action (WContext m)]
        lookup_ i = readSimpleRef controlmap >>= maybe (fail "control not registered") pure . Map.lookup i

        draw = modSimpleRef currentview (state $ \s -> (s, [])) >>= out

    flip runReaderT st $ runRefCreator $ \runRefWriter_ -> do

        buildwidget
        layout <- fmap snd <$> getLayout
        void $ onChangeEq layout $ lift . writeSimpleRef currentview
        lift $ lift draw

        let runRefWriter :: RefWriter (WContext m) b -> m b
            runRefWriter = flip runReaderT st . runRefWriter_

            click cs = fromMaybe (fail "not a button or checkbox") $ listToMaybe [runRefWriter act | Click act <- cs]
            put cs s = fromMaybe (fail "not an entry")             $ listToMaybe [runRefWriter $ act s | Put act <- cs]
            get cs   = fromMaybe (fail "not an entry or label")    $ listToMaybe [runRefWriter $ readerToWriter act | Get act <- cs]

        return
            ( \n -> lookup_ n >>= click >> draw
            , \n s -> lookup_ n >>= (`put` s) >> draw
            , \n -> (lookup_ n >>= get) >>= out . (:[])
            , \t -> runRefWriter (delay t) >> draw
            )


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

type Color = Int

red, green, magenta, grey, redbackground, greenbackground, bluebackground :: Color
red     = 31
green   = 32
yellow  = 33
magenta = 35
grey    = 37
redbackground   = 41
greenbackground = 42
bluebackground  = 44

color :: Color -> String -> String
color (-1) s = s
color c s = "\x1b[" ++ show c ++ "m" ++ s ++ "\x1b[0m"

---------------------

bool a _ True = a
bool _ b False = b

---------------------

newtype Double2 = Double2 Double
    deriving (Eq, Ord, Num, Fractional, Floating, Real, RealFrac, RealFloat)

instance Show Double2 where
    show d = showFFloat (Just 2) d ""
instance Read Double2 where
    readsPrec i = map f . readsPrec i where
        f (a, s) = (Double2 a, s)

---------------------

toSubscript '0' = '₀'
toSubscript '1' = '₁'
toSubscript '2' = '₂'
toSubscript '3' = '₃'
toSubscript '4' = '₄'
toSubscript '5' = '₅'
toSubscript '6' = '₆'
toSubscript '7' = '₇'
toSubscript '8' = '₈'
toSubscript '9' = '₉'
toSubscript _ = error "toSubscript"
