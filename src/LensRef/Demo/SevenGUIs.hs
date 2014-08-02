{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
module LensRef.Demo.SevenGUIs where

import Numeric (showFFloat)
import Data.String (IsString (..))
import Data.Function (on)
import Data.List (isPrefixOf, insertBy)
import Data.Maybe (fromMaybe, listToMaybe, isJust, isNothing)
import qualified Data.IntMap as Map
import Control.Applicative (pure, (<*>), (<$>), liftA2)
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Lens.Family2
import Lens.Family2.Stock
import Lens.Family2.Unchecked

import LensRef.Context
import LensRef.EqRef

-------------------------------------------------------------------------------- 7guis #1

{- |
Simple counter

Try in ghci:

> (click, put, get, delay) <- run counter
> click 1
> get 0

-}
counter :: WidgetContext s => RefCreator s ()
counter = do
    -- model
    r <- newRef (0 :: Int)
    let inc = modRef r (+1)
    -- view
    dynLabel "Value" $ show <$> readRef r
    button "Count" $ pure $ Just inc

-------------------------------------------------------------------------------- 7guis #2

temperatureConverter :: WidgetContext s => RefCreator s ()
temperatureConverter = do
    -- model
    celsius <- newRef (0 :: Prec2 Double)
    let fahrenheit = multiplying 1.8 . adding 32 `lensMap` celsius
    -- view
    void $ entryShow "Celsius" celsius
    void $ entryShow "Fahrenheit" fahrenheit

--------------- defined in Control.Lens

adding :: Num a => a -> Lens' a a
adding n = iso (+n) (+(-n))

multiplying :: (Fractional a, Eq a) => a -> Lens' a a
multiplying 0 = error "multiplying: factor 0"
multiplying n = iso (*n) (/n)

-------------------------------------------------------------------------------- 7guis #3

type Date = NonNegative Integer

flightBooker :: WidgetContext s => RefCreator s ()
flightBooker = do
    -- model
    booked       <- newRef False
    startdate    <- newRef (0 :: Date)
    maybeenddate <- newRef (Nothing :: Maybe Date)
    -- view
    void $ readRef booked `switch` \case
      True -> dynLabel "Notice" $ do
        start <- readRef startdate
        readRef maybeenddate <&> \case
            Just end -> "You have booked a return flight on " ++ show start ++ "-" ++ show end
            Nothing  -> "You have booked a one-way flight on " ++ show start
      False -> do
        -- view model
        boolenddate  <- extendRef maybeenddate maybeLens (False, 0)
        let isreturn = lensMap _1 boolenddate
            bookaction parseok = do
                ok    <- parseok
                start <- readRef startdate
                end   <- readRef maybeenddate
                return $ (ok && maybe True (start <=) end, writeRef booked True) ^. maybeLens
        -- view view
        combobox isreturn $ do
            item False "one-way flight"
            item True  "return flight"
        startok <- entryShow "Start" startdate
        endok   <- entryShowActive "End" (readRef isreturn) $ lensMap _2 boolenddate
        button "Book" $ bookaction $ (&&) <$> startok <*> endok

---------- part of the toolkit

maybeLens :: Lens' (Bool, a) (Maybe a)
maybeLens = lens (\(b,a) -> if b then Just a else Nothing)
                 (\(_,a) ma -> maybe (False, a) (\a' -> (True, a')) ma)

-------------------------------------------------------------------------------- 7guis #4

timer :: WidgetContext s => RefCreator s ()
timer = do
    -- model
    duration <- newRef 10
    start <- newRef =<< lift currentTime
    timer <- join <$> onChange (readRef start + readRef duration) (mkTimer (1/50))
    let elapsed = timer - readRef start
        ratio = per <$> elapsed <*> readRef duration where
            per _ 0 = 1
            per a b = a / b
        reset = writeRef start =<< lift currentTime
    -- view
    vertically $ do
        dynLabel "Elapsed Time (percent)" $ (++"%") . show . (*100) . (^. convert . prec2) <$> ratio
        dynLabel "Elapsed Time" $ (++"s") . show . (^. convert . prec2) <$> elapsed
        void $ entryShow "Duration" $ lensMap (convert . prec2 . nonNegative) duration
        button "Reset" $ pure $ Just reset

---------- part of the toolkit

mkTimer :: WidgetContext s => Delay -> Time -> RefCreator s (RefReader s Time)
mkTimer refresh end = do
    x <- newRef =<< lift currentTime
    void $ onChange (readRef x) $ \xt -> when (xt < end) $ asyncDo refresh $ writeRef x =<< lift currentTime
    return $ readRef x


-------------------------------------------------------------------------------- 7guis #5

crud :: WidgetContext s => RefCreator s ()
crud = do
    --------- model
    names   <- newRef [("Emil", "Hans"), ("Mustermann", "Max"), ("Tisch", "Roman")]
    name    <- newRef ("Romba", "John")
    prefix  <- newRef ""
    sel     <- onChangeEq_ (readRef prefix) $ const $ return Nothing
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
        entry "Filter prefix" prefix
        listbox sel $ map (\(i, (s, n)) -> (i, s ++ ", " ++ n)) <$> filterednames
        entry "Name" $ lensMap _2 name
        entry "Surname" $ lensMap _1 name
        horizontally $ do
            button "Create" $ pure $ Just create
            button "Update" $ fmap <$> (update <$> readRef name) <*> readRef sel
            button "Delete" $ fmap delete <$> readRef sel


-------------------------------------------------------------------------------- 7guis #6

circleDrawer :: forall s . WidgetContext s => RefCreator s ()
circleDrawer = do
    -------- model
    mousepos <- newRef (0, 0 :: Prec2 Double)
    circles  <- newRef [((0,2), 1), ((2,0), 1), ((0,0), 2)]
    selected <- onChange_ (readRef circles) $ const $ return Nothing
    (undo, redo)  <- undoTr (==) circles
    sel <- extendRef selected maybeLens (False, (0, 1))
    let click = do
            mp <- readerToWriter $ readRef mousepos
            l  <- readerToWriter $ readRef circles
            head $ [ writeRef selected $ Just (i, d)
                   | (i, (p, d)) <- zip [0..] l
                   , distance mp p <= d + 0.01
                   ] ++
                   [ modRef circles $ insertBy (compare `on` snd) (mp, 1) ]
        view = maybe id f <$> readRef selected <*> readRef circles  where
            f (i, d) l = insertBy (compare `on` snd) (fst $ l !! i, d) $ take i l ++ drop (i+1) l
        commit = readerToWriter view >>= writeRef circles
    -------- view
    horizontally $ do
        button "Undo" undo
        button "Redo" redo
    horizontally $ do
        void $ entryShow "MousePos" mousepos
        primButton "MouseClick" (not <$> readRef (lensMap _1 sel)) click
    dynLabel "Circles" $ view <&> \l -> unlines [show p ++ " " ++ show d | (p, d) <- l]
    void $ (readRef $ lensMap _1 sel) `switch` \case
      False -> return ()
      True  -> do
        dynLabel "Adjust diameter of circle at" $ show . fst <$> ((!!) <$> readRef circles <*> readRef (lensMap (_2 . _1) sel))
        horizontally $ do
            void $ entryShow "Diameter" $ lensMap (_2 . _2 . nonNegative) sel
            button "Done" $ pure $ Just commit

distance (x1, y1) (x2, y2)
    = sqrt $ (x2-x1)^2 + (y2-y1)^2

----------- part of the toolkit

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


-------------------------------------------------------------------------------- Widget API
--------------------------------------------------------------------------------

type Time  = Rational   -- seconds elapsed from program start
type Delay = Rational   -- duration in seconds

infix 1 `switch`

type NamedWidgets s = WriterT [(String, RefCreator s ())] (RefCreator s)

class RefContext s => WidgetContext s where

    label    :: String -> RefCreator s ()
    dynLabel :: String -> RefReader s String -> RefCreator s ()

    primEntry
        :: RefClass r
        => String
        -> RefReader s Bool
        -> RefReader s Bool
        -> r s String
        -> RefCreator s ()

    -- | Label entry.
    entry :: String -> Ref s String -> RefCreator s ()
    entry name = primEntry name (pure True) (pure True)

    entryShow :: (Show a, Read a, RefClass r) => String -> r s a -> RefCreator s (RefReader s Bool)
    entryShow name = entryShowActive name (pure True)

    entryShowActive :: (Show a, Read a, RefClass r) => String -> RefReader s Bool -> r s a -> RefCreator s (RefReader s Bool)
    entryShowActive name active r = do
        x <- readerToCreator $ readRef r
        v <- extendRef (toRef r) (lens fst set') (x, Nothing)
        let ok = isNothing . snd <$> readRef v
        primEntry name active ok $ lens get set `lensMap` v
        return ok
      where
        set' t@(v',_) v | show v == show v' = t
        set' _ v = (v, Nothing)

        get (_, Just s) = s
        get (v, _) = show v

        set (v, _) s = case reads s of
            ((x,""):_) -> (x, Nothing)
            _ -> (v, Just s)

    primButton
        :: RefReader s Doc        -- ^ dynamic label of the button
        -> RefReader s Bool       -- ^ the button is active when this returns @True@
        -> RefWriter s ()         -- ^ the action to do when the button is pressed
        -> RefCreator s ()

    -- | Button.
    button
        :: RefReader s String     -- ^ dynamic label of the button
        -> RefReader s (Maybe (RefWriter s ()))     -- ^ when the @Maybe@ readRef is @Nothing@, the button is inactive
        -> RefCreator s ()
    button s fm
        = primButton (text <$> s) (isJust <$> fm) $ readerToWriter fm >>= fromMaybe (pure ())

    -- | Button which inactivates itself automatically.
    smartButton
        :: RefReader s String -- ^ dynamic label of the button
        -> EqRef s a         -- ^ underlying reference
        -> (a -> a)   -- ^ The button is active when this function is not identity on readRef of the reference.
                      --   When the button is pressed the reference is modified with this function.
        -> RefCreator s ()
    smartButton s r f
        = primButton (text <$> s) (readRef r >>= changing r . f) (modRef r f)

    checkbox :: Ref s Bool -> RefCreator s ()
    checkbox r = primButton (text . show <$> readRef r) (pure True) $ modRef r not

    combobox :: Eq a => Ref s a -> Writer [(a, String)] () -> RefCreator s ()
    combobox i as = horizontally $ forM_ (execWriter as) $ \(n, s) ->
        primButton ((bool (color green) id . (== n) <$> readRef i) <*> pure (text s)) (pure True) $ writeRef i n

    listbox :: Eq a => Ref s (Maybe a) -> RefReader s [(a, String)] -> RefCreator s ()
    listbox sel as = void $ (null <$> as) `switch` \case
        True  -> return ()
        False -> do
            primButton (name <$> (head <$> as) <*> readRef sel)
                       (pure True)
                       (writeRef sel . Just . fst . head =<< readerToWriter as)
            listbox sel $ drop 1 <$> as    -- TODO: should work with tail instead of drop 1
      where
        name (a, s) (Just a') | a == a' = color green $ text s
        name (_, s) _ = text s

    padding      :: RefCreator s a -> RefCreator s a
    vertically   :: RefCreator s a -> RefCreator s a
    horizontally :: RefCreator s a -> RefCreator s a

    switch
        :: Eq a
        => RefReader s a
        -> (a -> RefCreator s b)
        -> RefCreator s (RefReader s b)

    asyncDoAt    :: Time -> RefWriter s () -> RefCreator s ()

    asyncDo      :: Delay -> RefWriter s () -> RefCreator s ()
    asyncDo d w = do
        t <- lift currentTime
        asyncDoAt (t + d) w

    currentTime  :: s Time

    notebook :: NamedWidgets s () -> RefCreator s ()
    notebook m = do
        ws <- execWriterT m
        i <- newRef (0 :: Int)
        vertically $ do
            combobox i $ forM_ (zip [0..] ws) $ \(n, (s, _)) -> item n s
            padding $ void $ readRef i `switch` snd . (ws !!)

item :: MonadWriter [(a, b)] m => a -> b -> m ()
item s m = tell [(s, m)]

-------------------------------------------------------------------------------- API implementation
--------------------------------------------------------------------------------

instance RefContext m => WidgetContext (WContext m) where

    label s = addLayout $ pure ((), pure $ color magenta $ text s)

    dynLabel name r = horizontally $ do
        label name
        addControl (pure [Get $ r <&> text]) $ color bluebackground <$> ((" " `hcomp_`) . (`hcomp_` " ") . text <$> r)

    primButton name vis act
        = addControl (vis <&> \case True -> [Click act, Get name]; False -> [])
            $ color <$> (bool grey magenta <$> vis) <*> name

    primEntry name active ok r = horizontally $ do
        label name
        addControl (active <&> \case True -> [Put $ writeRef r, Get $ text <$> readRef r]; False -> [])
            $ color <$> (active >>= bool (bool greenbackground redbackground <$> ok) (pure magenta))
                    <*> (text . pad 7 . (++ " ") <$> readRef r)
      where
        pad n s = replicate (n - length s) ' ' ++ s

    padding w = addLayout $ (,) <$> w <*> (fmap padDoc <$> getLayout)

    vertically ms = addLayout $ (,) <$> ms <*> getLayout

    horizontally ms = addLayout $ (,) <$> ms <*> (fmap (foldr hcomp emptyDoc) <$> collectLayouts)

    switch r f = addLayout $ h <$> onChangeMemo r g
      where
        g v = return <$> ((,) <$> f v <*> getLayout)
        h v = (fst <$> v, join $ snd <$> v)

    asyncDoAt t w = do
        f <- lift $ asks asyncDoAtDict
        f t w

    currentTime = do
        t <- asks time
        readSimpleRef t

getLayout :: (RefContext m, s ~ WContext m) => RefCreator s (RefReader s Doc)
getLayout = fmap (foldr vcomp emptyDoc) <$> collectLayouts


--------------------------------------------------------------------------------

data Action s
    = Click (RefWriter s ())             -- button and checkbox
    | Put   (String -> RefWriter s ())   -- entry
    | Get   (RefReader s Doc)            -- entry and dynamic label

type WContext m = ReaderT (WidgetContextDict m) m

data WidgetContextDict m = WidgetContextDict
    { addControlDict   :: RegisterControl (WContext m)
    , asyncDoAtDict    :: Time -> RefWriter (WContext m) () -> RefCreator (WContext m) ()
    , widgetCollection :: SimpleRef m (RefReader (WContext m) [Doc])
    , time             :: SimpleRef m Time
    }

type RegisterControl s = RefReader s [Action s] -> RefReader s Doc -> RefCreator s ()

--------------------------------------------------------------------------------

addControl :: (RefContext m, s ~ WContext m) => RefReader s [Action s] -> RefReader s Doc -> RefCreator s ()
addControl acts name = do
    f <- lift $ asks addControlDict
    f acts name

addLayout :: (RefContext m, s ~ WContext m) => RefCreator s (a, RefReader s Doc) -> RefCreator s a
addLayout f = do
    c <- lift $ asks widgetCollection
    vs <- lift $ modSimpleRef c $ state $ \s -> (s, pure [])
    (a, v) <- f
    lift $ modSimpleRef c $ modify $ liftA2 (++) $ liftA2 (:) v vs
    return a

collectLayouts :: (RefContext m, s ~ WContext m) => RefCreator s (RefReader s [Doc])
collectLayouts = do
    c <- lift $ asks widgetCollection
    lift $ modSimpleRef c $ state $ \s -> (reverse <$> s, pure [])

--------------------------------

run, run'
    :: RefCreator (WContext IO) ()
    -> IO (Int -> IO (), Int -> String -> IO (), Int -> IO (), Delay -> IO ())
run  = runWidget putStr . padding
run' = runWidget (appendFile "out") . padding

runWidget
    :: forall m . RefContext m
    => (String -> m ())
    -> RefCreator (WContext m) ()
    -> m (Int -> m (), Int -> String -> m (), Int -> m (), Delay -> m ())
runWidget out buildwidget = do
    delayedactions <- newSimpleRef mempty
    time           <- newSimpleRef 0
    controlmap     <- newSimpleRef mempty
    controlcounter <- newSimpleRef 0
    currentview    <- newSimpleRef emptyDoc
    collection     <- newSimpleRef $ pure []

    let addControl acts name = do
            i <- lift $ modSimpleRef controlcounter $ state $ \c -> (c, succ c)
            let setControlActions cs = modSimpleRef controlmap $ modify $ case cs of
                    [] -> Map.delete i
                    _ -> Map.insert i cs
                f Unblock = acts
                f _ = pure []
            void $ onChange acts $ lift . setControlActions
            onRegionStatusChange_ $ \msg -> setControlActions <$> f msg
            addLayout $ return $ (,) () $
                hcomp_ <$> name <*> (pure $ color yellow $ text $ map toSubscript $ show i)

        asyncDoAt t w = lift $ do
            ct <- readSimpleRef time
            if (t < ct)
              then fail "asyncDoAt"
              else modSimpleRef delayedactions $ modify $ insertBy (compare `on` fst) (t, w)

        delay d = do
            ct <- lift $ readSimpleRef time
            timeJump $ ct + d

        timeJump t = do
            lift (readSimpleRef delayedactions) >>= \case
              ((t', w): as) | t' <= t -> do
                lift $ writeSimpleRef delayedactions as
                lift $ writeSimpleRef time t'
                w
                timeJump t
              _ -> lift $ writeSimpleRef time t

        lookup_ :: Int -> m [Action (WContext m)]
        lookup_ i = readSimpleRef controlmap >>= maybe (fail "control not registered") pure . Map.lookup i

        draw = modSimpleRef currentview (state $ \d -> (show d, emptyDoc)) >>= out

        st = WidgetContextDict addControl asyncDoAt collection time

    flip runReaderT st $ runRefCreator $ \runRefWriter_ -> do

        buildwidget
        layout <- getLayout
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
            , \n -> (lookup_ n >>= get) >>= out . show
            , \t -> runRefWriter (delay t) >> draw
            )

-------------------------------------------------------------------------------- Doc data type
--------------------------------------------------------------------------------

data Doc = Doc Int [String] deriving Eq

instance IsString Doc where
    fromString = text

instance Show Doc where
    show (Doc _ ss) = unlines ss

height :: Doc -> Int
height (Doc _ l) = length l

emptyDoc :: Doc
emptyDoc = Doc 0 []

text :: String -> Doc
text = foldr vcomp emptyDoc . map f . lines
  where
    f s = Doc (length s) [s]

color :: Color -> Doc -> Doc
color c (Doc n ss) = Doc n ["\x1b[" ++ show c ++ "m" ++ s ++ "\x1b[0m" | s <- ss]

vcomp :: Doc -> Doc -> Doc
vcomp (Doc n s) (Doc m t) = Doc k $ map (pad (k-n)) s ++ map (pad (k-m)) t
  where
    k = max n m
    pad n l = l ++ replicate n ' '

hcomp :: Doc -> Doc -> Doc
hcomp (Doc 0 _) d2 = d2
hcomp d1 d2 = d1 `hcomp_` (" " `hcomp_` d2)

hcomp_ :: Doc -> Doc -> Doc
hcomp_ (Doc n xs) (Doc m ys) = Doc (n + m) $ zipWith (++) (ext n xs) (ext m ys)
  where
    h = max (length xs) (length ys)
    ext n l = take h $ l ++ repeat (replicate n ' ')

padDoc :: Doc -> Doc
padDoc d = color red (foldr vcomp emptyDoc $ replicate (height d) "  |") `hcomp` d

------------------------------------------

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

-------------------------------------------------------------------------------- Aux
--------------------------------------------------------------------------------

bool a _ True = a
bool _ b False = b

---------------------

newtype Prec2 a = Prec2 { unPrec2 :: a }
    deriving (Eq, Ord, Num, Fractional, Floating, Real, RealFrac, RealFloat)

instance RealFloat a => Show (Prec2 a) where
    show d = showFFloat (Just 2) d ""
instance Read a => Read (Prec2 a) where
    readsPrec i = map f . readsPrec i where
        f (a, s) = (Prec2 a, s)

prec2 :: Lens' a (Prec2 a)
prec2 = iso Prec2 unPrec2

---------------------

newtype NonNegative a = NonNegative { unNonNegative :: a }
    deriving (Eq, Ord, Num, Fractional, Floating, Real, RealFrac, RealFloat)

instance Show a => Show (NonNegative a) where
    show (NonNegative x) = show x
instance (Read a, Ord a, Num a) => Read (NonNegative a) where
    readsPrec i = concatMap f . readsPrec i where
        f (a, s) = [(NonNegative a, s) | a >= 0]

nonNegative :: Lens' a (NonNegative a)
nonNegative = iso NonNegative unNonNegative

---------------------

convert :: (RealFrac a, RealFrac b) => Lens' a b
convert = iso realToFrac realToFrac

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
