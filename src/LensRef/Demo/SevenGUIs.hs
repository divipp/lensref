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
import qualified Data.Map as Map'
import qualified Data.IntSet as Set
import Control.Applicative (pure, (<*>), (<$>), liftA2)
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Lens.Family2
import Lens.Family2.Stock
import Lens.Family2.Unchecked

import LensRef

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
    horizontally $ do
        label  "Value" $ show <$> readRef r
        button "Count" $ pure $ Just inc

-------------------------------------------------------------------------------- 7guis #1 version 2

counterV2 :: WidgetContext s => RefCreator s ()
counterV2 = counterModel >>= counterView

data Counter s = Counter
    { counterValue :: RefReader s Int
    , incrementCounter :: RefWriter s ()
    }

counterModel :: RefContext s => RefCreator s (Counter s)
counterModel = do
    r <- newRef (0 :: Int)
    return Counter
        { counterValue = readRef r
        , incrementCounter = modRef r (+1)
        }

counterView :: WidgetContext s => Counter s -> RefCreator s ()
counterView c = horizontally $ do
    label  "Value" $ show <$> counterValue c
    button "Count" $ pure $ Just $ incrementCounter c

-------------------------------------------------------------------------------- 7guis #2

type Temperature = Prec2 Double

temperatureConverter :: WidgetContext s => RefCreator s ()
temperatureConverter = do
    -- model
    celsius <- newRef (0 :: Temperature)
    let fahrenheit = multiplying 1.8 . adding 32 `lensMap` celsius
    -- view
    horizontally $ do
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
      True -> label "Notice" $ do
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
            item False "One-way"
            item True  "Return"
        startok <- entryShow "Start" startdate
        endok   <- entryShowActive "End" (readRef isreturn) $ lensMap _2 boolenddate
        button "Book" $ bookaction $ (&&) <$> startok <*> endok

---------- part of the toolkit

maybeLens :: Lens' (Bool, a) (Maybe a)
maybeLens = lens (\(b, a) -> mkMaybe a b)
                 (\(_, a) ma -> maybe (False, a) (\a' -> (True, a')) ma)

mkMaybe :: a -> Bool -> Maybe a
mkMaybe a True  = Just a
mkMaybe _ False = Nothing

-------------------------------------------------------------------------------- 7guis #4

timer :: WidgetContext s => Rational -> RefCreator s ()
timer refresh = do
    -- model
    duration <- newRef 10
    start <- newRef =<< lift currentTime
    timer <- join <$> onChange (readRef start + readRef duration) (mkTimer refresh)
    let elapsed = timer - readRef start
        ratio = per <$> elapsed <*> readRef duration where
            per _ 0 = 1
            per a b = a / b
        reset = writeRef start =<< lift currentTime
    -- view
    vertically $ do
        label "Elapsed (percent)" $ (++"%") . show . (*100) . (^. convert . prec2) <$> ratio
        label "Elapsed" $ (++"s") . show . (^. convert . prec2) <$> elapsed
        void $ entryShow "Duration" $ lensMap (convert . prec2 . nonNegative) duration
        button "Reset" $ pure $ Just reset

---------- part of the toolkit

mkTimer :: WidgetContext s => Delay -> Time -> RefCreator s (RefReader s Time)
mkTimer refresh end = do
    t <- lift currentTime
    if end <= t
      then return $ pure end
      else do
        x <- newRef t
        void $ onChange (readRef x) $ \xt -> when (xt < end) $ asyncDo refresh $ writeRef x =<< lift currentTime
        return $ readRef x


-------------------------------------------------------------------------------- 7guis #5

crud :: WidgetContext s => RefCreator s ()
crud = do
    -- model
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
    -- view
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
    -- model
    mousepos <- newRef (0, 0 :: Prec2 Double)
    circles  <- newRef [((0,2), 1), ((0,0), 2)]
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
        view = maybe id f <$> readRef selected <*> (map ((,) False) <$> readRef circles)  where
            f (i, d) l = insertBy (compare `on` snd . snd) (True, (fst $ snd $ l !! i, d)) $ take i l ++ drop (i+1) l
        commit = readerToWriter view >>= writeRef circles . map snd
    -- view
    horizontally $ do
        button "Undo" undo
        button "Redo" redo
    horizontally $ do
        void $ entryShow "MousePos" mousepos
        button "MouseClick" $ mkMaybe click . not <$> readRef (lensMap _1 sel)
    label "Circles" $ view <&> \l -> unlines [show d ++ " at " ++ show p ++ if s then " filled" else "" | (s, (p, d)) <- l]
    void $ (readRef $ lensMap _1 sel) `switch` \case
      False -> return ()
      True  -> do
        label "Adjust diameter of circle at" $ show . fst <$> ((!!) <$> readRef circles <*> readRef (lensMap (_2 . _1) sel))
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

    label :: String -> RefReader s String -> RefCreator s ()

    primEntry
        :: String
        -> RefReader s Bool     -- ^ active (sensitive)
        -> RefReader s Bool     -- ^ the content is correct
        -> Ref s String
        -> RefCreator s ()

    -- | Label entry.
    entry :: String -> Ref s String -> RefCreator s ()
    entry name = primEntry name (pure True) (pure True)

    entryShow :: (Show a, Read a) => String -> Ref s a -> RefCreator s (RefReader s Bool)
    entryShow name = entryShowActive name (pure True)

    entryShowActive :: (Show a, Read a) => String -> RefReader s Bool -> Ref s a -> RefCreator s (RefReader s Bool)
    entryShowActive name active r = do
        x <- readerToCreator $ readRef r
        v <- extendRef r (lens fst set') (x, Nothing)
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

    -- | Button.
    button
        :: RefReader s String     -- ^ dynamic label of the button
        -> RefReader s (Maybe (RefWriter s ()))     -- ^ when the @Maybe@ readRef is @Nothing@, the button is inactive
        -> RefCreator s ()

    checkbox :: Ref s Bool -> RefCreator s ()

    combobox :: Eq a => Ref s a -> Writer [(a, String)] () -> RefCreator s ()

    listbox :: Eq a => Ref s (Maybe a) -> RefReader s [(a, String)] -> RefCreator s ()

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

item :: MonadWriter [(a, b)] m => a -> b -> m ()
item s m = tell [(s, m)]

-------------------------------------------------------------------------------- API implementation
--------------------------------------------------------------------------------

instance RefContext m => WidgetContext (WContext m) where

    button s fm
        = primButton s (text <$> s) (isJust <$> fm) $ readerToWriter fm >>= fromMaybe (pure ())

    checkbox r = primButton (show <$> readRef r) (text . show <$> readRef r) (pure True) $ modRef r not

    combobox i as = horizontally $ forM_ (execWriter as) $ \(n, s) ->
        primButton (pure s) ((bool (color green) id . (== n) <$> readRef i) <*> pure (text s)) (pure True) $ writeRef i n

    listbox sel as = void $ (null <$> as) `switch` \case
        True  -> return ()
        False -> do
            primButton (fromMaybe "" . fmap snd . listToMaybe <$> as)    -- TODO: should work with head instead of listToMaybe
                       (layout <$> (head <$> as) <*> readRef sel)
                       (pure True)
                       (writeRef sel . Just . fst . head =<< readerToWriter as)
            listbox sel $ drop 1 <$> as    -- TODO: should work with tail instead of drop 1
      where
        layout (a, s) (Just a') | a == a' = color green $ text s
        layout (_, s) _ = text s

    label name r = horizontally $ do
        addLayout $ pure ((), pure $ color magenta $ text name)
        addControl (pure name) (pure [Get $ r <&> text]) $ color bluebackground <$> ((" " `hcomp_`) . (`hcomp_` " ") . text <$> r)

    primEntry name active ok r = horizontally $ do
        addLayout $ pure ((), pure $ color magenta $ text name)
        addControl (pure name) (active <&> \case True -> [Put $ writeRef r, Get $ text <$> readRef r]; False -> [])
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

type RegisterControl s = RefReader s String -> RefReader s [Action s] -> RefReader s Doc -> RefCreator s ()

--------------------------------------------------------------------------------

addControl :: (RefContext m, s ~ WContext m) => RefReader s String -> RefReader s [Action s] -> RefReader s Doc -> RefCreator s ()
addControl name acts layout = do
    f <- lift $ asks addControlDict
    f name acts layout

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

primButton
    :: (RefContext m, s ~ WContext m)
    => RefReader s String     -- ^ dynamic label of the button
    -> RefReader s Doc        -- ^ dynamic label of the button
    -> RefReader s Bool       -- ^ the button is active when this returns @True@
    -> RefWriter s ()         -- ^ the action to do when the button is pressed
    -> RefCreator s ()
primButton name layout vis act
    = addControl name (vis <&> \case True -> [Click act, Get layout]; False -> [])
        $ color <$> (bool grey magenta <$> vis) <*> layout

--------------------------------

run, run'
    :: RefCreator (WContext IO) ()
    -> IO (String -> IO (), String -> String -> IO (), String -> IO (), Delay -> IO ())
run  = runWidget putStr . padding
run' = runWidget (appendFile "out") . padding

runWidget
    :: forall m . RefContext m
    => (String -> m ())
    -> RefCreator (WContext m) ()
    -> m (String -> m (), String -> String -> m (), String -> m (), Delay -> m ())
runWidget out buildwidget = do
    delayedactions <- newSimpleRef mempty
    time           <- newSimpleRef 0
    controlmap     <- newSimpleRef mempty
    controlnames   <- newSimpleRef mempty
    controlcounter <- newSimpleRef 0
    currentview    <- newSimpleRef emptyDoc
    collection     <- newSimpleRef $ pure []

    let addControl name acts layout = do
            i <- lift $ modSimpleRef controlcounter $ state $ \c -> (c, succ c)
            let setControlActions cs = modSimpleRef controlmap $ modify $ case cs of
                    [] -> Map.delete i
                    _ -> Map.insert i cs
                f Unblock = acts
                f _ = pure []
            void $ onChange acts $ lift . setControlActions
            void $ onChangeEqOld name $ \oldname name -> lift $ modSimpleRef controlnames $ modify
                $ Map'.insertWith Set.union name (Set.singleton i)
                . Map'.update (Just . Set.delete i) oldname
            onRegionStatusChange_ $ \msg -> setControlActions <$> f msg
            addLayout $ return $ (,) () $
                hcomp_ <$> layout <*> (pure $ color yellow $ text $ map toSubscript $ show i)

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

        lookup_ :: String -> m [Action (WContext m)]
        lookup_ n = do
            ns <- readSimpleRef controlnames
            i <- case (Map'.lookup n ns, reads n) of
                (Just is, _) | not $ Set.null is -> return $ head $ Set.toList is
                (_, [(i, "")]) -> return i
                _ -> fail "no such control"
            cs <- readSimpleRef controlmap
            maybe (fail "control not registered") pure $ Map.lookup i cs

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

infixl 1 <&>

(<&>) :: Functor f => f a -> (a -> b) -> f b
as <&> f = f <$> as

bool :: a -> a -> Bool -> a
bool a _ True  = a
bool _ b False = b

modSimpleRef :: RefContext m => SimpleRef m a -> StateT a m b -> m b
modSimpleRef r s = do
    a <- readSimpleRef r
    (x, a') <- runStateT s a
    writeSimpleRef r a'
    return x

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
