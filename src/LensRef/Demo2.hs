{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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
import Lens.Family2
import Lens.Family2.Stock
import Lens.Family2.Unchecked

import LensRef.Context
import LensRef.EqRef

--------------------------------------------------------------------------------

type Widget s = RefCreator s (RefReader s (Int, [String]))

class RefContext s => WidgetContext s where
    registerControl :: RegisterControl s
    asyncWrite      :: AsyncWrite s

type RegisterControl s = RefReader s [Action s] -> RefReader s Color -> RefReader s String -> Widget s

type AsyncWrite s = Rational -> RefWriter s () -> RefCreator s ()

data Action s
    = Click (RefWriter s ())             -- button and checkbox
    | Put   (String -> RefWriter s ())   -- entry
    | Get   (RefReader s String)         -- entry and dynamic label

--------------------------------------------------------------------------------

type Color = Int

color :: Color -> String -> String
color (-1) s = s
color c s = "\x1b[" ++ show c ++ "m" ++ s ++ "\x1b[0m"

--------------------------------------------------------------------------------

data WidgetContextDict m = WidgetContextDict
    { registerControlDict :: RegisterControl (WContext m)
    , asyncWriteDict      :: AsyncWrite (WContext m)
    }

type WContext m = ReaderT (WidgetContextDict m) m

instance RefContext m => WidgetContext (WContext m) where
    registerControl acts col name = do
        f <- lift $ asks registerControlDict
        f acts col name
    asyncWrite d w = do
        f <- lift $ asks asyncWriteDict
        f d w

--run :: IO (Int -> IO (), Int -> String -> IO (), Int -> IO String)
run = runWidget (putStr . unlines) . padding
run' = runWidget (appendFile "out" . unlines) . padding

runWidget
    :: forall m . RefContext m
    => ([String] -> m ())
    -> Widget (WContext m)
    -> m (Int -> m (), Int -> String -> m (), Int -> m (), Rational -> m ())
runWidget out cw = do
    controlmap     <- newSimpleRef mempty
    controlcounter <- newSimpleRef 0
    delayedactions <- newSimpleRef mempty
    currentview    <- newSimpleRef []

    let registerControl acts col name = do
            i <- lift $ modSimpleRef controlcounter $ state $ \c -> (c, succ c)
            let setControlActions cs = modSimpleRef controlmap $ modify $ case cs of
                    [] -> Map.delete i
                    _ -> Map.insert i cs
                f Unblock = acts
                f _ = pure []
            _ <- onChange acts $ lift . setControlActions
            onRegionStatusChange_ $ \msg -> f msg <&> setControlActions
            let n = show i
            return $ do
                c <- col
                s <- name
                return (length n + length s, [color c s ++ color 31 (map toSubscript n)])
        asyncWrite d _ | d < 0 = error "asyncWrite"
        asyncWrite d w = lift $ modSimpleRef delayedactions $ modify $ f d
          where
            f d [] = [(d, w)]
            f d ((d1,w1):as)
                | d < d1    = (d, w): (d1-d,w1): as
                | otherwise = (d1, w1): f (d-d1) as
        st = WidgetContextDict registerControl asyncWrite

    flip runReaderT st $ runRefCreator $ \runRefWriter_ -> do

        w <- cw <&> fmap snd

        _ <- onChangeEq w $ lift . lift . writeSimpleRef currentview

        let runRefWriter :: RefWriter (WContext m) b -> m b
            runRefWriter = flip runReaderT st . runRefWriter_

            click cs = fromMaybe (fail "not a button or checkbox") $ listToMaybe [runRefWriter act | Click act <- cs]
            put cs s = fromMaybe (fail "not an entry")             $ listToMaybe [runRefWriter $ act s | Put act <- cs]
            get cs   = fromMaybe (fail "not an entry or label")    $ listToMaybe [runRefWriter $ readerToWriter act | Get act <- cs]

            lookup_ :: Int -> m [Action (WContext m)]
            lookup_ i = readSimpleRef controlmap >>= maybe (fail "control not registered") pure . Map.lookup i

            drawLast = modSimpleRef currentview (state $ \s -> (s, [])) >>= out

            delay d = do
                as <- lift $ readSimpleRef delayedactions
                case as of
                    [] -> return ()
                    ((d1, w1): as)
                        | d1 <= d -> do
                            lift $ writeSimpleRef delayedactions as
                            w1
                            delay (d-d1)
                        | otherwise ->
                            lift $ writeSimpleRef delayedactions $ (d1-d, w1): as

        lift $ lift $ drawLast
        return
            ( \n -> lookup_ n >>= click >> drawLast
            , \n s -> lookup_ n >>= (`put` s) >> drawLast
            , \n -> (lookup_ n >>= get) >>= out . (:[])
            , \t -> runRefWriter (delay t) >> drawLast
            )

--------------------------------------------------------------------------------

label :: WidgetContext s => String -> Widget s
label s = pure $ pure (length s, [color 35 s])

padding :: WidgetContext s => Widget s -> Widget s
padding w = w <&> \l -> l <&> \(n, s) -> (n+2, map ("  | " ++) $ {- replicate n ' ' : -} s)

dynLabel :: WidgetContext s => RefReader s String -> Widget s
dynLabel r = registerControl (pure [Get r]) (pure 44) (r <&> \s -> " " ++ s ++ " ")

primButton
    :: WidgetContext s
    => RefReader s String     -- ^ dynamic label of the button
    -> Maybe (RefReader s Color)
    -> RefReader s Bool       -- ^ the button is active when this returns @True@
    -> RefWriter s ()        -- ^ the action to do when the button is pressed
    -> Widget s
primButton name col vis act =
    registerControl (vis <&> \v -> if v then [Click act, Get name] else [])
         (fromMaybe (pure 37) col >>= \c -> vis <&> bool c 35)
         name

primEntry :: (RefClass r, WidgetContext s) => RefReader s Bool -> RefReader s Bool -> r s String -> Widget s
primEntry active ok r =
    registerControl (active <&> \v -> if v then [Put $ writeRef r, Get $ readRef r] else [])
         (active >>= bool (ok <&> bool 42 41) (pure 35))
         (readRef r <&> \s -> pad 7 s ++ " ")
  where
    pad n s = replicate (n - length s) ' ' ++ s

vertically :: WidgetContext s => [Widget s] -> Widget s
vertically ws = sequence ws <&> \l -> sequence l <&> foldr vert (0, [])
  where
    vert (n, s) (m, t) = (k, map (pad (k-n)) s ++ map (pad (k-m)) t)
      where
        k = max n m
        pad n l = l ++ replicate n ' '

horizontally :: WidgetContext s => [Widget s] -> Widget s
horizontally ws = sequence ws <&> \l -> sequence l <&> foldr horiz (0, [])
  where
    horiz (0, _) ys = ys
    horiz (n, xs) (m, ys) = (n + m + 1, zipWith (++) (ext n xs) (map (' ':) $ ext m ys))
      where
        h = max (length xs) (length ys)
        ext n l = take h $ l ++ repeat (replicate n ' ')

cell :: (Eq a, WidgetContext s) => RefReader s a -> (a -> Widget s) -> Widget s
cell r f = onChangeMemo r (\v -> f v <&> pure) <&> join

--------------------------------------------------------------------------------

checkbox :: WidgetContext s => Ref s Bool -> Widget s
checkbox r = primButton (readRef r <&> show) Nothing (pure True) $ modRef r not

combobox :: (WidgetContext s, Eq a) => [(String, a)] -> Ref s a -> Widget s
combobox as i = do
    horizontally
        [ primButton (pure s) (Just $ readRef i <&> bool 32 37 . (== n)) (pure True) $ writeRef i n
        | (s, n) <- as
        ]

notebook :: WidgetContext s => [(String, Widget s)] -> Widget s
notebook ws = do
    i <- newRef (0 :: Int)
    vertically
        [ horizontally
            [ primButton (pure s) (Just $ readRef i <&> bool 32 37 . (== n)) (pure True) $ writeRef i n
            | (n, (s,_)) <- zip [0..] ws
            ]
        , padding $ cell (readRef i) $ \i -> snd (ws !! i)
        ]

-- | Button.
button
    :: WidgetContext s
    => RefReader s String     -- ^ dynamic label of the button
    -> RefReader s (Maybe (RefWriter s ()))     -- ^ when the @Maybe@ readRef is @Nothing@, the button is inactive
    -> Widget s
button r fm = primButton r Nothing (fmap isJust fm) $ readerToWriter fm >>= fromMaybe (pure ())

-- | Button which inactivates itself automatically.
smartButton
    :: WidgetContext s
    => RefReader s String     -- ^ dynamic label of the button
    -> EqRef s a              -- ^ underlying reference
    -> (a -> a)   -- ^ The button is active when this function is not identity on readRef of the reference. When the button is pressed, the readRef of the reference is modified with this function.
    -> Widget s
smartButton s r f
    = primButton s Nothing (readRef r >>= changing r . f) (modRef r f)

emptyWidget :: WidgetContext s => Widget s
emptyWidget = horizontally []

-- | Label entry.
entry :: WidgetContext s => Ref s String -> Widget s
entry = primEntry (pure True) (pure True)

entryShow :: (Show a, Read a, RefClass r, WidgetContext s) => RefReader s Bool -> r s a -> Widget s
entryShow a r = entryShow_ a r >>= snd

entryShow_ :: (Show a, Read a, RefClass r, WidgetContext s) => RefReader s Bool -> r s a -> RefCreator s (RefReader s Bool, Widget s)
entryShow_ active r = do
    x <- readerToCreator $ readRef r
    v <- extendRef (toRef r) (lens fst set') (x, Nothing)
    let ok = readRef v <&> isNothing . snd
    return (ok, primEntry active ok $ lens get set `lensMap` v)
  where
    set' t@(v',_) v | show v == show v' = t
    set' _ v = (v, Nothing)

    get (_, Just s) = s
    get (v, _) = show v

    set (v, _) s = case reads s of
        ((x,""):_) -> (x, Nothing)
        _ -> (v, Just s)

--------------------------------------------------------------------------------

counter :: WidgetContext s => Widget s
counter = do
    r <- newRef (0 :: Int)
    horizontally
        [ entryShow (pure True) r
        , button (pure "Count") $ pure $ Just $ modRef r (+1)
        ]

--------------------------------------------------------------------------------

temperatureConverter :: WidgetContext s => Widget s
temperatureConverter = do
    x <- newRef (0 :: Double2)
    horizontally
        [ entryShow (pure True) x
        , label "Celsius = "
        , entryShow (pure True) (celsiusToFahrenheit `lensMap` x)
        , label "Fahrenheit"
        ]

celsiusToFahrenheit :: (Fractional a, Eq a) => Iso' a a
celsiusToFahrenheit = multiplying 1.8 . adding 32

---------------

adding :: Num a => a -> Iso' a a
adding n = iso (+n) (subtract n)

multiplying :: (Fractional a, Eq a) => a -> Iso' a a
multiplying 0 = error "multiplying: factor 0"
multiplying n = iso (*n) (/n)

type Iso' a b = Lens' a b

--------------------------------------------------------------------------------

type Time = Int

booker :: WidgetContext s => Widget s
booker = do
    booked       <- newRef False
    startdate    <- newRef (0 :: Time)
    maybeenddate <- newRef (Nothing :: Maybe Time)
    cell (readRef booked) $ \b -> if b
      then do
        let showbooking i (Just j) = "You have booked a return flight on " ++ show i ++ "-" ++ show j
            showbooking i _        = "You have booked a one-way flight on " ++ show i
        dynLabel $ showbooking <$> readRef startdate <*> readRef maybeenddate
      else do
        boolenddate <- extendRef maybeenddate maybeLens (False, 0)
        let isreturn = lensMap _1 boolenddate
            enddate  = lensMap _2 boolenddate
        (startok, startentry) <- entryShow_ (pure True) startdate
        (endok,   endentry)   <- entryShow_ (readRef isreturn) enddate
        let bookaction _ _        False     = Nothing
            bookaction i (Just j) _ | i > j = Nothing
            bookaction _ _        _         = Just $ writeRef booked True
        vertically
            [ combobox [("one-way flight", False), ("return flight", True)] isreturn
            , startentry
            , endentry
            , button (pure "Book") $ bookaction <$> readRef startdate <*> readRef maybeenddate <*> ((&&) <$> startok <*> endok)
            ]

----------

maybeLens :: Lens' (Bool, a) (Maybe a)
maybeLens = lens (\(b,a) -> if b then Just a else Nothing)
                 (\(_,a) -> maybe (False, a) (\a' -> (True, a')))

--------------------------------------------------------------------------------

fps :: Rational
fps = 50

timer :: WidgetContext s => Widget s
timer = do
    d <- newRef (10.0 :: Double2)
    e <- liftM (lensMap _2) $ extendRef d (lens fst $ \(_, t) d -> (d, min t d) ) (0, 0)
    let ratio = liftM2 (/) (readRef e) (readRef d) <&> min 1 . max 0
    _ <- onChange ratio $ const $ do
        t <- readerToCreator $ readRef e
        duration <- readerToCreator $ readRef d
        when (t < duration) $ asyncWrite (1/fps) $ writeRef e $ min duration $ t + 1/realToFrac fps
    vertically
        [ horizontally
            [ label "Elapsed Time: "
            , dynLabel (ratio <&> (++"%") . show . (*100))
            ]
        , dynLabel $ readRef e <&> (++"s") . show
        , horizontally
            [ label "Duration: "
            , entryShow (pure True) d
            ]
        , button (pure "Reset") $ return $ Just $ writeRef e 0
        ]

--------------------------------------------------------------------------------

crud :: WidgetContext s => Widget s
crud = do
    names <- newRef [("Emil", "Hans"), ("Mustermann", "Max"), ("Tisch", "Roman")]
    psel  <- newRef ("", Nothing)
    let prefix = lensMap (iso fst (\i->(i,Nothing))) psel
    let sel = lensMap _2 psel
    name    <- newRef "John"
    surname <- newRef "Romba"
    let fullname = (,) <$> readRef surname <*> readRef name
    let update s i = modRef names $ \l -> take i l ++ [s] ++ drop (i+1) l
        delete i = do
            modRef names $ \l -> take i l ++ drop (i+1) l
            writeRef sel Nothing
    let filterfun = readRef prefix <&> \p -> filter (isPrefixOf p . fst . snd)
    vertically
        [ horizontally
            [ label "Filter prefix:"
            , entry prefix
            ]
        , listbox sel $ (filterfun <*> (zip [0..] <$> readRef names)) <&> map (\(i, (s, n)) -> (i, s ++ ", " ++ n))
        , horizontally
            [ label "Name:"
            , entry name
            ]
        , horizontally
            [ label "Surname:"
            , entry surname
            ]
        , horizontally
            [ button (pure "Create") $ pure $ Just $ do
                n <- readerToWriter fullname
                modRef names (++ [n])
            , button (pure "Update") $ fmap <$> (update <$> fullname) <*> readRef sel
            , button (pure "Delete") $ fmap delete <$> readRef sel
            ]
        ]

listbox :: (WidgetContext s, Eq a) => Ref s (Maybe a) -> RefReader s [(a, String)] -> Widget s
listbox sel as = do
    cell (as <&> not . null) $ \b -> case b of
        False -> emptyWidget
        True -> vertically
            [ primButton (as <&> snd . head)
                         (Just $ col <$> (as <&> fst . head) <*> readRef sel)
                         (pure True)
                         (writeRef sel . Just . fst . head =<< readerToWriter as)
            , listbox sel (as <&> drop 1)
            ]
    -- TODO: should work with tail instead of drop 1
  where
    col i = maybe 37 (bool 32 37 . (== i))

--------------------------------------------------------------------------------

editor :: WidgetContext s => Widget s
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
    -> Widget s
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
                [ entryShow (pure True) len
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
            , padding $ listEditor def (map itemEditor [0..]) list_
            ]
        , (,) "Settings" $ horizontally
            [ label "create range"
            , checkbox range
            ]
        ]
 where
    list = toEqRef list_

    itemEditor :: Int -> Ref s (Integer, Bool) -> Widget s
    itemEditor i r = horizontally
        [ label $ show (i+1) ++ "."
        , entryShow (pure True) $ _1 `lensMap` r
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

listEditor :: forall s a . WidgetContext s => a -> [Ref s a -> Widget s] -> Ref s [a] -> Widget s
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
    :: RefContext s
    => (a -> a -> Bool)    -- ^ equality on state
    -> Ref s a             -- ^ reference of state
    -> RefCreator s
           ( RefReader s (Maybe (RefWriter s ()))
           , RefReader s (Maybe (RefWriter s ()))
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

--------------------------------------------------------------------------------

newtype Double2 = Double2 Double
    deriving (Eq, Ord, Num, Fractional, Floating, Real, RealFrac, RealFloat)

instance Show Double2 where
    show d = showFFloat (Just 2) d ""
instance Read Double2 where
    readsPrec i = map f . readsPrec i where
        f (a, s) = (Double2 a, s)

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
