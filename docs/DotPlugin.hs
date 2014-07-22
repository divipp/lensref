#!/home/divip/bin/runhaskell
module Main where

import Numeric
import Text.Pandoc
import Text.Pandoc.Shared
import Text.Pandoc.JSON
import System.Process
import Data.Maybe
import Data.List
-- from the utf8-string package on HackageDB:
import Data.ByteString.Lazy.UTF8 (fromString)
-- from the SHA package on HackageDB:
import Data.Digest.Pure.SHA
import GHC.IO.Handle
import System.IO
import System.Exit
-- from package hint
import Language.Haskell.Interpreter

-- This plugin allows you to include a graphviz "dot" diagram
-- in a document like this:
--
-- ~~~ {.dot name="diagram1"}
-- digraph G {Hello->World}
-- ~~~

transform :: Block -> IO [Block]
transform (CodeBlock (id, classes, namevals) contents) | "dot" `elem` classes = tr "dot" id namevals contents 
transform (CodeBlock (id, classes, namevals) contents) | "fdp" `elem` classes = tr "fdp" id namevals contents 
transform (CodeBlock (id, classes, namevals) contents) | "ghci" `elem` classes = ghci id namevals contents 
transform x = return [x]

ghci id namevals contents = do
    let file = case lookup "name" namevals of
            Just fn   -> fn
            Nothing   -> uniqueName contents
        infile  = file ++ ".in"
        outfile = file ++ ".out"
    let (Just modname) = lookup "module" namevals
        cs = lines contents
        format a b = ["> " ++ a, b]
    writeFile infile contents
    writeFile "out" ""
    res <- runInterpreter $ do
        set [searchPath := ["../src"]]
        loadModules [modname]
        setTopLevelModules [modname]
        interpret ("do {" ++ intercalate ";" (concat
                        [["appendFile " ++ show "out" ++ " " ++ show ("> " ++ l ++ "\n"), l] | l <- lines contents]
                    ) ++ "}") (as :: IO ())
    case res of
        Left e -> error $ "ghci plugin: " ++ show e
        Right r -> r
    result <- readFile "out"
    let result' = trans result
    writeFile outfile result'
    return [RawBlock (Format "latex") $ unlines $ begin ++ [result'] ++ end]
  where
    begin = ["\\begin{Shaded}","\\begin{Highlighting}[]"]
    end = ["\\end{Highlighting}","\\end{Shaded}\n"]

trans :: String -> String
trans ('\x1b':'[':cs) = case reads cs :: [(Int, String)] of
    [(col, 'm': cs)] -> trans' col [] cs
trans (c:cs) = c: trans cs
trans [] = []

trans' col acc ('\x1b':'[':'0':'m':cs) = color col (reverse acc) ++ trans cs
trans' col acc (c:cs) = trans' col (c:acc) cs
--trans' [] = []

--color c s = "\x1b[" ++ show c ++ "m" ++ s ++ "\x1b[0m"

color c s = "\\" ++ c' ++ "Tok{" ++ esc s ++ "}"
 {- "\\textcolor[rgb]{" ++ sh r ++ "," ++ sh g ++ "," ++ sh b ++ "}{{" ++ esc s ++ "}}"
  where
    sh r = showFFloat (Just 2) r ""
    (r,g,b) = case c of
        _ -> (0.5,0.5,0.5)
 -}
  where
    c' = case c of
        31  -> "BaseN"    -- bars
        33  -> "Comment"    -- index

        37  -> "DecVal"     -- button
        42  -> "String"     -- entry
        44  -> "Float"      -- dyn label

        32  -> "Char"       -- selected
        35  -> "DataType"   -- not active
        41  -> "Alert"      -- error

        i -> error $ "color " ++ show i
-- Error Alert Comment Keyword
-- Normal RegionMarker Function DataType Other String Char Float DecVal BaseN

esc = escapeStringUsing latexesc
latexesc = backslashEscapes "{}"

tr dot id namevals contents = do
    let (name, name', file) = case lookup "name" namevals of
            Just fn   -> ([Str fn], fn, fn)
            Nothing   -> ([], "", uniqueName contents)
        infile  = file ++ "." ++ dot
        outfile = file ++ ".pdf"
        margin = maybe (0.1 :: Double) read (lookup "margin" namevals)
        size = fmap ((+ margin) . read) (lookup "size" namevals)
        margin' = ["-Gmargin=" ++ show margin]
        size' = maybe [] ((:[]) . ("-Gsize="++) . show) size
    writeFile infile contents
    (Just inh, Just outh, Just errh, ph) <- createProcess
        (proc dot $ ["-Tpdf"] ++ margin' ++ size')
            { std_in  = CreatePipe
            , std_out = CreatePipe
            , std_err = CreatePipe
            }
    hSetBinaryMode outh True
    result <- hGetContents outh
    err <- hGetContents errh
    hPutStr inh contents
    hClose inh
    errc <- waitForProcess ph
    case errc of
        ExitFailure i -> print i
        _ -> return ()
    putStrLn err
    outh' <- openBinaryFile outfile WriteMode
    hPutStr outh' result
    hClose outh'
    return [ RawBlock (Format "latex") "\\begin{centering}"
           , Para [Image name (outfile, name')]
           , RawBlock (Format "latex") "\\end{centering}"
           ]

-- | Generate a unique filename given the file's contents.
uniqueName :: String -> String
uniqueName = showDigest . sha1 . fromString

main :: IO ()
main = toJSONFilter transform

