#!/home/divip/bin/runhaskell
module Main where

import Text.Pandoc
import Text.Pandoc.JSON
import System.Process
import Data.Maybe
-- from the utf8-string package on HackageDB:
import Data.ByteString.Lazy.UTF8 (fromString)
-- from the SHA package on HackageDB:
import Data.Digest.Pure.SHA
import System.IO
import System.Exit

-- This plugin allows you to include a graphviz "dot" diagram
-- in a document like this:
--
-- ~~~ {.dot name="diagram1"}
-- digraph G {Hello->World}
-- ~~~

transform :: Block -> IO Block
transform (CodeBlock (id, classes, namevals) contents) | "dot" `elem` classes = tr "dot" id namevals contents 
transform (CodeBlock (id, classes, namevals) contents) | "fdp" `elem` classes = tr "fdp" id namevals contents 
transform x = return x

tr dot id namevals contents = do
    let (name, name', file) = case lookup "name" namevals of
            Just fn   -> ([Str fn], fn, fn)
            Nothing   -> ([], "", uniqueName contents)
        infile  = file ++ "." ++ dot
        outfile = file ++ ".pdf"
        size = maybe [] ((:[]) . ("-Gsize="++)) $ lookup "size" namevals
        margin = maybe []  ((:[]) . ("-Gmargin="++)) $ lookup "margin" namevals
    writeFile infile contents
    (Just inh, Just outh, Just errh, ph) <- createProcess
        (proc dot $ ["-Tpdf"] ++ margin ++ size)
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
    return $ Para [Image name (outfile, name')]

-- | Generate a unique filename given the file's contents.
uniqueName :: String -> String
uniqueName = showDigest . sha1 . fromString

main :: IO ()
main = toJSONFilter transform

