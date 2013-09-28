module Main where

import ErrM
import System.IO
import System.IO.Error hiding (try)
import Control.Exception

import Lexwc_gram
import Parwc_gram
import Abswc_gram
import Interpreter
  
--import qualified Data.Map as M
--import qualified Data.Set as Set
import Control.Monad
import Data.STRef
import Data.List
import Control.Monad.ST
import System.Environment

data InterpretMode = Interactive | File
    deriving (Eq)

main :: IO()
main = do
    args <- getArgs
    env <- nullEnv
    if null args 
        then interpretProgram "C-like>>> " env stdin (return "") Interactive
        else do
            handle <- openFile (head args) ReadMode
            interpretProgram "" env handle (return "") File
  
interpretProgram :: String -> Env -> Handle -> IO String -> InterpretMode -> IO ()  
interpretProgram prompt env handle instPart mode = do
    if mode == Interactive
        then putStr prompt >> hFlush stdout
        else return()
    input <- try (hGetLine handle)
    case input of
        Left e -> 
            if isEOFError e
                then return ()
                else ioError e
        Right "exit" -> return ()
        Right inpStr -> do
            --act = (instPart >>= (\s -> if s == "" then return (inpStr) else return (s ++ "\n" ++ inpStr)))
                currInst <- (instPart >>= (\s -> if s == "" then return (inpStr) else return (s ++ "\n" ++ inpStr)))
                case pListInstruction (myLexer currInst) of
                    Ok rule -> do
                            -- wczytalem poprawna leksykograficznie instrukcje
                            lastResult <- interpret rule env True
                            interpretProgram "C-like>>> " env handle (return "") mode
                    Bad s -> if isInfixOf "line" s
                                then do 
                                    -- blad leksykograficzny
                                    putStrLn s
                                    interpretProgram "C-like>>> " env handle (return "") mode
                                -- niepelna instrukcja, wczytuje dalej
                                else interpretProgram "... "env handle (return currInst)  mode
