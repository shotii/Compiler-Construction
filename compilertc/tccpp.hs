module Main where

--import System.IO ( stdin, hGetContents )
import System.Environment ( getArgs)--, getProgName )
import System.Exit ( exitFailure)--, exitSuccess )
--import AbsCPP
import ErrM
import TypeChecker
import ParCPP
--import LexCPP
import CodeGenerator
--import LLVM.General

check :: String -> IO ()
check s = case pProgram (myLexer s) of
	Bad err -> do
		putStrLn "SYNTAX ERROR"
		putStrLn err
		exitFailure
	Ok tree -> case typecheck tree of
		Bad err -> do
			putStrLn "TYPE ERROR"
			putStrLn err
			exitFailure
		Ok ttree -> do
			--putStrLn $ show ttree
			(_,res) <- codeGen ttree
			putStrLn res

main :: IO ()
main = do
	args <- getArgs
	case args of
		[file]	-> readFile file >>= check
		_		-> do
			putStrLn "Usage : prog < SourceFile >"
			exitFailure 
