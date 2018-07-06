module Main where

import           Input

import qualified Data.Text.IO as T
import           System.Environment (getArgs,getProgName)
import           System.Exit (exitFailure)
import           System.IO (hPutStrLn,stderr)


main :: IO ()
main  =
  do args <- getArgs
     case args of
       [domFile,probFile] ->
         do mbDom <- fmap parseDomain (T.readFile domFile)
            dom <- case mbDom of
                     Left err  -> die err
                     Right dom -> return dom

            mbProb <- fmap parseProblem (T.readFile probFile)
            prob <- case mbProb of
                      Left err   -> die err
                      Right prob -> return prob

            let prob' = groundProblem prob { probDomain = dom }
            T.putStrLn (render prob' { probDomain = probDomain prob })
            putStrLn ""
            T.putStrLn (render (probDomain prob'))

       _ ->
         do progName <- getProgName
            die ("Usage: " ++ progName ++ " <domain.pddl> <problem.pddl>")

die :: String -> IO a
die msg =
  do hPutStrLn stderr msg
     exitFailure
