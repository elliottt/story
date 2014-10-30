{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}

module FF.Input where

import qualified Data.Attoparsec.ByteString as A
import qualified Data.AttoLisp as L
import qualified Data.ByteString as S
import qualified Data.Map.Strict as Map
import qualified Data.Text as T


data Term = TVar  !T.Text
          | TCon  !T.Text
          | TPred !T.Text [Term]
            deriving (Show)

data Problem = Problem { pName   :: !T.Text
                       , pDomain :: !T.Text
                       , pInits  :: [Term]
                       , pGoal   :: !Term
                       } deriving (Show)

data Domain = Domain { dName    :: !T.Text
                     , dTypes   :: [Typed [T.Text]]
                     , dActions :: [Action]
                     } deriving (Show)

data Typed a = Typed { tVal  :: a
                     , tType :: !T.Text
                     } deriving (Show)

data Action = Action { aName   :: !T.Text
                     , aParams :: [Typed [T.Text]]
                     , aPre    :: Term
                     , aEff    :: Term
                     } deriving (Show)


-- Parsing ---------------------------------------------------------------------

parseLisp :: L.FromLisp a => S.ByteString -> L.Result a
parseLisp inp =
  case A.parseOnly L.lisp inp of
    Right lisp -> L.fromLisp lisp
    Left err   -> fail err

type NamedArgs = Map.Map T.Text [L.Lisp]

pairArgs :: [L.Lisp] -> L.Parser NamedArgs
pairArgs  = go Map.empty
  where
  go !args (a:as)
    | L.List [ L.Symbol key, val ] <- a =
      go (Map.insertWith (++) key [val] args) as

    | L.List (L.Symbol key : vals) <- a =
      go (Map.insertWith (++) key [L.List vals] args) as

    | otherwise =
      L.typeMismatch "key/value pair" a

  go !args [] =
      return args

listArgs :: [L.Lisp] -> L.Parser NamedArgs
listArgs  = go Map.empty
  where
  go !args (key:val:as)
    | L.Symbol s   <- key
    , Just (':',_) <- T.uncons s =
      go (Map.insertWith (++) s [val] args) as

  go !args [] =
      return args

  go _ ls =
      fail "Invalid argument list"

namedArg :: L.FromLisp a => T.Text -> NamedArgs -> L.Parser a
namedArg n args =
  case Map.lookup n args of
    Just [l] -> L.parseLisp l
    _        -> fail ("Argument: " ++ T.unpack n ++ " not present")

namedArgs :: L.FromLisp a => T.Text -> NamedArgs -> L.Parser [a]
namedArgs n args =
  case Map.lookup n args of
    Just ls -> mapM L.parseLisp ls
    _       -> fail ("Argument: " ++ T.unpack n ++ " not present")

namedArgDefault :: L.FromLisp a => T.Text -> a -> NamedArgs -> L.Parser a
namedArgDefault n def args =
  case Map.lookup n args of
    Just [l] -> L.parseLisp l
    _        -> return def


instance L.FromLisp Domain where
  parseLisp (L.List (L.Symbol "define":ls)) =
    do args           <- pairArgs ls
       L.Symbol dName <- namedArg  "domain"  args
       L.List types   <- namedArg  ":types"  args
       dTypes         <- parseParams types
       dActions       <- namedArgs ":action" args
       return Domain { .. } 

instance L.ToLisp Domain where
  toLisp Domain { .. } =
    L.List $ L.Symbol "define"
           : pair "domain" (L.Symbol dName)
           : pair ":types" (L.List (concatMap (typedLisp (map L.Symbol)) dTypes))
           : map L.toLisp dActions
      where
      pair n l = L.List [ L.Symbol n, l ]

typedLisp :: (a -> [L.Lisp]) -> Typed a -> [L.Lisp]
typedLisp lispArg Typed { .. } =
  lispArg tVal ++ [L.Symbol "-", L.Symbol tType]

instance L.FromLisp Action where
  parseLisp (L.List (L.Symbol aName:ls)) =
    do args          <- listArgs ls
       L.List params <- namedArg ":parameters"   args
       aParams       <- parseParams params
       aPre          <- namedArg ":precondition" args
       aEff          <- namedArg ":effect"       args
       return Action { .. }

instance L.ToLisp Action where
  toLisp Action { .. } =
    L.List [ L.Symbol ":action"
           , L.Symbol aName
           , L.Symbol ":parameters"
           , L.List (concatMap (typedLisp (map mkVar)) aParams)
           , L.Symbol ":precondition"
           , L.toLisp aPre
           , L.Symbol ":effect"
           , L.toLisp aEff
           ]
    where
    mkVar str = L.Symbol (T.cons '?' str)

parseParams :: [L.Lisp] -> L.Parser [Typed [T.Text]]
parseParams  = vars [] []
  where
  err = fail "invalid argument list"

  vars acc vs (L.Symbol s:ls) =
    case T.uncons s of
      Just ('?',n) -> vars acc (n:vs) ls
      Just ('-',_) -> ty acc (reverse vs) ls
      Just _       -> vars acc (s:vs) ls
      _            -> err

  vars acc [] [] = return (reverse acc)
  vars []  vs [] = return [Typed (reverse vs) "object"]
  vars _   _  [] = err

  ty acc vs (L.Symbol s:ls) =
       vars (Typed vs s : acc) [] ls


instance L.FromLisp Problem where
  parseLisp (L.List (L.Symbol "define":ls)) =
    do args             <- pairArgs ls
       L.Symbol pName   <- namedArg "problem" args
       L.Symbol pDomain <- namedArg ":domain" args
       pInits           <- namedArg ":inits"  args
       pGoal            <- namedArg ":goal"   args
       return Problem { .. }

  parseLisp l =
       L.typeMismatch "Problem" l

instance L.ToLisp Problem where
  toLisp Problem { .. } =
    L.List [ L.Symbol "define"
           , pair "problem" (L.Symbol pName)
           , pair ":domain" (L.Symbol pDomain)
           , pair ":inits"  (L.toLisp pInits)
           , pair ":goal"   (L.toLisp pGoal)
           ]
    where
    pair n l = L.List [ L.Symbol n, l ]


instance L.FromLisp Term where
  parseLisp (L.Symbol s) =
    case T.uncons s of
      Just ('?',str) -> return (TVar str)
      _              -> return (TCon s)

  parseLisp (L.List (L.Symbol f:args)) =
    do ts <- mapM L.parseLisp args
       return (TPred f ts)

  parseLisp l =
       L.typeMismatch "Term" l

instance L.ToLisp Term where
  toLisp (TVar s)     = L.Symbol (T.cons '?' s)
  toLisp (TCon n)     = L.Symbol n
  toLisp (TPred f ts) = L.List (L.Symbol f : map L.toLisp ts)
