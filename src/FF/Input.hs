{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}

module FF.Input {-(
    Term(..)
  , Problem(..), parseProblem
  , Domain(..), parseDomain
  , Typed(..)
  , Pred(..)
  , Action(..)
  ) -}where

import           Control.Applicative ( Applicative(..), Alternative(..) )
import           Control.Monad ( unless, when )
import qualified Data.Attoparsec.Text.Lazy as A
import qualified Data.Text as S
import qualified Data.Text.Lazy as L

data PDDL = PDDLProblem Problem
          | PDDLDomain Domain
            deriving (Show)

data Problem = Problem { pName   :: !S.Text
                       , pDomain :: !S.Text
                       , pInits  :: Term
                       , pGoal   :: Term
                       } deriving (Show)

data Domain = Domain { dName    :: !S.Text
                     , dTypes   :: [Typed [S.Text]]
                       -- ^ Defined types
                     , dPreds   :: [Pred]
                       -- ^ Signatures for all predicates that show up
                     , dActions :: [Action]
                     } deriving (Show)

data Typed a = Typed { tVal  :: a
                     , tType :: !S.Text
                     } deriving (Show)

data Pred = Pred { pdName :: !S.Text
                 , pdArgs :: [Typed [S.Text]]
                 } deriving (Show)

data Action = Action { aName   :: !S.Text
                     , aParams :: [Typed [S.Text]]
                     , aPre    :: Term
                     , aEff    :: Term
                     } deriving (Show)

data Term = TVar  !S.Text
          | TCon  !S.Text
          | TPred !S.Text [Term]
            deriving (Show)


-- Parsing ---------------------------------------------------------------------

data SExp = SList [SExp]
          | SString !S.Text
          | SSymbol !S.Text
          | SInt !Integer
            deriving (Show)

comment :: A.Parser ()
comment  = A.option () $ do A.char ';'
                            loop
  where
  loop = do done <- A.choice [ do c <- A.satisfy A.isEndOfLine
                                  when (c == '\r') (A.skip (== '\n'))
                                  return True

                             ,    A.atEnd
                             ]
            if done
               then do A.skipSpace
                       comment
               else do A.skip (const True)
                       loop

sexp :: A.Parser SExp
sexp  = (A.skipSpace *> comment *> (slist <|> sstring <|> ssymbol <|> sint))
  A.<?> "sexp"
  where
  spaces = A.many1 A.space

  slist = do A.char '('
             exps <- A.manyTill (sexp <* A.skipSpace) (A.char ')')
             return (SList exps)
       A.<?> "slist"

  sstring = do A.char '"'
               str <- A.takeWhile (/= '\"')
               A.char '"'
               return (SString str)
         A.<?> "string"


  symChars = ":-!?_" ++ ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9']
  ssymbol  = do sym <- A.takeWhile1 (`elem` symChars)
                return (SSymbol sym)
          A.<?> "symbol"

  sint = do n <- A.decimal
            return (SInt n)
      A.<?> "integer"


--pddl :: A.Parser [PDDL]
pddl  = loop
  where
  loop = do comment
            end <- A.atEnd
            if end
               then return []
               else do e <- sexp
                       rest <- loop
                       return (e:rest)




{-

parseDomain :: S.ByteString -> Either String Domain
parseDomain bytes =
  case parseLisp bytes of
    L.Success a -> Right a
    L.Error msg -> Left msg

parseProblem :: S.ByteString -> Either String Problem
parseProblem bytes =
  case parseLisp bytes of
    L.Success a -> Right a
    L.Error msg -> Left msg

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
       L.List preds   <- namedArg ":predicates" args
       dPreds         <- mapM L.parseLisp preds
       dActions       <- namedArgs ":action" args
       return Domain { .. } 

instance L.ToLisp Domain where
  toLisp Domain { .. } =
    L.List $ L.Symbol "define"
           : pair "domain" (L.Symbol dName)
           : pair ":types" (L.List (concatMap (typedLisp (map L.Symbol)) dTypes))
           : L.List (L.Symbol ":predicates" : map L.toLisp dPreds)
           : map L.toLisp dActions
      where
      pair n l = L.List [ L.Symbol n, l ]

typedLisp :: (a -> [L.Lisp]) -> Typed a -> [L.Lisp]
typedLisp lispArg Typed { .. } =
  lispArg tVal ++ [L.Symbol "-", L.Symbol tType]

instance L.FromLisp Pred where
  parseLisp (L.List (L.Symbol pdName : params)) =
    do pdArgs <- parseParams params
       return Pred { .. }

  parseLisp l =
       L.typeMismatch "Pred" l

instance L.ToLisp Pred where
  toLisp Pred { .. } =
    L.List [ L.Symbol pdName
           , L.List (concatMap (typedLisp (map mkVar)) pdArgs)
           ]
    where
    mkVar str = L.Symbol (T.cons '?' str)

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

-}
