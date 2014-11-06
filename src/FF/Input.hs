{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}

module FF.Input where

import           Control.Applicative ( Applicative(..), Alternative(..) )
import           Control.Monad ( unless, when )
import qualified Data.Attoparsec.Text.Lazy as A
import qualified Data.Text as S
import qualified Data.Text.Lazy as L

data PDDL = PDDLProblem Problem
          | PDDLDomain Domain
            deriving (Show)

type Name = S.Text

data Domain = Domain { dName     :: Name
                     , dRequires :: [Requirement]
                     } deriving (Show)

data Problem = Problem { pName     :: !Name
                       , pDomain   :: !Name
                       , pRequires :: [Requirement]
                       } deriving (Show)

data Requirement = ReqStrips
                 | ReqTyping
                 | ReqNegativePreconditions
                 | ReqDisjunctivePreconditions
                 | ReqEquality
                 | ReqExistentialPreconditions
                 | ReqUniversalPreconditions
                 | ReqQuantifiedPreconditions
                 | ReqConditionalEffects
                 | ReqFluents
                 | ReqNumericFluents
                 | ReqObjectFluents
                 | ReqAdl
                 | ReqDurativeActions
                 | ReqDurationInequalities
                 | ReqContinuousEffects
                 | ReqDerivedPredicates
                 | ReqTimedInitialLiterals
                 | ReqPreferences
                 | ReqConstraints
                 | ReqActionCosts
                   deriving (Show)

expandRequirement :: Requirement -> [Requirement]
expandRequirement ReqQuantifiedPreconditions =
  [ ReqExistentialPreconditions
  , ReqUniversalPreconditions ]
expandRequirement ReqFluents  =
  [ ReqNumericFluents
  , ReqObjectFluents ]
expandRequirement ReqAdl =
  [ ReqStrips
  , ReqTyping
  , ReqNegativePreconditions
  , ReqDisjunctivePreconditions
  , ReqEquality
  , ReqExistentialPreconditions
  , ReqUniversalPreconditions
  , ReqConditionalEffects ]
expandRequirement ReqTimedInitialLiterals =
  [ ReqTimedInitialLiterals
  , ReqDurativeActions ]
expandRequirement req = [req]


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

-- | Parse the requirements definition from a domain or problem.
requireDef :: SExp -> A.Parser [Requirement]
requireDef exp = case exp of

  SList (SSymbol ":requirements" : rest) -> mapM requireKey rest

  _ -> fail "Expected (:requirements <require-key>*)"

requireKey :: SExp -> A.Parser Requirement
requireKey exp = case exp of
  SSymbol ":strips"                    -> return ReqStrips
  SSymbol ":typing"                    -> return ReqTyping
  SSymbol ":negative-preconditions"    -> return ReqNegativePreconditions
  SSymbol ":disjunctive-preconditions" -> return ReqDisjunctivePreconditions
  SSymbol ":equality"                  -> return ReqEquality
  SSymbol ":existential-preconditions" -> return ReqExistentialPreconditions
  SSymbol ":universal-preconditions"   -> return ReqUniversalPreconditions
  SSymbol ":quantified-preconditions"  -> return ReqQuantifiedPreconditions
  SSymbol ":conditional-effects"       -> return ReqConditionalEffects
  SSymbol ":fluents"                   -> return ReqFluents
  SSymbol ":numeric-fluents"           -> return ReqNumericFluents
  SSymbol ":object-fluents"            -> return ReqObjectFluents
  SSymbol ":adl"                       -> return ReqAdl
  SSymbol ":durative-actions"          -> return ReqDurativeActions
  SSymbol ":duration-inequalities"     -> return ReqDurationInequalities
  SSymbol ":continuous-effects"        -> return ReqContinuousEffects
  SSymbol ":derived-predicates"        -> return ReqDerivedPredicates
  SSymbol ":timed-initial-literals"    -> return ReqTimedInitialLiterals
  SSymbol ":preferences"               -> return ReqPreferences
  SSymbol ":constraints"               -> return ReqConstraints
  SSymbol ":action-costs"              -> return ReqActionCosts
  _                                    -> fail "Expected <require-key>"
