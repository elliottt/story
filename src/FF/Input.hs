{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE DeriveFunctor #-}

module FF.Input where

import           Control.Applicative ( Applicative(..), Alternative(..) )
import           Control.Monad ( when )
import qualified Data.Attoparsec.Text.Lazy as A
import qualified Data.Set as Set
import qualified Data.Text as S

data PDDL = PDDLProblem Problem
          | PDDLDomain Domain
            deriving (Show)

type Name = S.Text
type Pred = Name

type Var  = S.Text

data Domain = Domain { dName     :: Name
                     , dRequires :: [Requirement]
                     , dTypes    :: TypedList Name
                     , dConsts   :: TypedList Name
                     , dPredSigs :: [PredSig]
                     , dFuns     :: TypedList Function
                     , dCons     :: [Con]
                     } deriving (Show)

emptyDomain :: Name -> Domain
emptyDomain n = Domain { dName     = n
                       , dRequires = []
                       , dTypes    = UntypedList []
                       , dConsts   = UntypedList []
                       , dPredSigs = []
                       , dFuns     = UntypedList []
                       , dCons     = []
                       }

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

data TypedList a = UntypedList [a]
                 | TypedList [Typed a]
                   deriving (Show,Functor)

data Typed a = Typed { tType :: Type
                     , tVal  :: a
                     } deriving (Show,Functor)

data Type = Type Name
          | Either [Name]
            deriving (Show)

data PredSig = PredSig { psName :: Name
                       , psArgs :: TypedList Name
                       } deriving (Show)

data Function = Function { funName :: Name
                         , funArgs :: TypedList Name
                         } deriving (Show)

data Term = TVar Var
          | TName Name
            deriving (Show)

data GoalDesc = GDAnd [GoalDesc]
              | GDOr [GoalDesc]
              | GDNot GoalDesc
              | GDImply GoalDesc GoalDesc
              | GDExists (TypedList Var) GoalDesc
              | GDForall (TypedList Var) GoalDesc
              | GDLit (Literal Term)
                deriving (Show)

data Con = CAnd [GoalDesc]
         | CForall (TypedList Name) Con
         | CAtEnd GoalDesc
         | CAlways GoalDesc
         | CSometime GoalDesc
         | CWithin Int GoalDesc
         | CAtMostOnce GoalDesc
         | CSometimeAfter GoalDesc GoalDesc
         | CSometimeBefore GoalDesc GoalDesc
         | CAlwaysWithin Int GoalDesc GoalDesc
         | CHoldDuring Int Int GoalDesc
         | CHoldAfter Int GoalDesc
           deriving (Show)

data Literal a = Literal Bool (Formula a)
                 deriving (Show)

data Formula a = FPred Pred [a]
               | FEq a a
                 deriving (Show)


-- Utilities -------------------------------------------------------------------

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
          | SInt !Int
            deriving (Show)

comment :: A.Parser ()
comment  = A.option () $ do _ <- A.char ';'
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
  slist = do _    <- A.char '('
             exps <- A.manyTill (sexp <* A.skipSpace) (A.char ')')
             return (SList exps)
       A.<?> "slist"

  sstring = do _   <- A.char '"'
               str <- A.takeWhile (/= '\"')
               _   <- A.char '"'
               return (SString str)
         A.<?> "string"


  symChars = ":-!?_" ++ ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9']
  ssymbol  = do sym <- A.takeWhile1 (`elem` symChars)
                return (SSymbol sym)
          A.<?> "symbol"

  sint = do n <- A.decimal
            return (SInt n)
      A.<?> "integer"

parseVar :: SExp -> A.Parser Var
parseVar (SSymbol name) | Just ('?',_) <- S.uncons name = return name
parseVar _                                              = fail "expected a var"

parseName :: SExp -> A.Parser Name
parseName (SSymbol name) = return name
parseName _              = fail "expected a name"

parseType :: SExp -> A.Parser Type
parseType (SSymbol name)                 = return (Type name)
parseType (SList (SSymbol "either":tys)) = Either `fmap` mapM parseName tys
parseType _                              = fail "expected a type"

parseTerm :: SExp -> A.Parser Term
parseTerm e = (TName `fmap` parseName e)
          <|> (TVar  `fmap` parseVar  e)

pddl :: A.Parser [PDDL]
pddl  = loop
  where
  loop = do comment
            end <- A.atEnd
            if end
               then return []
               else do e    <- pddlElem =<< sexp
                       rest <- loop
                       return (e:rest)

pddlElem :: SExp -> A.Parser PDDL
pddlElem (SList (SSymbol "define" : rest)) =
  case rest of
    SList [SSymbol "domain", SSymbol name] : rest' -> 
        PDDLDomain  `fmap` domain  name rest'

    SList [SSymbol "problem", SSymbol name] : rest' ->
        PDDLProblem `fmap` problem name rest'

    _ -> fail "invalid top-level element"
pddlElem _ =
  fail "expected pddl element"

domain :: Name -> [SExp] -> A.Parser Domain
domain domName = loop Set.empty (emptyDomain domName)
  where
  loop seen _ (SList (SSymbol name : _) : _)
    | name `Set.member` seen =
       fail ("invalid domain specification, more than one " ++ S.unpack name ++ " group")

  loop seen dom (SList (SSymbol ":requirements":reqs):rest) =
    do rs <- mapM requireKey reqs
       loop (Set.insert ":requirements" seen) dom { dRequires = rs } rest

  loop seen dom (SList (SSymbol ":types":types):rest) =
    do tys <- typedList parseName types
       loop (Set.insert ":types" seen) dom { dTypes = tys } rest

  loop seen dom (SList (SSymbol ":constants":consts):rest) =
    do cs <- typedList parseName consts
       loop (Set.insert ":constraints" seen) dom { dConsts = cs } rest

  loop seen dom (SList (SSymbol ":predicates":sigs):rest) =
    do ps <- mapM predSig sigs
       loop (Set.insert ":predicates" seen) dom { dPredSigs = ps } rest

  loop seen dom (SList (SSymbol ":functions":funs):rest) =
    do fs <- typedList function funs
       loop (Set.insert ":functions" seen) dom { dFuns = fs } rest

  loop _ dom [] =
       return dom

  loop _ _ _ =
       fail "invalid domain specification"

problem :: Name -> [SExp] -> A.Parser Problem
problem name def =
     undefined

requireKey :: SExp -> A.Parser Requirement
requireKey e = case e of
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

typedList :: (SExp -> A.Parser a) -> [SExp] -> A.Parser (TypedList a)
typedList parse es = loop [] es A.<?> "typed list"
  where
  loop as (e:rest) = case e of

    SSymbol "-" -> addType as rest
    _           -> do a <- parse e
                      loop (a:as) rest

  loop as [] = return (UntypedList (reverse as))

  addType as (sym:rest) =
    do ty <- parseType sym
       let as' = [ Typed ty a | a <- reverse as ]
       if null rest
          then return (TypedList as')
          else do TypedList tys <- typed [] rest
                  return (TypedList (as' ++ tys))

  addType _ _ = fail "expected a type"

  typed as (e:rest) = case e of

    SSymbol "-" -> addType as rest
    _           -> do a <- parse e
                      typed (a:as) rest

  typed _ [] = fail "set of variables without a final type"

predSig :: SExp -> A.Parser PredSig
predSig (SList (SSymbol name : args)) =
  do as <- typedList parseVar args
     return PredSig { psName = name, psArgs = as }
predSig _ =
     fail "expected predicate"


function :: SExp -> A.Parser Function
function (SList (SSymbol name : args)) =
  do as <- typedList parseVar args
     return Function { funName = name, funArgs = as }
function _ =
     fail "expected function"

goalDesc :: SExp -> A.Parser GoalDesc
goalDesc (SList (SSymbol sym : rest))
  | sym == "and" =
       GDAnd `fmap` mapM goalDesc rest

  | sym == "or" =
       GDOr  `fmap` mapM goalDesc rest

  | sym == "imply", [p,q] <- rest =
    do a <- goalDesc p
       b <- goalDesc q
       return (GDImply a b)

  | sym == "exists", [SList tys,body] <- rest =
    do args <- typedList parseVar tys
       gd   <- goalDesc body
       return (GDExists args gd)

  | sym == "forall", [SList tys,body] <- rest =
    do args <- typedList parseVar tys
       gd   <- goalDesc body
       return (GDForall args gd)

goalDesc e =
   GDLit `fmap` literal parseTerm e


constraint :: SExp -> A.Parser Con
constraint (SList (SSymbol sym : cons))

  | sym == "and" =
       CAnd `fmap` mapM goalDesc cons

  | sym == "forall", [SList vars,body] <- cons =
    do args <- typedList parseVar vars
       con  <- constraint body
       return (CForall args con)

  | sym == "at", [SSymbol "end",body] <- cons =
       CAtEnd `fmap` goalDesc body

  | sym == "always", [body] <- cons =
       CAlways `fmap` goalDesc body

  | sym == "sometime", [body] <- cons =
       CSometime `fmap` goalDesc body

  | sym == "within", [SInt n,body] <- cons =
       CWithin n `fmap` goalDesc body

  | sym == "at-most-once", [body] <- cons =
       CAtMostOnce `fmap` goalDesc body

  | sym == "sometime-after", [a,b] <- cons =
    do x <- goalDesc a
       y <- goalDesc b
       return (CSometimeAfter x y)

  | sym == "sometime-before", [a,b] <- cons =
    do x <- goalDesc a
       y <- goalDesc b
       return (CSometimeBefore x y)

  | sym == "always-within", [SInt n, a, b] <- cons =
    do x <- goalDesc a
       y <- goalDesc b
       return (CAlwaysWithin n x y)

  | sym == "hold-during", [SInt a, SInt b, body] <- cons =
       CHoldDuring a b `fmap` goalDesc body

  | sym == "hold-after", [SInt n, body] <- cons =
       CHoldAfter n `fmap` goalDesc body

constraint _ = fail "expected <con-GD>"


literal :: (SExp -> A.Parser a) -> SExp -> A.Parser (Literal a)
literal parse e@(SList (SSymbol sym : args))
  | sym == "not" = Literal False `fmap` formula parse (SList args)
  | otherwise    = Literal True  `fmap` formula parse e
literal _ _ = fail "expected <literal>"


formula :: (SExp -> A.Parser a) -> SExp -> A.Parser (Formula a)
formula parse (SList (SSymbol sym : args))
  | sym == "=", [a,b] <- args =
    do x <- parse a
       y <- parse b
       return (FEq x y)

  | otherwise =
       FPred sym `fmap` mapM parse args

formula _ _ = fail "expected <atomic formula>"
