{-# LANGUAGE OverloadedStrings #-}

module Input.Parser (
    parseDomain,
    parseProblem,
    Atom,
  ) where

import           Input.Types

import           Control.Applicative ((<|>))
import           Control.Monad (unless)
import           Data.SCargot
import           Data.SCargot.Comments (withLispComments)
import           Data.SCargot.Repr
import qualified Data.Text as T
import           Text.Parsec (many,oneOf)
import           Text.Parsec.Char (letter,alphaNum)
import           Text.Parsec.Text (Parser)


-- Parsing ---------------------------------------------------------------------

parseDomain :: T.Text -> Either String Domain
parseDomain  = decodeOne domain

parseProblem :: T.Text -> Either String (Problem T.Text)
parseProblem  = decodeOne problem

domain :: SExprParser Atom Domain
domain  = setCarrier domainParser baseParser

problem :: SExprParser Atom (Problem T.Text)
problem  = setCarrier problemParser baseParser


type P = Either String

-- | Parse a domain from an s-expression.
domainParser :: WellFormedSExpr Atom -> P Domain
domainParser (WFSList ("define" : rest)) =
  do (name,rest1)   <- parseName "domain" rest
     (tys,rest2)    <- parseDomainTypes rest1
     (consts,rest3) <- parseConstants ":constants" rest2
     (props,rest4)  <- parsePredicates ":properties" rest3
     (preds,rest5)  <- parsePredicates ":predicates" rest4
     acts           <- parseActions rest5
     return Domain { domName = name
                   , domTypes = tys
                   , domConsts = consts
                   , domProperties = props
                   , domPreds = preds
                   , domActions = acts }

domainParser _ =
     fail "Expected a top-level `define`"

-- | Parse a domain name.
parseName :: String -> [WellFormedSExpr Atom] -> P (Atom,[WellFormedSExpr Atom])

parseName str (WFSList [WFSAtom lab,WFSAtom name]:rest)
  | str == T.unpack lab = return (name,rest)

parseName str _ =
  fail ("Expected `(" ++ str ++ " <name>)`")


-- | Parse out a types definition from a domain.
parseDomainTypes :: [WellFormedSExpr Atom] -> P ([Type],[WellFormedSExpr Atom])

parseDomainTypes (WFSList (":types":tys):rest) =
  do (annotated,others) <- parseTyped (fmap Type . parseAtom) tys
     return ([ ty | Typed ty _ <- annotated ] ++ others, rest)

parseDomainTypes rest =
     return ([], rest)


-- | Constant definitions.
parseConstants :: String -> [WellFormedSExpr Atom] -> P ([Constant],[WellFormedSExpr Atom])

parseConstants str (WFSList (WFSAtom lab:tcs):rest)
  | str == T.unpack lab =
    do (cs,untyped) <- parseTyped parseAtom tcs
       unless (null untyped)
              (fail ("missing type annotations: " ++ show untyped))
       return (cs,rest)

parseConstants _ rest =
     return ([], rest)


parsePredicates :: T.Text -> [WellFormedSExpr Atom] -> P ([PredDef],[WellFormedSExpr Atom])

parsePredicates key inp@(WFSList (WFSAtom sym:body):rest)
  | key == sym = go [] body
  | otherwise  = return ([], inp)
  where
  go acc (WFSList (WFSAtom name:sig):preds) =
    do (tys,untyped) <- parseTyped parseParam sig
       unless (null untyped)
              (fail ("Missing types for params: " ++ show untyped))
       go (PredDef { pdName = name, pdSpec = tys }:acc) preds

  go _ (p:_) =
       fail ("Invalid predicate: " ++ show p)

  go acc [] =
       return (reverse acc, rest)

parsePredicates key _ =
     fail ("Invalid `" ++ T.unpack key ++ "`")



-- | Parse actions out of the remaining expressions in an action.
parseActions :: [WellFormedSExpr Atom] -> P [Action]
parseActions  = go []
  where
  go acc [] =
       return (reverse acc)

  go acc es =
    do (act,rest) <- parseAction es
       go (act:acc) rest


-- | Action definitions.
parseAction :: [WellFormedSExpr Atom] -> P (Action,[WellFormedSExpr Atom])

parseAction (WFSList (":action":WFSAtom name:body):rest) =
  do (ps,body1) <- parseActionParams body
     (p,body2)  <- parsePrecondition body1
     (e,body3)  <- parseActionEffect body2
     unless (null body3)
            (fail "Invalid action: left-over parts")
     return (Action { actName = name
                    , actParams = ps
                    , actPrecond = p
                    , actEffect = e }, rest)

parseAction _ =
     fail "Invalid action"


-- | Parse the list of parameters to an action.
parseActionParams :: [WellFormedSExpr Atom] -> P ([Param],[WellFormedSExpr Atom])

parseActionParams (WFSAtom ":parameters":WFSList es:rest) =
  do (ts,untyped) <- parseTyped parseParam es
     unless (null untyped)
            (fail ("Action parameters missing types: " ++ show rest))
     return (ts,rest)

parseActionParams _ =
     fail "Invalid parameters"


-- | Parse a parameter (an identifier starting with a question mark).
parseParam :: WellFormedSExpr Atom -> P T.Text

parseParam (WFSAtom str) =
  case T.uncons str of
    Just ('?', _) -> return str
    _             -> fail "Parameters must start with a `?`"
parseParam WFSList{} =
     fail "Expected an atom for a parameter name"


parsePrecondition :: [WellFormedSExpr Atom] -> P (Pre, [WellFormedSExpr Atom])

parsePrecondition (":precondition":body:rest) =
  do tm <- parsePre body
     return (tm,rest)

-- no precondition
parsePrecondition rest =
     return (pAnd [], rest)


-- | Parse a term.
parsePre :: WellFormedSExpr Atom -> P Pre

parsePre (WFSList ("and":body)) =
  do es <- mapM parsePre body
     return (pAnd es)

parsePre (WFSList ("or":body)) =
  do es <- mapM parsePre body
     return (pOr es)

parsePre (WFSList ["not",body]) =
  do e <- parsePre body
     return (PNot e)

parsePre (WFSList ["exists",WFSList args,body]) =
  do (ps,untyped) <- parseTyped parseParam args
     unless (null untyped)
            (fail ("Some arguments missing types on exists: " ++ show untyped))
     e  <- parsePre body
     return (PExists ps e)

parsePre (WFSList ["forall",WFSList args,body]) =
  do (ps,untyped) <- parseTyped parseParam args
     unless (null untyped)
            (fail ("Some arguments missing types on forall: " ++ show untyped))
     e  <- parsePre body
     return (PForall ps e)

parsePre (WFSList ["=>",a,b]) =
  do a' <- parsePre a
     b' <- parsePre b
     return (PImp a' b')

parsePre (WFSList body) =
  do lit <- parseLiteral body
     return (PLit lit)

parsePre _ =
     fail "Invalid term, expected a list"



-- | Parse an action effect.
parseActionEffect :: [WellFormedSExpr Atom] -> P (Effect,[WellFormedSExpr Atom])

parseActionEffect (":effect":body:rest) =
  do eff <- parseEffect body
     return (eff, rest)

parseActionEffect (_:_) =
     fail "Invalid effect"

parseActionEffect [] =
     fail "Missing effect"


-- | Parse a single action effect.
parseEffect :: WellFormedSExpr Atom -> P Effect

parseEffect (WFSList ("and":body)) =
  do es <- mapM parseEffect body
     return (EAnd es)

parseEffect (WFSList ["when",t,e]) =
  do t' <- parsePre t
     e' <- parseEffect e
     return (EWhen t' e')

parseEffect (WFSList ["forall",WFSList args,body]) =
  do (ps,untyped) <- parseTyped parseParam args
     unless (null untyped)
            (fail ("Some arguments missing types on effect forall: " ++ show untyped))
     e            <- parseEffect body
     return (EForall ps e)

parseEffect (WFSList ["not",WFSList es]) =
  do lit <- parseLiteral es
     return (ENot lit)

parseEffect (WFSList es) =
  do lit <- parseLiteral es
     return (ELit lit)

parseEffect _ =
     fail "Invalid action effect"


parseLiteral :: [WellFormedSExpr Atom] -> P Literal

parseLiteral es
  | Just (p:es') <- mapM isAtom es =
    return (Pred p es')

  | otherwise =
    fail "Invalid literal"


-- | Parse a list of things that have type annotations.
parseTyped :: (WellFormedSExpr Atom -> P a)
           -> [WellFormedSExpr Atom]
           -> P ([Typed a],[a])

parseTyped f = go [] []
  where

  go delayed acc ("-":WFSAtom ty:rest) =
       go [] (map (`Typed` Type ty) delayed ++ acc) rest

  go delayed acc (e:rest) =
    do a <- f e
       go (a:delayed) acc rest

  go delayed acc [] =
       return (reverse acc, reverse delayed)


parseAtom :: WellFormedSExpr Atom -> P Atom
parseAtom (WFSAtom a) = return a
parseAtom _           = fail "Expected an atom"


-- | Parse a problem description.
problemParser :: WellFormedSExpr Atom -> P (Problem T.Text)
problemParser (WFSList ("define" : rest)) =
  do (name,rest1) <- parseName "problem" rest
     (dom,rest2)  <- parseName ":domain" rest1
     (objs,rest3) <- parseConstants ":objects" rest2
     (is,rest4)   <- parseInit rest3
     (goal,_)     <- parseGoal rest4
     return Problem { probName = name
                    , probDomain = dom
                    , probObjects = objs
                    , probInit = is
                    , probGoal = goal
                    }

problemParser _ =
     fail "Invalid problem"

parseInit :: [WellFormedSExpr Atom] -> P ([Literal],[WellFormedSExpr Atom])

parseInit (WFSList (":init":is):rest) =
  do is' <- traverse (expectList parseLiteral) is
     return (is',rest)

parseInit _ =
     fail "Expected an :init section"


parseGoal :: [WellFormedSExpr Atom] -> P (Pre,[WellFormedSExpr Atom])

parseGoal (WFSList [":goal",tm]:rest) =
  do goal <- parsePre tm
     return (goal,rest)

parseGoal _ =
     fail "Invalid :goal section"


-- Utilities -------------------------------------------------------------------

baseParser :: SExprParser T.Text (WellFormedSExpr Atom)
baseParser  = withLispComments (asWellFormed (mkParser atom))

type Atom = T.Text

atom :: Parser Atom
atom  =
  do l  <- letter <|> oneOf "=:-?"
     as <- many (alphaNum <|> oneOf "?!_->")
     return (T.pack (l:as))

isAtom :: WellFormedSExpr Atom -> Maybe Atom
isAtom (WFSAtom str) = Just str
isAtom _             = Nothing


expectList :: ([WellFormedSExpr Atom] -> P r) -> WellFormedSExpr Atom -> P r
expectList f (WFSList es) = f es
expectList _ _            = fail "Expected a list"
