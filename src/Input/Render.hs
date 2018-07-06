{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Input.Render (
    render,
    ToSExpr(..),
  ) where

import Input.Parser
import Input.Types

import           Data.SCargot.Print (unconstrainedPrint,setFromCarrier,encodeOne)
import           Data.SCargot.Repr.Basic (SExpr(..),pattern L,pattern A)
import qualified Data.Text as T


render :: ToSExpr a => a -> T.Text
render  = encodeOne (setFromCarrier toSExpr (unconstrainedPrint id))

class ToSExpr a where
  toSExpr :: a -> SExpr Atom

instance ToSExpr T.Text where
  toSExpr = A

instance ToSExpr (Problem T.Text) where
  toSExpr Problem { .. } =
    L $ [ A "define"
        , L [ A "problem", A probName ]
        , L [ A ":domain", A probDomain ]
        , L (A ":objects" : typedList probObjects)
        ] ++ A ":init" : map toSExpr probInit
          ++ [ A ":goal", toSExpr probGoal ]

instance ToSExpr Domain where
  toSExpr Domain { .. } =
    L $ [ A "define"
        , L [ A "domain", A domName ]
        , L ( A ":types" : map toSExpr domTypes )
        , L ( A ":constants" : typedList domConsts )
        , L ( A ":properties" : map toSExpr domProperties )
        , L ( A ":predicates" : map toSExpr domPreds)
        ] ++ map toSExpr domActions

instance ToSExpr Type where
  toSExpr (Type ty) = A ty

typedList :: ToSExpr a => [Typed a] -> [SExpr Atom]
typedList tys =
  case tys of
    []                -> []
    Typed a ty : rest -> go [a] ty rest
  where
  go delayed ty (Typed a ty' : rest)
    | ty == ty' = go (a:delayed) ty rest
    | otherwise = fmt delayed ty ++ go [a] ty' rest

  go delayed ty [] = fmt delayed ty

  fmt as ty = map toSExpr (reverse as) ++ [ A "-", toSExpr ty ]

instance ToSExpr Pre where
  toSExpr (PAnd as)      = L (A "and" : map toSExpr as)
  toSExpr (POr as)       = L (A "or"  : map toSExpr as)
  toSExpr (PNot p)       = L [ A "not", toSExpr p ]
  toSExpr (PImp a b)     = L [ A "=>", toSExpr a, toSExpr b ]
  toSExpr (PExists ps p) = L [ A "exists", L (typedList ps), toSExpr p ]
  toSExpr (PForall ps p) = L [ A "forall", L (typedList ps), toSExpr p ]
  toSExpr (PLit lit)     = toSExpr lit

instance ToSExpr PredDef where
  toSExpr (PredDef name tys) = L (A name : typedList tys)

instance ToSExpr arg => ToSExpr (Pred arg) where
  toSExpr (Pred name args) = L (A name : map toSExpr args)

instance ToSExpr Action where
  toSExpr Action { .. } =
    L [ A ":action"
      , A actName
      , A ":parameters", L (typedList actParams)
      , A ":precondition", toSExpr actPrecond
      , A ":effect", toSExpr actEffect ]

instance ToSExpr Effect where
  toSExpr (EForall ps e) = L [ A "forall", L (typedList ps), toSExpr e ]
  toSExpr (EWhen p e)    = L [ A "when", toSExpr p, toSExpr e ]
  toSExpr (EAnd es)      = L ( A "and" : map toSExpr es )
  toSExpr (ENot lit)     = L [ A "not", toSExpr lit ]
  toSExpr (ELit lit)     = toSExpr lit
