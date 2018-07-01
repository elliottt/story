{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ParallelListComp #-}

module Input.Ground where

import Input.Types

import           Control.Applicative (Alternative,empty)
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import           Data.Maybe (fromMaybe)
import qualified Data.Text as T


-- | Ground an input problem in the context of its domain.
groundProblem :: Problem Domain -> Problem Domain
groundProblem prob =
  prob { probDomain = dom { domActions = actions' }
       , probGoal   = PLit goalLit
       , probInit   = negInits negPreconds (probInit prob)
       }
  where

  goalLit = Pred "$goal-achieved" []

  goalOperator =
    Action { actName = "$goal-operator"
           , actParams = []
           , actPrecond = probGoal prob
           , actEffect = ELit goalLit
           }


  -- predicates that are used with negation in action preconditions
  negPreconds =
    HS.filter (\ (Pred name _) -> not (name `HM.member` cProps ctx))
              (foldMap (negativePreconditions . actPrecond) actions')

  actions' = concatMap groundAction (goalOperator : domActions dom)

  groundAction act =
    do let disjuncts = eliminateDisjunction
                     $ eliminiateQuantifiers ctx
                     $ nnfAction act

           moreThanOne =
             case disjuncts of
               _:rest -> not (null rest)
               _      -> False

           noParams = null (actParams act)

       (i,act') <- zip [1 ..] disjuncts

       inst <- instancesOf ctx (actParams act)

       let su     = HM.fromList inst

           params = [ Typed n ty | Typed _ ty <- actParams act
                                 | (_,n)      <- inst ]
           nameParts
             | noParams && moreThanOne = [ T.pack (show (i :: Int)) ]
             | noParams                = []
             | otherwise               = [ name | (_,name) <- inst ]

           new = act' { actName    = T.intercalate "-" (actName act : nameParts)
                      , actParams  = params
                      , actPrecond = subst su (actPrecond act')
                      , actEffect  = subst su (actEffect act') }

       validateAction ctx new

  dom = probDomain prob

  ctx = groundingContext prob

  -- add assertions of negatives for predicates with negative counterparts that
  -- aren't mentioned in the initial state.
  negInits negs (lit : rest)
    | lit `elem` negs = lit : negInits (HS.delete lit negs) rest
    | otherwise       = lit : negInits                negs  rest

  negInits negs [] = map mkNegLit (HS.toList negs)



-- Context ---------------------------------------------------------------------

data Context = Context { cObjects :: !(HM.HashMap Type [T.Text])
                       , cProps   :: !(HM.HashMap Name [[Name]])
                       } deriving (Show)

-- | Collect the aggregate object and predicate information from the
-- problem/domain pair.
groundingContext :: Problem Domain -> Context
groundingContext prob =
  Context { cObjects = objects
          , cProps   = props
          }
  where

  dom = probDomain prob

  objects = HM.fromListWith (++)
          $ reverse
          $ [ (ty,[con]) | Typed con ty <- domConsts dom ]
         ++ [ (ty,[con]) | Typed con ty <- probObjects prob ]

  propNames = HS.fromList [ name | PredDef name _ <- domProperties dom ]

  props = HM.fromListWith (++)
          [ (name, [args])
          | Pred name args <- probInit prob
          , name `HS.member` propNames ]


-- | Enumerate instances of a predicate, given context.
instancesOf :: Context -> [Typed a] -> [[(a,Name)]]
instancesOf Context { cObjects } args =
  sequence [ zip (repeat a) (HM.lookupDefault [] ty cObjects)
           | Typed a ty <- args ]

-- | Check an instantiation of a property, returning 'Nothing' if the name given
-- is not a property.
checkProperty :: Context -> Name -> [Name] -> Maybe Bool
checkProperty ctx name inst =
  do insts <- HM.lookup name (cProps ctx)
     return (inst `elem` insts)


-- Action Validation -----------------------------------------------------------

-- | Validate an action, returning 'empty' if the action is not valid. This
-- assumes that the action is grounded.
validateAction :: Alternative f => Context -> Action -> f Action
validateAction ctx act
  | validPre ctx (actPrecond act) && validEffect ctx (actEffect act) = pure act
  | otherwise                                                        = empty

-- | Check to see if a grounded precondition is valid.
validPre :: Context -> Pre -> Bool
validPre ctx p =
  case p of
    PAnd ps -> all validSimple ps
    _       -> validSimple p

  where

  validSimple (PNot (PLit lit)) = maybe True not (validLit ctx lit)
  validSimple (PLit lit)        = fromMaybe True (validLit ctx lit)
  validSimple _                 = error "validPre: precondition not grounded"

-- | Check to see if an effect is valid.
validEffect :: Context -> Effect -> Bool
validEffect ctx (EAnd es)   = all (validEffect ctx) es
validEffect ctx (ENot p)    = maybe True not (validLit ctx p)
validEffect ctx (ELit p)    = fromMaybe True (validLit ctx p)
validEffect ctx (EWhen p e) = validPre ctx p && validEffect ctx e
validEffect _   EForall{}   = error "validEffect: effect not grounded"

-- | Evaluate a literal, with 'Nothing' representing uncertainty.
validLit :: Context -> Literal -> Maybe Bool
validLit _   (Pred "=" [x,y]) = Just (x == y)
validLit ctx (Pred name args) = checkProperty ctx name args


-- Negation Normal Form --------------------------------------------------------

-- | Put an action in negation normal form.
nnfAction :: Action -> Action
nnfAction act =
  act { actPrecond = nnfPre (actPrecond act)
      , actEffect  = nnfEffect (actEffect act) }

nnfPre :: Pre -> Pre

nnfPre pre@(PNot i) =
  case i of
    PAnd ps      -> pOr  (map (nnfPre . PNot) ps)
    POr ps       -> pAnd (map (nnfPre . PNot) ps)
    PImp a b     -> pAnd [nnfPre a, nnfPre (PNot b)]
    PExists ps p -> PForall ps (nnfPre (PNot p))
    PForall ps p -> PExists ps (nnfPre (PNot p))
    PNot p       -> nnfPre p
    PLit{}       -> pre

nnfPre (PAnd ps)      = pAnd (map nnfPre ps)
nnfPre (POr  ps)      = pOr (map nnfPre ps)
nnfPre (PImp a b)     = pOr [nnfPre (PNot a), nnfPre b]
nnfPre (PExists ps p) = PExists ps (nnfPre p)
nnfPre (PForall ps p) = PForall ps (nnfPre p)
nnfPre p@PLit{}       = p

nnfEffect :: Effect -> Effect
nnfEffect (EForall ps e) = EForall ps (nnfEffect e)
nnfEffect (EWhen p e)    = EWhen (nnfPre p) (nnfEffect e)
nnfEffect (EAnd es)      = EAnd (map nnfEffect es)
nnfEffect e@ENot{}       = e
nnfEffect e@ELit{}       = e


-- Negative Preconditions ------------------------------------------------------

mkNegLit :: Literal -> Literal
mkNegLit (Pred name args) = Pred ("$not-" <> name) args

-- | Collect negative instances of predicates
negativePreconditions :: Pre -> HS.HashSet Literal

negativePreconditions (PAnd ps) =
  foldMap negativePreconditions ps

negativePreconditions (POr ps) =
  foldMap negativePreconditions ps

-- NOTE: equality is handled specially during grounding, so it's not considered
-- to be a use of negative preconditions.
negativePreconditions (PNot (PLit lit))
  | predName lit == T.pack "=" = HS.empty
  | otherwise                  = HS.singleton lit

negativePreconditions PLit{} =
  HS.empty

negativePreconditions PImp{} =
  error "negativePreconditions: unexpected PImp"

negativePreconditions PNot{} =
  error "negativePreconditions: unexpected PNot"

negativePreconditions PExists{} =
  error "negativePreconditions: unexpected PExists"

negativePreconditions PForall{} =
  error "negativePreconditions: unexpected PForall"


-- Quantifier Elimination ------------------------------------------------------

-- | Remove quantifiers from actions.
eliminiateQuantifiers :: Context -> Action -> Action
eliminiateQuantifiers ctx act =
  act { actPrecond = elimQuantPre ctx emptySubst (actPrecond act)
      , actEffect  = elimQuantEff ctx (actEffect act) }


elimQuantPre :: Context -> Subst -> Pre -> Pre
elimQuantPre ctx = go
  where
  go su (PAnd ps)      = pAnd (map (go su) ps)
  go su (POr  ps)      = pOr  (map (go su) ps)
  go su (PNot p)       = PNot (go su p)
  go su (PImp a b)     = PImp (go su a) (go su b)

  go su (PExists ps e) = pOr $
    do inst <- instancesOf ctx ps
       let su' = HM.fromList inst `HM.union` su
       return (go su' e)

  go su (PForall ps e) = pAnd $
    do inst <- instancesOf ctx ps
       let su' = HM.fromList inst `HM.union` su
       return (go su' e)

  go su (PLit p) = PLit (subst su p)

elimQuantEff :: Context -> Effect -> Effect
elimQuantEff ctx = go HM.empty
  where
  go su (EForall ps e) = eAnd $
    do inst <- instancesOf ctx ps
       let su' = HM.fromList inst `HM.union` su
       return (go su' e)

  go su (EWhen p e) = EWhen (elimQuantPre ctx su p) (go su e)

  go su (EAnd es)   = eAnd (map (go su) es)
  go su (ENot p)    = ENot (subst su p)
  go su (ELit p)    = ELit (subst su p)


-- Disjunction Elimination -----------------------------------------------------

-- | Eliminate disjunctions from actions. This assumes that the actions have
-- been put in negation normal form, and had quantifiers eliminated.
eliminateDisjunction :: Action -> [Action]
eliminateDisjunction act =
  do pre <- elimDisjPre (actPrecond act)
     eff <- elimDisjEff (actEffect act)
     return act { actPrecond = pre, actEffect = eff }

elimDisjPre :: Pre -> [Pre]
elimDisjPre (PAnd ps) = pAnd <$> traverse elimDisjPre ps
elimDisjPre (POr  ps) = concatMap elimDisjPre ps
elimDisjPre p@PNot{}  = return p
elimDisjPre p@PLit{}  = return p
elimDisjPre PImp{}    = error "elimDisjPre: unexpected PImp"
elimDisjPre PExists{} = error "elimDisjPre: unexpected PExists"
elimDisjPre PForall{} = error "elimDisjPre: unexpected PForall"

elimDisjEff :: Effect -> [Effect]
elimDisjEff (EWhen p e) =
  do p' <- elimDisjPre p
     e' <- elimDisjEff e
     return (EWhen p' e')

elimDisjEff (EAnd es) = eAnd <$> traverse elimDisjEff es

elimDisjEff e@ENot{} = return e
elimDisjEff e@ELit{} = return e
elimDisjEff EForall{} = error "elimDisjEff: unexpected EForall"


-- Substitution ----------------------------------------------------------------

type Subst = HM.HashMap Var Name

emptySubst :: Subst
emptySubst  = HM.empty

-- | The substitution, but without these names.
without :: Subst -> [Typed Name] -> Subst
without  = foldr (\ (Typed name _) -> HM.delete name)

substVar :: Subst -> Var -> Name
substVar su var = HM.lookupDefault var var su

class HasVars a where
  subst :: Subst -> a -> a

instance HasVars (Pred Name) where
  subst su (Pred p ps) = Pred p (map (substVar su) ps)

instance HasVars Pre where
  subst su = go
    where
    go (PAnd ps)      = pAnd (map go ps)
    go (POr  ps)      = pOr  (map go ps)
    go (PNot p)       = PNot (subst su p)
    go (PLit p)       = PLit (subst su p)
    go (PImp a b)     = PImp (go a) (go b)
    go (PExists ps b) = PExists ps (subst (su `without` ps) b)
    go (PForall ps b) = PForall ps (subst (su `without` ps) b)

instance HasVars Effect where
  subst su = go
    where
    go (EWhen p e)    = EWhen (subst su p) (go e)
    go (EAnd es)      = eAnd (map go es)
    go (ENot p)       = ENot (subst su p)
    go (ELit p)       = ELit (subst su p)
    go (EForall ps e) = EForall ps (subst (su `without` ps) e)
