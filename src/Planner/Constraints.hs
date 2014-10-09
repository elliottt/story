{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp #-}

module Planner.Constraints (
    BindConsts()
  , Domain(..)
  , consistent
  , bindings
  , solve

    -- * Construction
  , empty
  , unify
  , constrain
  , known, unknown
  ) where

import qualified Planner.DiscTrie as T
import           Planner.Monad
import           Planner.Types
                     ( Effect(..), Constraint(..), Pred(..), Term(..), Var(..) )

import           Control.Monad ( MonadPlus, guard, mzero, foldM )
import           Data.Function ( on )
import qualified Data.IntSet as ISet
import qualified Data.IntMap.Strict as IMap
import           Data.List ( sortBy, transpose )
import qualified Data.Set as Set


-- Binding Constraints ---------------------------------------------------------

type Vars         = IMap.IntMap VarInfo
type EquivClasses = IMap.IntMap EquivClass

data BindConsts = BindConsts { bcVars         :: Vars
                             , bcEquivClasses :: EquivClasses
                             , bcNextRef      :: !EquivClassRef
                             } deriving (Show)

data VarInfo = VarInfo { viVar :: !Var
                       , viRef :: !EquivClassRef
                       } deriving (Show)

addVar :: VarInfo -> Vars -> Vars
addVar vi m = IMap.insert (varIndex (viVar vi)) vi m

empty :: BindConsts
empty  = BindConsts { bcVars         = IMap.empty
                    , bcEquivClasses = IMap.empty
                    , bcNextRef      = 0
                    }

class Unify a where
  unify :: a -> a -> BindConsts -> PlanM BindConsts

instance Unify a => Unify [a] where
  unify (a:as) (b:bs) cs = do cs' <- unify a b cs
                              unify as bs cs'

  unify []     []     cs =    return cs

  unify _      _      _  =    mzero

instance Unify Effect where
  unify (EPred p)      (EPred q)      cs =    unify p q cs

  unify (EIntends a p) (EIntends b q) cs = do cs' <- unify a b cs
                                              unify p q cs'

  unify _              _              _  =    mzero

instance Unify Pred where
  unify (Pred n1 p1 ts1) (Pred n2 p2 ts2) cs = do guard (n1 == n2 && p1 == p2)
                                                  unify ts1 ts2 cs

instance Unify Term where
  unify (TCon a) (TCon b) cs | a == b = return cs
  unify (TGen a) (TGen b) cs | a == b = return cs

  unify (TVar a) (TVar b) cs          = unify a b cs
  unify (TVar v) (TCon t) cs          = known v [t] cs
  unify (TCon t) (TVar v) cs          = known v [t] cs

  unify _        _        _           = mzero

instance Unify Var where
  unify a b bc @ BindConsts { .. } =
    case (IMap.lookup (varIndex a) bcVars, IMap.lookup (varIndex b) bcVars) of

      -- both variables exist, merge their classes
      (Just x, Just y)
        | viRef x == viRef y -> return bc
        | otherwise          ->
          do let Just xc = IMap.lookup (viRef x) bcEquivClasses
                 Just yc = IMap.lookup (viRef y) bcEquivClasses

                 mergeRefs vi | viRef vi == viRef y = vi { viRef = viRef x }
                              | otherwise           = vi

             merged <- mergeClasses xc yc
             return BindConsts
               { bcVars         = IMap.map mergeRefs bcVars
               , bcEquivClasses = IMap.delete (viRef y)
                                $ IMap.insert (viRef x) merged bcEquivClasses
               , bcNextRef      = bcNextRef
               }

      -- one variable exists
      (Just ref,Nothing) -> bindVar ref b
      (Nothing,Just ref) -> bindVar ref a

      -- neither variable exists
      (Nothing,Nothing) ->
        do let ec = EquivClass { ecDomain  = DomUnknown
                               , ecMembers = ISet.fromList [ varIndex a
                                                           , varIndex b ]
                               , ecAvoid   = ISet.empty
                               }
           return BindConsts
             { bcVars = addVar (VarInfo a bcNextRef)
                      $ addVar (VarInfo b bcNextRef)
                        bcVars

             , bcEquivClasses = IMap.insert bcNextRef ec bcEquivClasses

             , bcNextRef = bcNextRef + 1
             }

    where

    bindVar ref Var { .. } =
         return BindConsts { bcVars         = IMap.insert varIndex ref bcVars
                           , bcEquivClasses = bcEquivClasses
                           , bcNextRef      = bcNextRef
                           }


neq :: Var -> Var -> BindConsts -> PlanM BindConsts
neq l r bc =
  do let (rl,ecl,bcl) = getClass l bc
         (rr,ecr,bcr) = getClass r bcl

     -- require that the two classes aren't the same
     guard (rl /= rr)

     let ecl' = ecl { ecAvoid = ISet.insert (varIndex r) (ecAvoid ecl) }
         ecr' = ecr { ecAvoid = ISet.insert (varIndex l) (ecAvoid ecr) }

     return bcr { bcEquivClasses = IMap.insert rl ecl'
                                 $ IMap.insert rr ecr'
                                 $ bcEquivClasses bcr }


-- | Add a variable with a known domain.
known :: Var -> [String] -> BindConsts -> PlanM BindConsts
known v vals bc =
  do let (rv,ecv,bcv) = getClass v bc
     dom' <- mergeDomains (ecDomain ecv) (DomKnown (Set.fromList vals))
     let ecv' = ecv { ecDomain = dom' }
     return bcv { bcEquivClasses = IMap.insert rv ecv' (bcEquivClasses bcv) }


-- | For unconstrained variables.
unknown :: Var -> BindConsts -> PlanM BindConsts
unknown v bc =
  do let (_,_,bcv) = getClass v bc
     return bcv


-- | Lookup or create the equivalence class for a variable.
getClass :: Var -> BindConsts -> (EquivClassRef,EquivClass,BindConsts)
getClass v @ Var { .. } bc @ BindConsts { .. } =
  case IMap.lookup varIndex bcVars of

    Just VarInfo { .. } ->
      let Just ec = IMap.lookup viRef bcEquivClasses
       in (viRef,ec,bc)

    Nothing  ->
      let ec  = EquivClass { ecDomain  = DomUnknown
                           , ecMembers = ISet.fromList [ varIndex ]
                           , ecAvoid   = ISet.empty }
          bc' = BindConsts { bcVars         = addVar (VarInfo v bcNextRef) bcVars
                           , bcEquivClasses = IMap.insert bcNextRef ec bcEquivClasses
                           , bcNextRef      = bcNextRef + 1
                           }
       in (bcNextRef,ec,bc')


-- Constraints -----------------------------------------------------------------

-- | Interpret a constraint.
constrain :: Constraint -> BindConsts -> PlanM BindConsts

-- inequalities only make sense between two variables
constrain (CNeq (TVar a) (TVar b)) bc = neq a b bc
constrain (CNeq _        _       ) _  = mzero

constrain (CPred p) bc =
  do facts <- getFacts
     let insts = T.lookup p facts
         dom   = predDomain p insts

     foldM constrainDom bc dom

  where
  constrainDom cs (v,d) =
    do let (ref,ec,cs') = getClass v cs
       dom' <- mergeDomains (ecDomain ec) d
       let ec' = ec { ecDomain = dom' }
       return cs' { bcEquivClasses = IMap.insert ref ec' (bcEquivClasses cs') }


predDomain :: Pred -> [Pred] -> [(Var,Domain)]
predDomain p facts =
  do (TVar v, ts) <- zip (pArgs p) (transpose (map pArgs facts))
     let ts' = [ c | TCon c <- ts ]
         dom | null ts'  = DomUnknown
             | otherwise = DomKnown (Set.fromList ts')
     return (v, dom)


-- Equivalence Classes ---------------------------------------------------------

data Domain = DomUnknown
            | DomKnown (Set.Set String)
              deriving (Show,Eq)

-- | Remove an element from this domain, failing if that renders the domain
-- empty.
domRemove :: String -> Domain -> PlanM Domain
domRemove e (DomKnown es) = do let es' = Set.delete e es
                               guard (not (Set.null es'))
                               return (DomKnown es')
domRemove _ DomUnknown    =    return DomUnknown

-- | Sort of a hack, as it returns maxBound when the domain is unknown.
domainSize :: Domain -> Int
domainSize (DomKnown d) = Set.size d
domainSize DomUnknown   = maxBound

mergeDomains :: MonadPlus m => Domain -> Domain -> m Domain
mergeDomains (DomKnown l) (DomKnown r) = do let es = l `Set.intersection` r
                                            guard (not (Set.null es))
                                            return (DomKnown es)
mergeDomains DomUnknown   r            =    return r
mergeDomains l            _            =    return l


type EquivClassRef = Int

data EquivClass = EquivClass { ecDomain  :: Domain
                             , ecMembers :: ISet.IntSet
                             , ecAvoid   :: ISet.IntSet
                             } deriving (Show)

ecDegree :: EquivClass -> Int
ecDegree EquivClass { .. } = ISet.size ecAvoid

-- | Merge two equivalence classes.
mergeClasses :: MonadPlus m => EquivClass -> EquivClass -> m EquivClass
mergeClasses l r =
  do guard $ ISet.null (ecMembers l `ISet.intersection` ecAvoid r)
          && ISet.null (ecMembers r `ISet.intersection` ecAvoid l)

     dom' <- mergeDomains (ecDomain  l) (ecDomain  r)

     return EquivClass
       { ecDomain  = dom'
       , ecMembers = ISet.union   (ecMembers l) (ecMembers r)
       , ecAvoid   = ISet.union   (ecAvoid   l) (ecAvoid   r)
       }


-- Checking Consistency --------------------------------------------------------

consistent :: BindConsts -> Bool
consistent cs =
  case runPlanM undefined undefined (solve cs) of
    Just _  -> True
    Nothing -> False

bindings :: BindConsts -> [(Var,Domain)]
bindings BindConsts { .. } =
  [ (viVar,ecDomain) | EquivClass { .. } <- IMap.elems bcEquivClasses
                     , var               <- ISet.toList ecMembers
                     , let Just VarInfo { .. } = IMap.lookup var bcVars
                     ]

solve :: BindConsts -> PlanM BindConsts
solve cs0 = loop cs0 (IMap.toList (bcEquivClasses cs0))
  where

  loop cs unbound = case sortUnbound unbound of

    (ref,ec) : rest ->
      do dom'  <- fixDomain (ecDomain ec)

         let ec' = ec { ecDomain = dom' }
         rest' <- forwardChecking ec' rest

         let cs' = cs { bcEquivClasses = IMap.insert ref ec' (bcEquivClasses cs) }

         loop cs' rest'

    [] ->
         return cs


type UnboundVars = [(EquivClassRef,EquivClass)]

sortUnbound :: UnboundVars -> UnboundVars
sortUnbound []   = []
sortUnbound vars = sortBy cmp vars
  where
  cmp (_,ec1) (_,ec2)
      -- order by domain size...
    | domSize /= EQ = domSize

      -- ... and when that fails, order by who has the larger degree.  the two
      -- classes are reversed here, so that larger domains will come first in
      -- the list.
    | otherwise     = (compare `on` ecDegree) ec2 ec1
    where
    domSize = (compare `on` (domainSize . ecDomain)) ec1 ec2


fixDomain :: Domain -> PlanM Domain
fixDomain DomUnknown    =    return DomUnknown
fixDomain (DomKnown ds) = do d <- choose (Set.toList ds)
                             return (DomKnown (Set.singleton d))

forwardChecking :: EquivClass -> UnboundVars -> PlanM UnboundVars
forwardChecking ec =
  case ecDomain ec of
    DomKnown (Set.toList -> [d]) -> mapM (restrictDom (ecAvoid ec) d)
    _                            -> return

restrictDom :: ISet.IntSet -> String -> (EquivClassRef,EquivClass)
            -> PlanM (EquivClassRef,EquivClass)
restrictDom avoid d (r,ecr)

  | ISet.null (ecMembers ecr `ISet.intersection` avoid) =
       return (r,ecr)

  | otherwise =
    do dom' <- domRemove d (ecDomain ecr)
       return (r,ecr { ecDomain = dom' })
