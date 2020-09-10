{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.List (delete, find)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

{- BASIC DEFINITIONS

This section defines the basic constructs we will be working with, namely, the AST
for our tiny language, as well as the definition of what a type and scheme is.
-}

-- Represents what kind of type we use for types
type Ident = String

-- Represents a kind of type variable
type TVar = Ident

-- Represents a kind of variable
type Var = Ident

-- Represents some kind of type we can have, either as an annotation, or a final type
data Type
  = -- A reference to some type variable
    TVar TVar
  | -- The primitive integer type
    TInt
  | -- The primitive string type
    TString
  | -- The function type between two other types
    TFunc Type Type
  deriving (Eq, Show)

-- Represents a scheme, or a polymorphic type
--
-- The idea is that we quantify over variables appearing in the resulting type.
data Scheme = Forall [TVar] Type deriving (Eq, Show)

-- Represents some kind of binary operation between two things
data BinOp = Add | Mul | Concat deriving (Eq, Show)

opType :: BinOp -> Type
opType Add = TInt `TFunc` (TInt `TFunc` TInt)
opType Mul = TInt `TFunc` (TInt `TFunc` TInt)
opType Concat = TString `TFunc` (TString `TFunc` TString)

-- Represents the basic expressions in our language.
--
-- We also have a type parameter `t`, which is used to allow
-- us to have a typed version of the AST
data Expr t
  = -- An Integer litteral
    IntLitt Int
  | -- A String litteral
    StrLitt String
  | -- A reference to a variable name
    Name Var
  | -- Represents the application of some kind of binary operator
    BinOp BinOp (Expr t) (Expr t)
  | -- A function application between two expressions
    Apply (Expr t) (Expr t)
  | -- A lambda introducing a new variable, and producing an expression
    Lambda Var t (Expr t)
  | -- Represents a let expression, binding a variable known to have type t to an expression
    -- and then uses that inside the resulting expression
    Let Var t (Expr t) (Expr t)
  deriving (Eq, Show)

-- Represents a kind of type annotation with no information whatsoever
data Unknown = Unknown deriving (Eq, Show)

-- Represents some kind of type error in our language
data TypeError = TypeMismatch Type Type | InfiniteType TVar Type deriving (Eq, Show)

{- CONSTRAINTS & SUBSTUTITIONS

This section defines the basic aspects of constraints, which are produced by the constraint
generation phase, and then consumed to produce a substitution.
-}

-- Represents some kind of constraint we generate during our gathering phase
--
-- This provides us with information about what certain type variables need to look like,
-- and allows us to eventually produce a valid substitution for these variables
data Constraint
  = -- An assertion that two types must be equal
    SameType Type Type
  | -- An assertion that a type can be seen as an instance of some scheme
    ExplicitlyInstantiates Type Scheme
  | -- An assertion that the first type should be an instance of the second, generalized over some type variables
    ImplicitlyInstantiates Type (Set.Set TVar) Type
  deriving (Eq, Show)

-- Represents a substitution of some type variables for a given type
newtype Subst = Subst (Map.Map TVar Type) deriving (Eq, Show)

instance Semigroup Subst where
  (Subst s1) <> (Subst s2) = Subst (Map.map (subst (Subst s1)) s2 <> s1)

instance Monoid Subst where
  mempty = Subst mempty

-- Create a singleton substitution
singleSubst :: TVar -> Type -> Subst
singleSubst v t = Subst (Map.singleton v t)

-- Represents some kind of type where we can use a substitution
class Substitutable a where
  subst :: Subst -> a -> a

instance (Ord a, Substitutable a) => Substitutable (Set.Set a) where
  subst = Set.map . subst

instance Substitutable TVar where
  subst (Subst s) a = case Map.findWithDefault (TVar a) a s of
    TVar tv -> tv
    _ -> a

instance Substitutable Type where
  subst sub@(Subst s) t = case t of
    TInt -> TInt
    TString -> TString
    TVar a -> Map.findWithDefault (TVar a) a s
    TFunc t1 t2 -> TFunc (subst sub t1) (subst sub t2)

instance Substitutable Scheme where
  subst (Subst s) (Forall vars t) = Forall vars (subst s' t)
    where
      s' = Subst (foldr Map.delete s vars)

instance Substitutable Constraint where
  subst s (SameType t1 t2) = SameType (subst s t1) (subst s t2)
  subst s (ExplicitlyInstantiates t sc) = ExplicitlyInstantiates (subst s t) (subst s sc)
  subst s (ImplicitlyInstantiates t1 vars t2) = ImplicitlyInstantiates (subst s t1) (subst s vars) (subst s t2)

-- A class used to calculate the free type variables in some type
class FreeTypeVars a where
  ftv :: a -> Set.Set TVar

instance FreeTypeVars Type where
  ftv TInt = Set.empty
  ftv TString = Set.empty
  ftv (TVar a) = Set.singleton a
  ftv (TFunc t1 t2) = Set.union (ftv t1) (ftv t2)

instance FreeTypeVars TVar where
  ftv = Set.singleton

instance FreeTypeVars Scheme where
  ftv (Forall vars t) = Set.difference (ftv t) (Set.fromList vars)

instance (Ord a, FreeTypeVars a) => FreeTypeVars (Set.Set a) where
  ftv = foldMap ftv

-- This is a class allowing us to detect which variables are important in a constraint, or sequence of them
class ActiveTypeVars a where
  atv :: a -> Set.Set TVar

instance ActiveTypeVars Constraint where
  atv (SameType t1 t2) = Set.union (ftv t1) (ftv t2)
  atv (ExplicitlyInstantiates t sc) = Set.union (ftv t) (ftv sc)
  atv (ImplicitlyInstantiates t1 vars t2) = Set.union (ftv t1) (Set.intersection (ftv vars) (ftv t2))

instance ActiveTypeVars a => ActiveTypeVars [a] where
  atv = foldMap atv

{- INFERENCE

This is the section defining the main context in which we'll perform inference
-}

-- This is the context in which we perform our type checking
--
-- We have access to a set of bound type variables, as well as the ability to throw errors,
-- and a source of fresh type variables
newtype Infer a = Infer (ReaderT (Set.Set TVar) (StateT Int (Except TypeError)) a)
  deriving (Functor, Applicative, Monad, MonadReader (Set.Set TVar), MonadError TypeError)

runInfer :: Infer a -> Either TypeError a
runInfer (Infer m) = runExcept (fst <$> runStateT (runReaderT m Set.empty) 0)

-- Generate a fresh type containing a type variable
fresh :: Infer TVar
fresh = Infer $ do
  count <- get
  put (count + 1)
  return ("$" <> show count)

-- Instantiate some type scheme by supplying a fresh set of variables for all the bound variables
instantiate :: Scheme -> Infer Type
instantiate (Forall vars t) = do
  newVars <- mapM (const fresh) vars
  let sub = foldMap (uncurry singleSubst) (zip vars (map TVar newVars))
  return (subst sub t)

-- Generalize a type into a scheme by closing over all variables appearing in the type not bound elsewhere
generalize :: Set.Set TVar -> Type -> Scheme
generalize free t = Forall as t
  where
    as = Set.toList (Set.difference (ftv t) free)

-- Extend the inference context with a certain bound type variable
withCtx :: TVar -> Infer a -> Infer a
withCtx a (Infer m) = Infer (local (Set.insert a) m)

{- CONSTRAINT GENERATION -}

-- Represents an ordered collection of assumptions we've gathered so far
newtype Assumption = Assumption {assumptions :: [(Var, Type)]} deriving (Show, Semigroup, Monoid)

-- Remove the assumptions associated with some variable
removeAssumption :: Var -> Assumption -> Assumption
removeAssumption v (Assumption as) = Assumption (filter ((/= v) . fst) as)

-- An assumption about a single type
singleAssumption :: Var -> Type -> Assumption
singleAssumption v t = Assumption [(v, t)]

-- Extend an assumption with a single variable and type pair
extendAssumption :: Var -> Type -> Assumption -> Assumption
extendAssumption v t as = singleAssumption v t <> as

-- Lookup all of the types associated with a certain variable
lookupAssumption :: Var -> Assumption -> [Type]
lookupAssumption target (Assumption as) = [t | (v, t) <- as, v == target]

-- Infer the assumptions and constraints for an expression
infer :: Expr t -> Infer (Assumption, [Constraint], Type)
infer expr = case expr of
  IntLitt _ -> return (mempty, [], TInt)
  StrLitt _ -> return (mempty, [], TString)
  Name v -> do
    tv <- TVar <$> fresh
    return (singleAssumption v tv, [], tv)
  Lambda v _ e -> do
    a <- fresh
    let tv = TVar a
    (as, cs, t) <- withCtx a (infer e)
    return (removeAssumption v as, [SameType t' tv | t' <- lookupAssumption v as] <> cs, TFunc tv t)
  Apply e1 e2 -> do
    (as1, cs1, t1) <- infer e1
    (as2, cs2, t2) <- infer e2
    tv <- TVar <$> fresh
    return (as1 <> as2, [SameType t1 (TFunc t2 tv)] <> cs1 <> cs2, tv)
  Let v _ e1 e2 -> do
    (as1, cs1, t1) <- infer e1
    (as2, cs2, t2) <- infer e2
    bound <- ask
    return (removeAssumption v (as1 <> as2), [ImplicitlyInstantiates t' bound t1 | t' <- lookupAssumption v as2] <> cs1 <> cs2, t2)
  BinOp op e1 e2 -> do
    (as1, cs1, t1) <- infer e1
    (as2, cs2, t2) <- infer e2
    tv <- TVar <$> fresh
    let u1 = t1 `TFunc` (t2 `TFunc` tv)
        u2 = opType op
    return (as1 <> as2, [SameType u1 u2] <> cs1 <> cs2, tv)

{- CONSTRAINT SOLVER -}

-- Solve a set of constraints by inferring a substitution
solve :: [Constraint] -> Infer Subst
solve [] = return mempty
solve cs = solve' (nextSolvable cs)
  where
    nextSolvable :: [Constraint] -> (Constraint, [Constraint])
    nextSolvable xs = case find solvable (chooseOne xs) of
      Just c -> c
      _ -> error "Couldn't find solvable constraint"
      where
        chooseOne xs = [(x, ys) | x <- xs, let ys = delete x xs]
        solvable (SameType _ _, _) = True
        solvable (ExplicitlyInstantiates _ _, _) = True
        solvable (ImplicitlyInstantiates t1 bound t2, cs) =
          Set.null (Set.intersection (atv cs) (Set.difference (ftv t2) bound))
    solve' :: (Constraint, [Constraint]) -> Infer Subst
    solve' (constraint, cs) = case constraint of
      SameType t1 t2 -> do
        su1 <- unify t1 t2
        su2 <- solve (map (subst su1) cs)
        return (su2 <> su1)
      ImplicitlyInstantiates t1 bound t2 -> solve (ExplicitlyInstantiates t1 (generalize bound t2) : cs)
      ExplicitlyInstantiates t sc -> do
        sc' <- instantiate sc
        solve (SameType t sc' : cs)

unify :: Type -> Type -> Infer Subst
unify t1 t2 | t1 == t2 = return mempty
unify (TVar a) t = bind a t
unify t (TVar a) = bind a t
unify (TFunc t1 t2) (TFunc t3 t4) = do
  su1 <- unify t1 t3
  su2 <- unify (subst su1 t2) (subst su1 t4)
  return (su2 <> su1)
unify t1 t2 = throwError (TypeMismatch t1 t2)

bind :: TVar -> Type -> Infer Subst
bind a t
  | t == TVar a = return mempty
  | Set.member a (ftv t) = throwError (InfiniteType a t)
  | otherwise = return (singleSubst a t)
