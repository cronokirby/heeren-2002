{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
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
data BinOp = Add | Mul | Concat

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
    BinOp (Expr t) (Expr t)
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
data TypeError = TypeError deriving (Eq, Show)

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

-- Represents a substitution of some type variables for a given type
newtype Subst = Subst (Map.Map TVar Type) deriving (Eq, Show, Semigroup, Monoid)

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

-- Generate a fresh type containing a type variable
fresh :: Infer Type
fresh = Infer $ do
  count <- get
  put (count + 1)
  return (TVar ("$" <> show count))

-- Instantiate some type scheme by supplying a fresh set of variables for all the bound variables
instantiate :: Scheme -> Infer Type
instantiate (Forall vars t) = do
  newVars <- mapM (const fresh) vars
  let sub = foldMap (uncurry singleSubst) (zip vars newVars)
  return (subst sub t)

-- Generalize a type into a scheme by closing over all variables appearing in the type not bound elsewhere
generalize :: Set.Set TVar -> Type -> Scheme
generalize free t = Forall as t
  where
    as = Set.toList (Set.difference (ftv t) free)

{- CONSTRAINT GENERATION -}

-- Represents an ordered collection of assumptions we've gathered so far
newtype Assumption = Assumption {assumptions :: [(Var, Type)]} deriving (Semigroup, Monoid)

-- Remove the assumptions associated with some variable
removeAssumption :: Var -> Assumption -> Assumption
removeAssumption v (Assumption as) = Assumption (filter ((/= v) . fst) as)

-- An assumption about a single type
singleAssumption :: Var -> Type -> Assumption
singleAssumption v t = Assumption [(v, t)]

-- Extend an assumption with a single variable and type pair
extendAssumption :: Var -> Type -> Assumption -> Assumption
extendAssumption v t as = singleAssumption v t <> as
