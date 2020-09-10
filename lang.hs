{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}

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
