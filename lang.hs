{- BASIC DEFINITIONS

This section defines the basic constructs we will be working with, namely, the AST
for our tiny language, as well as the definition of what a type and scheme is.
-}

-- Represents what kind of type we use for types
type Ident = String

-- Represents some kind of type we can have, either as an annotation, or a final type
data Type
  = TVar Ident
  | TInt
  | TString
  | TFunc Type Type
  deriving (Eq, Show)

-- Represents a scheme, or a polymorphic type
--
-- The idea is that we quantify over variables appearing in the resulting type.
data Scheme = Forall [Ident] Type deriving (Eq, Show)

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
    Name Ident
  | -- A function application between two expressions
    Apply (Expr t) (Expr t)
  | -- A lambda introducing a new variable, and producing an expression
    Lambda Ident t (Expr t)
  | -- Represents a let expression, binding a variable known to have type t to an expression
    -- and then uses that inside the resulting expression
    Let Ident t (Expr t) (Expr t)
  deriving (Eq, Show)

-- Represents a kind of type annotation with no information whatsoever
data Unknown = Unknown deriving (Eq, Show)

-- Represents some kind of type error in our language
data TypeError = TypeError deriving (Eq, Show)
