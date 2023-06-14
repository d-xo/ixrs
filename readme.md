# ixrs

ixrs (Indexed Recursion Schemes) is a library that implements recursion schemes for single parameter GADTs. The GADT can be indexed by a custom kind.

This kind of structure is very convenient when implementing compilers and programming languages as
it enables the easy construction of type safe ASTs. Existing libraries either do not support this
pattern (recursion-schemes, yaya) or are highly complex and not well maintained (multirec,
compdata).

This library offers a simple and convenient interface, does not require modification of your core
AST type at all, and uses template haskell to generate all required datatypes and instance
declarations.

When compared to the canonical `recursion-schemes` library, the only additional boilerplate is the
requirement to sometimes use the `Const` and `Identity` functors when implementing algebras.

For an introduction to (non indexed) recursion schemes the [series at
sumtypeofway](https://blog.sumtypeofway.com/posts/introduction-to-recursion-schemes.html) is
excellent, and for an indepth explanation of the indexed variant used here, the [post by tim philip
williams](http://www.timphilipwilliams.com/posts/2013-01-16-fixing-gadts.html) is also highly
recomended.

The code in the `Data.Functor.HFoldable` in this repo is very lightly modified from the presentation
in the blog post from Tim Philip Williams, tweaked only to take advantage of PolyKinds.

## Tutorial


### Required Extensions

If you wish to make use of the template haskell facilities, you will need the following language
pragmas:

```haskell
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ApplicativeDo #-}
```

For the tutorial we will additionally enable some extra ones and import a few modules:

```haskell
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module Main where

import Data.Functor.HFoldable
import Data.Functor.HFoldable.TH
import Data.Text (Text)
import Control.Applicative
```

Now we can define our language and derive all the required instances to start making use of
recursion schemes:

```haskell
data Ty
  = Boolean
  | Number

data Exp (t :: Ty) where
  Var :: Text -> Exp t
  LitInt :: Integer -> Exp Number
  LitBool :: Bool -> Exp Boolean
  Add :: Exp Number -> Exp Number -> Exp Number
  Sub :: Exp Number -> Exp Number -> Exp Number
  Eq  :: Exp t -> Exp t -> Exp Boolean
  And :: Exp Boolean -> Exp Boolean -> Exp Boolean

deriving instance (Show (Exp a))
$(makeBaseFunctor ''Exp)
```

Thats it! Now we can start to write some algebras :)

```haskell
-- | Gather all free variables in the AST
freevars :: Exp a -> Set Text
freevars = getConst . hcata go
  where
    -- since we want to return an unindexed type, we have to use the
    -- `Const` functor when defining our algebra
    go :: ExpF (Const (Set Text)) a -> Const (Set Text) a
    go = \case
      (VarF n) -> Const $ Set.singleton n
      r -> Const $ hfoldMap getConst r

-- | Evaluates an expression down to it's most concrete form
eval :: Exp a -> Exp a
eval = hcata $ \case
  AddF (LitInt x) (LitInt y) -> LitInt (x + y)
  SubF (LitInt x) (LitInt y) -> LitInt (x - y)
  EqF x y -> case (x,y) of
    (LitInt l, LitInt r) -> LitBool (l == r)
    (LitBool l, LitBool r) -> LitBool (l == r)
    (Var l, Var r) -> LitBool (l == r)
    _ -> Eq x y
  AndF (LitBool x) (LitBool y) -> LitBool (x && y)
  LitIntF n -> LitInt n
  LitBoolF n -> LitBool n
  e -> hembed e

main :: IO ()
main = do
  print $ eval (Add (LitInt 10) (LitInt 25))
  print $ eval (Add (LitInt 10) (Var "a"))
  print $ eval (And (Eq (LitInt 10) (LitInt 10)) (And (Var "a") (Var "a")))
  print $ freevars (And (Eq (LitInt 10) (LitInt 10)) (And (Var "a") (Var "c")))
```

## Template Haskell

The template haskell splice will generate roughly the following:

```haskell
-- | Pattern Functor for Exp
data ExpF (r :: Ty -> Type) (t :: Ty) where
  VarF :: Text -> ExpF r t
  LitIntF :: Integer -> ExpF r Number
  LitBoolF :: Bool -> ExpF r Boolean
  AddF :: r Number -> r Number -> ExpF r Number
  SubF :: r Number -> r Number -> ExpF r Number
  EqF  :: r t -> r t -> ExpF r Boolean
  AndF :: r Boolean -> r Boolean -> ExpF r Boolean

-- | Declare ExpF as the pattern functor for Exp
type instance HBase Exp = ExpF

-- | HFunctor
instance HFunctor ExpF where
  hfmap f = \case
    AddF l r -> AddF (f l) (f r)
    SubF l r -> SubF (f l) (f r)
    EqF l r -> EqF (f l) (f r)
    AndF l r -> AndF (f l) (f r)
    LitIntF i -> LitIntF i
    LitBoolF i -> LitBoolF i
    VarF t -> VarF t

-- | HFoldable
instance HFoldable ExpF where
  hfoldMap f = \case
    AddF l r -> f l <> f r
    SubF l r -> f l <> f r
    EqF l r -> f l <> f r
    AndF l r -> f l <> f r
    LitIntF _ -> mempty
    LitBoolF _ -> mempty
    VarF _ -> mempty

-- | HTraversable
instance HTraversable ExpF where
  htraverse f = \case
    AddF l r -> liftA2 AddF (f l) (f r)
    SubF l r -> liftA2 SubF (f l) (f r)
    EqF l r -> liftA2 EqF (f l) (f r)
    AndF l r -> liftA2 AndF (f l) (f r)
    LitIntF i -> pure (LitIntF i)
    LitBoolF i -> pure (LitBoolF i)
    VarF n -> pure (VarF n)

-- | Project Exp to ExpF
instance HRecursive Exp where
  hproject = \case
    Add x y -> AddF x y
    Sub x y -> SubF x y
    Eq x y -> EqF x y
    And x y -> AndF x y
    LitInt n -> LitIntF n
    LitBool n -> LitBoolF n
    Var n -> VarF n

-- | Project ExpF to Exp
instance HCorecursive Exp where
  hembed = \case
    AddF x y -> Add x y
    SubF x y -> Sub x y
    EqF x y -> Eq x y
    AndF x y -> And x y
    LitIntF n -> LitInt n
    LitBoolF n -> LitBool n
    VarF n -> Var n
```
