{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module Test.Expr() where

import Data.Functor.HFoldable
import Data.Text (Text)
import Data.Kind

--- Datatypes ---

data Ty
  = Boolean
  | Number

data Exp (t :: Ty) where
  Var :: Text -> Exp t
  LitInt :: Integer -> Exp Number
  Add :: Exp Number -> Exp Number -> Exp Number
  Sub :: Exp Number -> Exp Number -> Exp Number
  Eq  :: Exp t -> Exp t -> Exp Boolean
  And :: Exp Boolean -> Exp Boolean -> Exp Boolean

--- Define Pattern Functor ---

data ExpF (r :: Ty -> Type) (t :: Ty) where
  VarF :: Text -> ExpF r t
  LitIntF :: Integer -> ExpF r Number
  AddF :: r Number -> r Number -> ExpF r Number
  SubF :: r Number -> r Number -> ExpF r Number
  EqF  :: r t -> r t -> ExpF r Boolean
  AndF :: r Boolean -> r Boolean -> ExpF r Boolean

instance HFunctor ExpF where
  hfmap f = \case
    AddF l r -> AddF (f l) (f r)
    SubF l r -> SubF (f l) (f r)
    EqF l r -> EqF (f l) (f r)
    AndF l r -> AndF (f l) (f r)
    LitIntF i -> LitIntF i
    VarF t -> VarF t

instance HFoldable ExpF where
  hfoldMap f = \case
    AddF l r -> f l <> f r
    SubF l r -> f l <> f r
    EqF l r -> f l <> f r
    AndF l r -> f l <> f r
    LitIntF _ -> mempty
    VarF _ -> mempty

instance HTraversable ExpF where
  htraverse f = \case
    AddF l r -> liftA2 AddF (f l) (f r)
    SubF l r -> liftA2 SubF (f l) (f r)
    EqF l r -> liftA2 EqF (f l) (f r)
    AndF l r -> liftA2 AndF (f l) (f r)
    LitIntF i -> pure (LitIntF i)
    VarF n -> pure (VarF n)

--- Link Pattern Functor to Main Type ---

type instance HBase Exp = ExpF

instance HRecursive Exp where
  hproject = \case
    Add x y -> AddF x y
    Sub x y -> SubF x y
    Eq x y -> EqF x y
    And x y -> AndF x y
    LitInt n -> LitIntF n
    Var n -> VarF n

instance HCorecursive Exp where
  hembed = \case
    AddF x y -> Add x y
    SubF x y -> Sub x y
    EqF x y -> Eq x y
    AndF x y -> And x y
    LitIntF n -> LitInt n
    VarF n -> Var n
