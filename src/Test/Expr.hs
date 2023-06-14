{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module Test.Expr where

import Control.Applicative
import Data.Functor.HFoldable
import Data.Functor.HFoldable.TH
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Set as Set


--- Datatypes ---


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


--- Recursion ---


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

test :: IO ()
test = do
  print $ eval (Add (LitInt 10) (LitInt 25))
  print $ eval (Add (LitInt 10) (Var "a"))
  print $ eval (And (Eq (LitInt 10) (LitInt 10)) (And (Var "a") (Var "a")))
  print $ freevars (And (Eq (LitInt 10) (LitInt 10)) (And (Var "a") (Var "c")))
  pure ()

