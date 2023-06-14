# hkrs

hkrs (Higher Kinded Recursion Schemes) is a library that implements recursion schemes for GADTS that
are indexed by a custom type.

```haskell
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module Test.Expr where

import Data.Functor.HFoldable
import Data.Functor.HFoldable.TH
import Data.Text (Text)
import Control.Applicative


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

$(makeBaseFunctor ''Exp)


--- Do Recursion :)  ---


data Value (ix :: Ty) where
    VInt  :: Integer -> Value Number
    VBool :: Bool -> Value Boolean
    VNone :: Value ix

deriving instance Show (Value ix)

eval :: Exp a -> Value a
eval = hcata $ \case
  AddF (VInt x) (VInt y) -> VInt (x + y)
  SubF (VInt x) (VInt y) -> VInt (x - y)
  EqF x y -> case (x,y) of
    (VInt l, VInt r) -> VBool (l == r)
    (VBool l, VBool r) -> VBool (l == r)
    _ -> VNone
  AndF (VBool x) (VBool y) -> VBool (x && y)
  LitIntF n -> VInt n
  _ -> VNone


test :: IO ()
test = do
  print $ eval (Add (LitInt 10) (LitInt 25))
  print $ eval (Add (LitInt 10) (Var "a"))
  -- TODO: this should be (VBool True) but currently evals to VNone...
  print $ eval (And (Eq (LitInt 10) (LitInt 10)) (And (Var "a") (Var "a")))
  pure ()
```
