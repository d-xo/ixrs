{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module Main where

import Data.Kind (Type)

data Ty
  = Boolean
  | Number

data ExpF (r :: Ty -> Type) (t :: Ty) where
  Add :: r Number -> r Number -> ExpF r Number
  Sub :: r Number -> r Number -> ExpF r Number
  Eq  :: r t -> r t -> ExpF r Boolean
  And :: r Boolean -> r Boolean -> ExpF r Boolean

main :: IO ()
main = putStrLn "Hello, Haskell!"
