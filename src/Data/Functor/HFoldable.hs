{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module Data.Functor.HFoldable where

import Data.Kind (Type)
import Control.Monad ((<=<))

type f ~> g = forall a. f a -> g a

type family HBase (h :: k -> Type) :: (k -> Type) -> (k -> Type)

type NatM m f g = forall a. f a -> m (g a)

type HAlgebra h f = h f ~> f
type HAlgebraM m h f = NatM m (h f) f

type HCoalgebra h f = f ~> h f
type HCoalgebraM m h f = NatM m f (h f)

class HFunctor (h :: (k -> Type) -> (k -> Type)) where
  hfmap :: (f ~> g) -> (h f ~> h g)

class HFunctor h => HFoldable (h :: (k -> Type) -> (k -> Type)) where
  hfoldMap :: Monoid m => (forall b. f b -> m) -> h f a -> m

class HFoldable h => HTraversable (h :: (k -> Type) -> (k -> Type))  where
  htraverse :: Applicative e => NatM e f g -> NatM e (h f) (h g)

class HFunctor (HBase h) => HRecursive (h :: k -> Type) where
  hproject :: h ~> (HBase h) h

  hcata :: HAlgebra (HBase h) f -> h ~> f
  hcata algebra = algebra . hfmap (hcata algebra) . hproject

class HFunctor (HBase h) => HCorecursive (h :: k -> Type) where
  hembed :: (HBase h) h ~> h

  hana :: (f ~> (HBase h) f) -> f ~> h
  hana coalgebra = hembed . hfmap (hana coalgebra) . coalgebra

hhylo :: HFunctor f => HAlgebra f b -> HCoalgebra f a -> a ~> b
hhylo f g = f . hfmap (hhylo f g) . g

hcataM :: (Monad m, HTraversable (HBase h), HRecursive h) => HAlgebraM m (HBase h) f -> h a -> m (f a)
hcataM f = f <=< htraverse (hcataM f) . hproject

hanaM :: (Monad m, HTraversable (HBase h), HCorecursive h) => HCoalgebraM m (HBase h) f -> f a -> m (h a)
hanaM f = fmap hembed . htraverse (hanaM f) <=< f

hhyloM :: (HTraversable t, Monad m) => HAlgebraM m t h -> HCoalgebraM m t f -> f a -> m (h a)
hhyloM f g = f <=< htraverse(hhyloM f g) <=< g
