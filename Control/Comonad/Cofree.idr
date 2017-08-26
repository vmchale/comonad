-- -------------------------------------- [ Control.Comonad.Cofree.idr ]
-- Module      : Data.Profunctor.Comonad.Cofree
-- Description : 
-- --------------------------------------------------------------------- [ EOH ]
module Data.Profunctor.Comonad.Cofree

import Control.Comonad

%access export

data Cofree : (f : Type -> Type) -> (a : Type) -> Type where
  Co : a -> f (Cofree f a) -> Cofree f a

interface (Functor f, Comonad w) => ComonadCofree (f : Type -> Type) (w : Type -> Type) where
  unwrap : w a -> f (w a)
