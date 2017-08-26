-- -------------------------------------- [ Control.Comonad.Cofree.idr ]
-- Module      : Data.Profunctor.Comonad.Cofree
-- Description : 
-- --------------------------------------------------------------------- [ EOH ]
module Data.Profunctor.Comonad.Cofree

import Control.Comonad

%access export

data Cofree : (f : Type -> Type) -> Type -> Type where
  Co : a -> f (Cofree f a) -> Cofree f a

interface (Functor f, Comonad w) => ComonadCofree (f : Type -> Type) (w : Type -> Type) where
  unwrap : w a -> f (w a)

implementation (Functor f) => Functor (Cofree f) where
  map f m = assert_total $ case m of
    Co a as => Co (f a) (map (map f) as)

implementation (Functor f) => Comonad (Cofree f) where
  extract (Co a _) = a
