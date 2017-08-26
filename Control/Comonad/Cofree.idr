-- -------------------------------------- [ Control.Comonad.Cofree.idr ]
-- Module      : Data.Profunctor.Comonad.Cofree
-- Description : 
-- --------------------------------------------------------------------- [ EOH ]

||| Cofree comonads; useful for histomorphisms and also recursion
module Data.Profunctor.Comonad.Cofree

import Control.Comonad

%access public export

||| Constructor for a cofree comonad
data Cofree : (f : Type -> Type) -> Type -> Type where
  Co : a -> f (Cofree f a) -> Cofree f a

||| Typeclass for cofree comonads
public export interface (Functor f, Comonad w) => ComonadCofree (f : Type -> Type) (w : Type -> Type) where
  unwrap : w a -> f (w a)

implementation (Functor f) => Functor (Cofree f) where
  map f m = assert_total $ case m of
    Co a as => Co (f a) (map (map f) as)

implementation (Functor f) => Comonad (Cofree f) where
  extract (Co a _) = a

implementation (Functor f) => ComonadCofree f (Cofree f) where
  unwrap (Co _ as) = as

||| Recursion using comonads
unfold : (Functor f) => (g : (b -> (a, f b))) -> b -> Cofree f a
unfold g c = let (x, d) = g c in Co x (map (unfold g) d)
