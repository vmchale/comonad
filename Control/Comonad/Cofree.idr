-- -------------------------------------- [ Control.Comonad.Cofree.idr ]
-- Module      : Control.Comonad.Cofree
-- Description :
-- --------------------------------------------------------------------- [ EOH ]

||| Cofree comonads; useful for histomorphisms and also recursion
module Control.Comonad.Cofree

import Control.Comonad

%access public export

||| Constructor for a cofree comonad
data Cofree : (f : Type -> Type) -> Type -> Type where
  Co : (a, f (Cofree f a)) -> Cofree f a

||| Typeclass for cofree comonads
public export interface (Functor f, Comonad w) => ComonadCofree (f : Type -> Type) (w : Type -> Type) where
  unwrap : w a -> f (w a)

implementation (Functor f) => Functor (Cofree f) where
  map f m = assert_total $ case m of
    Co (a, as) => Co (f a, map (map f) as)

mutual

  implementation (Functor f) => Comonad (Cofree f) where
    extract (Co (a, _)) = a
    duplicate w = assert_total $ Co (w, map duplicate (unwrap w))

  implementation (Functor f) => ComonadCofree f (Cofree f) where
    unwrap (Co (_, as)) = as

||| Recursion using comonads
unfold : (Functor f) => (g : (b -> (a, f b))) -> b -> Cofree f a
unfold g c = let (x, d) = g c in Co (x, (map (unfold g) d))
