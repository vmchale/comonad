||| Module providing comonads for idris.
module Control.Comonad

import Data.Vect

%access public export
%default total

infixr 1 =>=
infixr 1 =<=
infixr 1 <<=
infixr 1 =>>

||| A comonad is the categorical dual of a monad. It must satisfy the following
||| laws:
|||
||| ```idris 
||| extend extract      = id
||| extract . extend f  = f
||| extend f . extend g = extend (f . extend g)
||| ```
interface Functor w => Comonad (w : Type -> Type) where
  extract : w a -> a
  extend : (w a -> b) -> w a -> w b
  duplicate : w a -> w (w a)

  -- default implementations
  extend f = map f . duplicate
  duplicate = extend id
  
||| Lift a function into a function on comonadic values.
liftW : (Comonad w) => (f : a -> b) -> (w a -> w b)
liftW f = extend (f . extract)

||| Left-to-right cokleisli composition
(=>=) : (Comonad w) => (w a -> b) -> (w b -> c) -> w a -> c
(=>=) f g = g . extend f

||| Right-to-left cokleisli composition
(=<=) : Comonad w => (w b -> c) -> (w a -> b) -> w a -> c
(=<=) = flip (=>=)

||| Operator giving us 'extend'
(<<=) : Comonad w => (w a -> b) -> w a -> w b
(<<=) = extend

||| Dual to '>>='
(=>>) : Comonad w => w a -> (w a -> b) -> w b
(=>>) = flip extend

Comonad (Pair a) where
  extract = snd
  extend f t = (fst t, f t)

Comonad Stream where
  extract (x::xs) = x
  -- all tails of the initial stream
  duplicate = iterate (drop 1)

Comonad (Vect (S n)) where
  extract = head
  -- all rotations of the initial vector
  duplicate {n} xs = init $ scanl (\(y :: ys),_ => rewrite plusCommutative 1 n in ys ++ [y]) xs xs  