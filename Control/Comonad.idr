||| Module providing comonads for idris.
module Control.Comonad

import Data.Vect

%access public export

infixr 1 =>=
infixr 1 =<=
infixr 1 <<=
infixr 1 =>>
infixl 4 <@>
infixl 4 @>
infixl 4 <@

||| A comonad is the categorical dual of a monad. It must satisfy the following
||| laws:
|||
||| ```idris example
||| extend extract      = id
||| extract . extend f  = f
||| extend f . extend g = extend (f . extend g)
||| ```
interface Functor w => Comonad (w : Type -> Type) where
  extract : w a -> a

  duplicate : w a -> w (w a)

implementation Comonad Stream where
  extract (x::xs) = x
  duplicate = pure

implementation Comonad (Vect (S n)) where
  extract = head
  duplicate = pure

extend : (Comonad w) => (w a -> b) -> w a -> w b
extend f = map f . duplicate

||| Lift a function into a function on comonadic values.
liftW : (Comonad w) => (f : a -> b) -> (w a -> w b)
liftW f = extend (f . extract)

||| Left-to-right cokliesli composition
(=>=) : (Comonad w) => (w a -> b) -> (w b -> c) -> w a -> c
(=>=) f g = g . extend f

||| Right-to-left cokliesli composition
(=<=) : Comonad w => (w b -> c) -> (w a -> b) -> w a -> c
(=<=) = flip (=>=)

||| Operator giving us 'extend'
(<<=) : Comonad w => (w a -> b) -> w a -> w b
(<<=) = extend

||| Dual to '>>='
(=>>) : Comonad w => w a -> (w a -> b) -> w b
(=>>) = flip extend

||| CoApplicatives provide a categorical approach to zippers. They must satisfy
||| the following laws:
|||
||| ```idris example
||| (.) <$> u <@> v <@> w = u <@> (v <@> w)
||| extract (p <@> q) = extract p (extract q)
||| duplicate (p <@> q) = (<@>) <$> duplicate p <@> duplicate q
||| ```
|||
||| If 'w' is an applicative functor, it must further satisfy
|||
||| ```idris example
||| (<@>) = (<*>)
||| ```
interface (Comonad w) => CoApplicative (w : Type -> Type) where
  (<@>) : w (a -> b) -> w a -> w b
  (@>) : w a -> w b -> w b
  (<@) : w a -> w b -> w a

implementation CoApplicative Stream where
  (<@>) = (<*>)
  (@>) _ y = y
  (<@) x _ = x

implementation CoApplicative (Vect (S n)) where
  (<@>) = (<*>)
  (@>) _ y = y
  (<@) x _ = x
