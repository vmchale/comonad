module Control.Coapplicative

import Control.Comonad

%access public export
%default total

infixl 3 <@>
infixl 3 @>
infixl 3 <@

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

||| Coapplicative zippers
liftW2 : CoApplicative w => (f : a -> b -> c) -> w a -> w b -> w c
liftW2 f a b = f <$> a <@> b

liftW3 : CoApplicative w => (f : a -> b -> c -> d) -> w a -> w b -> w c -> w d
liftW3 f a b c = f <$> a <@> b <@> c
