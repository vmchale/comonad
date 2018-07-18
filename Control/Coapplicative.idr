module Control.Coapplicative

import Control.Comonad
import Data.Vect

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
