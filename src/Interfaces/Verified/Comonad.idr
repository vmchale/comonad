module Interfaces.Verified.Comonad

import Control.Comonad
import Data.Vect

-- VerifiedFunctor ?
interface Comonad w => VerifiedComonad (w : Type -> Type) where 
  comonadLeftId : (wx : w a) -> (f : w a -> b) -> extract (extend f wx) = f wx
  comonadRightId : (wx : w a) -> extend Comonad.extract wx = wx
  comonadAssoc : (wx : w a) -> (f : w a -> b) -> (g : w b -> c) -> extend g (extend f wx) = extend (g . extend f) wx

VerifiedComonad (Pair a) where
  comonadLeftId (a,b) f = Refl
  comonadRightId (a,b) = Refl
  comonadAssoc (a,b) f g = Refl
