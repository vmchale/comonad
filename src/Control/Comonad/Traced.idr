module Control.Comonad.Traced

import Control.Monad.Identity
import Control.Comonad.Trans

%access public export
%default total

||| Comonads which support relative (monoidal) position information via `track`.
|||
||| Laws:
|||
||| - `track neutral = extract`
||| - `(track s =<= track t) x = track (s <+> t) x`
interface Comonad w => ComonadTraced t (w : Type -> Type) | w where
  ||| Extracts a value at the specified relative position
  track : t -> w a -> a

record TracedT (t : Type) (w : Type -> Type) (a : Type) where
  constructor MkTracedT 
  runTracedT : w (t -> a)

Functor w => Functor (TracedT t w) where
  map f (MkTracedT w) = MkTracedT ((\g, t => f $ g t) <$> w)

(Comonad w, Monoid t) => Comonad (TracedT t w) where
  extract (MkTracedT w) = extract w neutral
  extend f (MkTracedT w) = MkTracedT ((\w', t => f $ MkTracedT ((\h, t' => h $ t <+> t') <$> w')) <<= w)

Monoid t => ComonadTrans (TracedT t) where
  lower (MkTracedT w) = (\f => f neutral) <$> w  

||| Extracts a value at a relative position which depends on the current value.
tracks : ComonadTraced t w => (a -> t) -> w a -> a
tracks f w = track (f $ extract w) w

||| Get the current position.
listenTr : Functor w => TracedT t w a -> TracedT t w (a, t)
listenTr (MkTracedT tr) = MkTracedT ((\f, t => (f t, t)) <$> tr)

||| Get a value which depends on the current position.
listensTr : Functor w => (t -> b) -> TracedT t w a -> TracedT t w (a, b)
listensTr f (MkTracedT tr) = MkTracedT ((\g, t => (g t, f t)) <$> tr)

||| Apply a function to the current position.
censorTr : Functor w => (t -> t) -> TracedT t w a -> TracedT t w a
censorTr f (MkTracedT tr) = MkTracedT ((\g => g . f) <$> tr)  --(f >>> _)

(Comonad w, Monoid t) => ComonadTraced t (TracedT t w) where
  track t (MkTracedT tr) = extract tr t

Traced : Type -> Type -> Type
Traced m = TracedT m Identity

-- | Unwrap a value in the `Traced` comonad.
runTraced : Traced m a -> m -> a
runTraced (MkTracedT t) = runIdentity t

-- | Create a value in context in the `Traced` comonad.
traced : (m -> a) -> Traced m a
traced = MkTracedT . Id
