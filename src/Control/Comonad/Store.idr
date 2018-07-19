module Control.Comonad.Store

import public Control.Monad.Identity
import public Control.Comonad.Trans

%access public export
%default total

||| Computations which support local position information via `pos` and `peek`.
||| Laws:
|||
||| - `pos (extend _ x) = pos x`
||| - `peek (pos x) x = extract x`
interface Comonad w => ComonadStore s (w : Type -> Type) | w where
  ||| Read the current position
  pos : w a -> s
  ||| Read the value at the specified position in the specified context
  peek : s -> w a -> a

||| The store comonad transformer.
record StoreT (s : Type) (w : Type -> Type) (a : Type) where
  constructor MkStoreT 
  runStoreT : (w (s -> a),  s)

Functor w => Functor (StoreT s w) where
  map f (MkStoreT (w, s)) = MkStoreT (map (\h => f . h) w, s) -- ((\h => h . f) <$> w, s)

Comonad w => Comonad (StoreT s w) where
  extract (MkStoreT (w, s)) = extract w s
  extend f (MkStoreT (w, s)) = MkStoreT ((\w', s' => f $ MkStoreT (w', s')) <<= w, s)

Comonad w => ComonadStore s (StoreT s w) where
  pos (MkStoreT (f, s)) = s
  peek s (MkStoreT (f, _)) = extract f s  

ComonadTrans (StoreT s) where
  lower (MkStoreT (w, s)) = (\f => f s) <$> w    

||| Extract a collection of values from positions which depend on the current position.
experiment : ComonadStore s w => Functor f => (s -> f s) -> w a -> f a
experiment f x = flip peek x <$> f (pos x)

||| Extract a value from a position which depends on the current position.
peeks : ComonadStore s w => (s -> s) -> w a -> a
peeks f x = peek (f $ pos x) x

||| Reposition the focus at the specified position.
seek : ComonadStore s w => s -> w a -> w a
seek s = peek s . duplicate

||| Reposition the focus at the specified position, which depends on the current position.
seeks : ComonadStore s w => (s -> s) -> w a -> w a
seeks f = peeks f . duplicate  

Store : (s : Type) -> Type -> Type
Store s = StoreT s Identity

||| Unwrap a value in the `Store` comonad.
runStore : Store s a -> (s -> a, s)
runStore (MkStoreT (fid, s)) = (runIdentity fid, s)

||| Create a value in context in the `Store` comonad.
store : (s -> a) -> s -> Store s a
store f x = MkStoreT (Id f, x)
