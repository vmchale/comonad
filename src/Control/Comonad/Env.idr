module Control.Comonad.Env

import Control.Monad.Identity
import Control.Comonad.Trans

%access public export
%default total

||| A comonad which supports a global environment
interface Comonad w => ComonadEnv e (w : Type -> Type) | m where
    ||| Return the environment
    askEnv   : w a -> e
    ||| Allows the value of the local context to be modified for the duration of the execution of action
    localEnv : (e -> e) -> w a -> w a

-- | The environment comonad transformer.
-- |
-- | This comonad transformer extends the context of a value in the base comonad with a _global environment_ of
-- | type `e`.
-- |
-- | The `ComonadEnv` type class describes the operations supported by this comonad.
record EnvT (e : Type) (w : Type -> Type) (a : Type) where
  constructor MkEnvT
  runReaderT : (e, w a)

||| Change the underlying comonad and data type in an `EnvT` context.
mapEnvT : (w1 a -> w2 b) -> EnvT e w1 a -> EnvT e w2 b
mapEnvT f (MkEnvT (e, x)) = MkEnvT (e, f x)

Functor w => Functor (EnvT e w) where
  map f (MkEnvT (e, x)) = MkEnvT (e, f <$> x)

Comonad w => Comonad (EnvT e w) where
  extract (MkEnvT (e, x)) = extract x
  extend f (MkEnvT (e, x)) = MkEnvT (e, f <$> ((MkEnvT . MkPair e) <<= x)) 
  
Comonad w => ComonadEnv e (EnvT e w) where
  askEnv (MkEnvT (x, _)) = x
  localEnv f (MkEnvT (y, z)) = MkEnvT (f y, z)  

ComonadTrans (EnvT e) where
  lower (MkEnvT (_, x)) = x

Foldable f => Foldable (EnvT e f) where
  foldr fn a (MkEnvT (_, x)) = foldr fn a x  

Traversable f => Traversable (EnvT e f) where
  traverse f (MkEnvT (a, x)) = MkEnvT <$> MkPair a <$> traverse f x  

||| Get a value which depends on the environment.
asksEnv : ComonadEnv e1 w => (e1 -> e2) -> w e1 -> e2
asksEnv f x = f (askEnv x)

Env : (e : Type) -> Type -> Type
Env e = EnvT e Identity

||| Unwrap a value in the `Env` comonad.
runEnv : Env e a -> (e, a)
runEnv (MkEnvT (e, x)) = (e, runIdentity x)

||| Create a value in context in the `Env` comonad.
env : e -> a -> Env e a
env e a = MkEnvT $ (e, Id a)
