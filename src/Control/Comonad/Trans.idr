module Control.Comonad.Trans

import public Control.Comonad

%access public export

||| `lower (extend w (f <<< lower)) = extend (lower w) f`
interface ComonadTrans (f : (Type -> Type) -> Type -> Type) where
    lower : Comonad w => f w a -> w a


    