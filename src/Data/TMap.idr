module Data.TMap

data Expr : Type where

data ExprMap : Type -> Type where

emptyEM : ExprMap v

lookupEM : Expr -> ExprMap v -> Maybe v

XT : Type -> Type
XT x = Maybe x -> Maybe x

alterEM : Expr -> XT v -> ExprMap v -> ExprMap v






