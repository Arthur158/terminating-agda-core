module Agda.Core.Syntax.Context where

import Agda.Core.Syntax.Term (Type)
import Scope.Core (RScope, Scope, rbind, singleton)

data Context = CtxEmpty
             | CtxExtend Context Type

singScope :: Context -> Scope
singScope CtxEmpty = mempty
singScope (CtxExtend g _) = singScope g <> singleton

data Telescope = EmptyTel
               | ExtendTel Type Telescope
                   deriving Show

singTel :: Telescope -> RScope
singTel EmptyTel = mempty
singTel (ExtendTel ty t) = rbind (singTel t)

addTel :: Telescope -> Telescope -> Telescope
addTel EmptyTel tel0 = tel0
addTel (ExtendTel ty s) tel0 = ExtendTel ty (addTel s tel0)

caseTelEmpty :: Telescope -> e -> e
caseTelEmpty EmptyTel f = f

caseTelBind :: Telescope -> (Type -> Telescope -> e) -> e
caseTelBind (ExtendTel a tel) f = f a tel

addContextTel :: Context -> Telescope -> Context
addContextTel c EmptyTel = c
addContextTel c (ExtendTel ty telt)
  = addContextTel (CtxExtend c ty) telt

