module Agda.Core.Syntax.Signature where

import Agda.Core.Syntax.Context (Telescope)
import Agda.Core.Syntax.Substitute (Subst(SNil), Substitute(subst), extSubst)
import Agda.Core.Syntax.Term (Sort, Term, TermS, Type)
import Scope.In (Index)

data Constructor = Constructor{conIndTel :: Telescope,
                               conIx :: TermS}
                     deriving Show

instConIx :: Constructor -> TermS -> TermS -> TermS
instConIx con tPars tInd
  = subst (extSubst (extSubst SNil tPars) tInd) (conIx con)

data Datatype = Datatype{dataSort :: Sort, dataParTel :: Telescope,
                         dataIxTel :: Telescope, dataConstructors :: [Index]}
                  deriving Show

data SigDefinition = FunctionDef Term

data Signature = Signature{sigData :: Index -> Datatype,
                           sigDefs :: Index -> (Type, SigDefinition),
                           sigCons :: Index -> Index -> Constructor}

getType :: Signature -> Index -> Type
getType sig x = subst SNil (fst defs)
  where
    defs :: (Type, SigDefinition)
    defs = sigDefs sig x

getDefinition :: Signature -> Index -> SigDefinition
getDefinition sig x = snd defs
  where
    defs :: (Type, SigDefinition)
    defs = sigDefs sig x

getBody :: Signature -> Index -> Term
getBody sig x
  = case getDefinition sig x of
        FunctionDef body -> body

data Defn = FunctionDefn Term
          | DatatypeDefn Datatype
          | ConstructorDefn Constructor
              deriving Show

data Definition = Definition{defName :: String, defType :: Type,
                             theDef :: Defn}
                    deriving Show

