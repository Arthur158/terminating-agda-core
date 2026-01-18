module Agda.Core.TCM.Instances where

import Agda.Core.TCM.TCM (TCM(MkTCM, runTCM))

fmapTCM :: (a -> b) -> TCM a -> TCM b
fmapTCM f = MkTCM . fmap (fmap f) . \ r -> runTCM r

liftA2TCM :: (a -> b -> c) -> TCM a -> TCM b -> TCM c
liftA2TCM g ta tb
  = MkTCM (\ e -> g <$> runTCM ta e <*> runTCM tb e)

pureTCM :: a -> TCM a
pureTCM = MkTCM . const . Right

bindTCM :: TCM a -> (a -> TCM b) -> TCM b
bindTCM ma mf
  = MkTCM
      (\ f ->
         do v <- runTCM ma f
            runTCM (mf v) f)

instance Functor TCM where
    fmap = fmapTCM
    (<$) = \ x -> fmapTCM (\ b -> x)

instance Applicative TCM where
    pure = pureTCM
    (<*>)
      = \ ta tb -> MkTCM (\ e -> id <$> runTCM ta e <*> runTCM tb e)
    (<*)
      = \ ta tb ->
          MkTCM (\ e -> (\ z _ -> z) <$> runTCM ta e <*> runTCM tb e)
    (*>)
      = \ ta tb ->
          MkTCM (\ e -> (\ _ z -> z) <$> runTCM ta e <*> runTCM tb e)

instance Monad TCM where
    (>>=)
      = \ ma mf ->
          MkTCM
            (\ f ->
               do v <- runTCM ma f
                  runTCM (mf v) f)
    return = pureTCM
    (>>)
      = \ x y ->
          MkTCM
            (\ f ->
               do v <- runTCM x f
                  runTCM y f)

