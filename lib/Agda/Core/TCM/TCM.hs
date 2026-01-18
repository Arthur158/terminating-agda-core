module Agda.Core.TCM.TCM where

import Agda.Core.Prelude (Fuel)
import Agda.Core.Syntax.Signature (Signature)

type TCError = String

data TCEnv = MkTCEnv{tcSignature :: Signature, tcFuel :: Fuel}

data TCM a = MkTCM{runTCM :: TCEnv -> Either TCError a}

tcmFuel :: TCM Fuel
tcmFuel = MkTCM (Right . (\ x -> x) . \ r -> tcFuel r)

tcmSignature :: TCM Signature
tcmSignature = MkTCM (Right . \ r -> tcSignature r)

tcError :: TCError -> TCM a
tcError = MkTCM . const . Left

assert :: Bool -> TCError -> TCM ()
assert False e = tcError e
assert True e = MkTCM (const (Right ()))

liftEither :: Either TCError a -> TCM a
liftEither (Left e) = MkTCM (\ f -> Left e)
liftEither (Right v) = MkTCM (\ f -> Right v)

liftMaybe :: Maybe a -> TCError -> TCM a
liftMaybe Nothing e = MkTCM (\ f -> Left e)
liftMaybe (Just x) e = MkTCM (\ f -> Right x)

