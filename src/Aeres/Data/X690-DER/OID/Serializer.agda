{-# OPTIONS --subtyping #-}

open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.TLV
open import Aeres.Prelude

module Aeres.Data.X690-DER.OID.Serializer where

serializeSub : ∀ {@0 bs} → OIDSub bs → Singleton bs
serializeSub (mkOIDSub lₚ lₚ≥128 lₑ lₑ<128 leastDigs bs≡) =
  singleton _ (sym bs≡)

serialize : ∀ {@0 bs} → OID bs → Singleton bs
serialize = TLV.serialize (serializeNonEmptySequenceOf serializeSub)
