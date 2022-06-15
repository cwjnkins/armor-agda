{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X690-DER.OID.TCB as TCB
open import Aeres.Prelude

module Aeres.Data.X690-DER.OID where

module OID where
  open TCB public
  open import Aeres.Data.X690-DER.OID.Serializer public
  open import Aeres.Data.X690-DER.OID.Properties public

open TCB public hiding
  (LeastBytes; leastBytes?; leastBytesUnique)

mkOIDSubₛ
  : (lₚ : List UInt8) (lₑ : UInt8)
    → {@0 _ : True (All.all ((_≥? 128) ∘ toℕ) lₚ)} {@0 _ : True (OID.leastBytes? lₚ)} {@0 _ : True (lₑ Fin.<? # 128)}
    → OIDSub (lₚ ∷ʳ lₑ)
mkOIDSubₛ lₚ lₑ {lₚ≥128}{leastDigs}{lₑ<128} = mkOIDSub lₚ (toWitness lₚ≥128) lₑ (toWitness lₑ<128) (toWitness leastDigs) refl
