{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Val.EC.TCB
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.OctetString
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.EC.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

private
  here' = "X509: PublicKey: Val: EC"

parseECBitString : Parser (Logging ∘ Dec) ECBitString
parseECBitString =
  parse×Dec TLV.nonnesting
    (tell $ here' String.++ ": unused bits field is non-zero")
    parseBitstring
    λ where
      [] → no λ where (mk&ₚ refl sndₚ₁ ())
      (x ∷ x₁) →
        case x ≟ # 0 ret (const _) of λ where
          (yes refl) → yes (mk&ₚ refl self refl)
          (no x≢0) → no λ where (mk&ₚ refl sndₚ₁ refl) → contradiction refl x≢0
