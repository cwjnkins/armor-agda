{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.HashAlg.RFC4055
open import Aeres.Data.X509.MaskGenAlg.RFC4055.TCB
import      Aeres.Data.X509.MaskGenAlg.TCB.OIDs as OIDs
open import Aeres.Data.X690-DER.Null
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.MaskGenAlg.RFC4055.Properties where

open Aeres.Grammar.Definitions UInt8

@0 unambiguous : Unambiguous MGF1
unambiguous =
  TLV.unambiguous
    (DefinedByOID.unambiguous MGF1Params
      (λ o →
        case _≋?_ (TLV.val o) OIDs.MGF1
        ret (λ o∈? → Unambiguous (MGF1Params' o o∈?))
        of λ where
          (no ¬p) → λ ()
          (yes p) → λ a₁ a₂ → ‼ RFC4055.unambiguous a₁ a₂))

@0 nonmalleable : NonMalleable RawMGF1
nonmalleable =
  DefinedByOID.nonmalleable MGF1Params _ {R = RawMGF1Params}
    (λ {bs}{o}{bs₁}{bs₂} →
      case _≋?_ (TLV.val o) OIDs.MGF1
      ret (λ o∈? → (p₁ : MGF1Params' o o∈? bs₁) (p₂ : MGF1Params' o o∈? bs₂)
                 → toRawMGF1Param o o∈? p₁ ≡ toRawMGF1Param o o∈? p₂
                 → _≡_{A = Exists─ _ (MGF1Params' o o∈?)} (─ bs₁ , p₁) (─ bs₂ , p₂))
      of λ where
        (no ¬p) → λ ()
        (yes p) → λ p₁ p₂ eq →
          ‼ (RFC4055.nonmalleable p₁ p₂ eq))

instance
  eq≋ : Eq≋ (DefinedByOIDFields MGF1Params)
  eq≋ = DefinedByOID.eq≋ MGF1Params (λ o
    → case _≋?_ (TLV.val o) OIDs.MGF1
      ret (λ o∈? → Eq≋ (MGF1Params' o o∈?))
      of λ where
        (no ¬p) → record { _≋?_ = λ () }
        (yes p) → it)

