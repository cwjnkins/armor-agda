{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Strings.VisibleString.TCB
import      Aeres.Data.X690-DER.TLV.Properties as TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Definitions.NonMalleable.Base
open import Aeres.Prelude

module Aeres.Data.X690-DER.Strings.VisibleString.Properties where

open Aeres.Grammar.Definitions                   UInt8
open Aeres.Grammar.Definitions.NonMalleable.Base UInt8
open VisibleStringValue using (size)

@0 unambiguous : Unambiguous VisibleStringValue
unambiguous (mkVisibleStringValue chars range refl) (mkVisibleStringValue .chars range₁ refl) =
  case All.irrelevant (inRange-unique{A = ℕ}{B = UInt8}) range range₁ of λ where
    refl → refl

@0 nonmalleable : NonMalleable VisibleStringValue RawVisibleStringValue
NonMalleable.unambiguous nonmalleable = unambiguous
NonMalleable.injective nonmalleable (fst , mkVisibleStringValue chars range refl) (fst₁ , mkVisibleStringValue chars₁ range₁ refl) refl =
  case All.irrelevant (inRange-unique{A = ℕ}{B = UInt8}) range range₁ of λ where
    refl → refl

sizeUnique : ∀ {@0 bs} → (a₁ a₂ : VisibleStringValue bs) → size a₁ ≡ size a₂
sizeUnique (mkVisibleStringValue chars range refl) (mkVisibleStringValue .chars range₁ refl) = refl

instance
  VisibleStringEq : Eq (Exists─ (List UInt8) VisibleStringValue)
  Eq._≟_ VisibleStringEq (─ ._ , mkVisibleStringValue chars₁ range₁ refl) (─ ._ , mkVisibleStringValue chars₂ range₂ refl) =
    case chars₁ ≟ chars₂ of λ where
      (no ¬p) → no λ where refl → contradiction refl ¬p
      (yes refl) →
        case ‼ All.irrelevant{P = InRange{A = ℕ}{B = UInt8} 32 127} (inRange-unique{A = ℕ}{B = UInt8}) range₁ range₂
        ret (const _)
        of λ where
          refl → yes refl

@0 nonmalleableVisibleString : NonMalleable VisibleString RawVisibleString
nonmalleableVisibleString = TLV.nonmalleable nonmalleable
