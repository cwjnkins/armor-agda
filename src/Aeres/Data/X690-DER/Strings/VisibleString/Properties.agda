{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Strings.VisibleString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
open import Aeres.Prelude

module Aeres.Data.X690-DER.Strings.VisibleString.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.IList       UInt8

@0 unambiguous : Unambiguous VisibleStringValue
unambiguous (mkVisibleStringValue chars range refl) (mkVisibleStringValue .chars range₁ refl) =
  case All.irrelevant (inRange-unique{A = ℕ}{B = UInt8}) range range₁ of λ where
    refl → refl

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
