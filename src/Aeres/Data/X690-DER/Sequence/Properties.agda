{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Default
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X690-DER.Sequence.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Seq         UInt8

module _ {A : @0 List UInt8 → Set} ⦃ _ : Eq≋ A ⦄ {@0 bs' : List UInt8} (default : A bs') where

  @0 nosubstringsDefault₁
    : ∀ {B} → NoSubstrings A → NoSubstrings B → NoConfusion A B
      → NoSubstrings (&ₚ (Default A default) B)
  nosubstringsDefault₁ ns₁ ns₂ nc xs₁++ys₁≡xs₂++ys₂ (mk&ₚ (mkDefault oa₁ nd₁) b₁ bs≡₁) (mk&ₚ (mkDefault oa₂ nd₂) b₂ bs≡₂) =
    Seq.nosubstringsOption₁ ns₁ ns₂ nc xs₁++ys₁≡xs₂++ys₂ (mk&ₚ oa₁ b₁ bs≡₁) (mk&ₚ oa₂ b₂ bs≡₂)

  @0 unambiguousDefault₁
    : ∀ {B} → Unambiguous A → NoSubstrings A → Unambiguous B → NoConfusion A B
      → Unambiguous (&ₚ (Default A default) B)
  unambiguousDefault₁ ua₁ ns₁ ua₂ nc (mk&ₚ (mkDefault oa₁ nd₁) b₁ bs≡₁) (mk&ₚ (mkDefault oa₂ nd₂) b₂ bs≡₂) =
    case Seq.unambiguousOption₁ ua₁ ns₁ ua₂ nc (mk&ₚ oa₁ b₁ bs≡₁) (mk&ₚ oa₂ b₂ bs≡₂)
    ret (const _)
    of λ where
      refl → case ‼ Default.uniqueNotDefault default oa₁ nd₁ nd₂ ret (const _) of λ where
        refl → refl
