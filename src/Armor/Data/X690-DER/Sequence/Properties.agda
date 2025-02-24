{-# OPTIONS --erasure #-}
open import Armor.Binary
open import Armor.Data.X690-DER.Default
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X690-DER.Sequence.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Seq         UInt8

module _ {A : @0 List UInt8 → Set} ⦃ _ : Eq≋ A ⦄  {@0 bs' : List UInt8} (default : A bs') where

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

  @0 unambiguousDefaultOption
    : ∀ {B : @0 List UInt8 → Set} → Unambiguous A → NoSubstrings A → NonEmpty A
      → Unambiguous B → NonEmpty B
      → NoConfusion A B
      → Unambiguous (&ₚ (Default A default) (Option B))
  unambiguousDefaultOption ua₁ ns₁ ne₁ ua₂ ne₂ nc (mk&ₚ (mkDefault a₁ nd₁) b₁ bs≡₁) (mk&ₚ (mkDefault a₂ nd₂) b₂ bs≡₂) =
    case Seq.unambiguousOption₂ ua₁ ns₁ ne₁ ua₂ ne₂ nc (mk&ₚ a₁ b₁ bs≡₁) (mk&ₚ a₂ b₂ bs≡₂) ret (const _) of λ where
      refl → case ‼ Default.uniqueNotDefault default a₁ nd₁ nd₂ ret (const _) of λ where
        refl → refl

module _ {B C E F : @0 List UInt8 → Set} ⦃ _ : Eq≋ B ⦄  ⦃ _ : Eq≋ C ⦄ ⦃ _ : Eq≋ E ⦄ ⦃ _ : Eq≋ F ⦄ {@0 bs' bs'' bs''' bs'''' : List UInt8} (default₂ : B bs') (default₃ : C bs'') (default₅ : E bs''') (default₆ : F bs'''') where

  @0 unambiguous₂Option₂Default₄
    : ∀ {A D : @0 List UInt8 → Set}
    → Unambiguous A → NoSubstrings A → NonEmpty A
    → Unambiguous B → NoSubstrings B → NonEmpty B
    → Unambiguous C → NoSubstrings C → NonEmpty C
    → Unambiguous D → NoSubstrings D → NonEmpty D
    → Unambiguous E → NoSubstrings E → NonEmpty E
    → Unambiguous F → NonEmpty F
    → NoConfusion A B → NoConfusion A C → NoConfusion A D → NoConfusion A E → NoConfusion A F
    → NoConfusion B C → NoConfusion B D → NoConfusion B E → NoConfusion B F
    → NoConfusion C D → NoConfusion C E → NoConfusion C F
    → NoConfusion D E → NoConfusion D F
    → NoConfusion E F
    → Unambiguous (&ₚ (Option A) (&ₚ (Default B default₂) (&ₚ(Default C default₃)
                      (&ₚ (Option D) (&ₚ (Default E default₅) (Default F default₆))))))
  unambiguous₂Option₂Default₄ x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃ x₁₄ x₁₅ x₁₆ x₁₇ x₁₈ x₁₉ x₂₀ x₂₁ x₂₂ x₂₃ x₂₄ x₂₅ x₂₆ x₂₇ x₂₈ x₂₉ x₃₀ x₃₁
    (mk&ₚ fstₚ₁ (mk&ₚ (mkDefault value₀ notDefault₀) (mk&ₚ (mkDefault value notDefault) (mk&ₚ fstₚ₇ (mk&ₚ (mkDefault value₁ notDefault₁) (mkDefault value₂ notDefault₂) bs≡₈) bs≡₆) bs≡₄) bs≡₂) bs≡)
    (mk&ₚ fstₚ₂ (mk&ₚ (mkDefault value₃ notDefault₃) (mk&ₚ (mkDefault value₄ notDefault₄) (mk&ₚ fstₚ₈ (mk&ₚ (mkDefault value₅ notDefault₅) (mkDefault value₆ notDefault₆) bs≡₉) bs≡₇) bs≡₅) bs≡₃) bs≡₁) =
    case Seq.unambiguous₂Option₆
           x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃ x₁₄ x₁₅ x₁₆ x₁₇ x₁₈ x₁₉ x₂₀ x₂₁ x₂₂ x₂₃ x₂₄ x₂₅ x₂₆ x₂₇ x₂₈ x₂₉ x₃₀ x₃₁
           (mk&ₚ fstₚ₁ (mk&ₚ value₀ (mk&ₚ value (mk&ₚ fstₚ₇ (mk&ₚ value₁ value₂ bs≡₈) bs≡₆) bs≡₄) bs≡₂) bs≡)
           (mk&ₚ fstₚ₂ (mk&ₚ value₃ (mk&ₚ value₄ (mk&ₚ fstₚ₈ (mk&ₚ value₅ value₆ bs≡₉) bs≡₇) bs≡₅) bs≡₃) bs≡₁)
      ret (const _) of λ where
        refl → case ‼ Default.uniqueNotDefault default₂ value₀ notDefault₀ notDefault₃ ret (const _) of λ where
          refl → case ‼ Default.uniqueNotDefault default₃ value notDefault notDefault₄ ret (const _) of λ where
            refl → case ‼ Default.uniqueNotDefault default₅ value₁ notDefault₁ notDefault₅ ret (const _) of λ where
              refl → case ‼ Default.uniqueNotDefault default₆ value₂ notDefault₂ notDefault₆ ret (const _) of λ where
               refl → refl
