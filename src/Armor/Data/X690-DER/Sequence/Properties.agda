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

module _ {A C : @0 List UInt8 → Set} ⦃ _ : Eq≋ A ⦄  ⦃ _ : Eq≋ C ⦄ {@0 bs' bs'' : List UInt8} (default : A bs') (default₁ : C bs'') where

  @0 nosubstringsDefault₁
    : ∀ {B} → NoSubstrings A → NoSubstrings B → NoConfusion A B
      → NoSubstrings (&ₚ (Default A default) B)
  nosubstringsDefault₁ ns₁ ns₂ nc xs₁++ys₁≡xs₂++ys₂ (mk&ₚ (mkDefault oa₁ nd₁) b₁ bs≡₁) (mk&ₚ (mkDefault oa₂ nd₂) b₂ bs≡₂) =
    Seq.nosubstringsOption₁ ns₁ ns₂ nc xs₁++ys₁≡xs₂++ys₂ (mk&ₚ oa₁ b₁ bs≡₁) (mk&ₚ oa₂ b₂ bs≡₂)

  -- postulate
  --   @0 nosubstringsDefault₂
  --     : NoSubstrings A → NoSubstrings C → NoConfusion A C → NoSubstrings (&ₚ (Default A default) (Default C default₁))
  -- -- nosubstringsDefault₂ nsa nsc ncac eq
  --   -- (mk&ₚ (mkDefault value notDefault) (mkDefault value₁ notDefault₁) bs≡₁)
  --   -- (mk&ₚ (mkDefault value₂ notDefault₂) (mkDefault value₃ notDefault₃) bs≡₃)
  --   -- = {!!}
  --   --   -- Seq.nosubstringsOption₁ nsa nsb ncab eq (mk&ₚ {!!} {!ₚ!} {!!}) (mk&ₚ value₂ {!!} {!!})

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

  @0 unambiguousOptionDefaultDefault
    : ∀ {B} → Unambiguous B → NoSubstrings B → NonEmpty B
    → Unambiguous A → NoSubstrings A → NonEmpty A
    → Unambiguous C → NonEmpty C
    → NoConfusion B A → NoConfusion B C → NoConfusion A C
    → Unambiguous (&ₚ (Option B) (&ₚ (Default A default) (Default C default₁)))
  unambiguousOptionDefaultDefault x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ (mk&ₚ fstₚ₁ (mk&ₚ (mkDefault value notDefault) (mkDefault value₁ notDefault₁) bs≡₂) bs≡)
    (mk&ₚ fstₚ₂ (mk&ₚ (mkDefault value₂ notDefault₂) (mkDefault value₃ notDefault₃) bs≡₃) bs≡₁) =
      case  Seq.unambiguous₂Option₃
        x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ (mk&ₚ fstₚ₁ (mk&ₚ value value₁ bs≡₂) bs≡) (mk&ₚ fstₚ₂ (mk&ₚ value₂ value₃ bs≡₃) bs≡₁)
      ret (const _) of λ where
        refl → case ‼ Default.uniqueNotDefault default value notDefault notDefault₂ ret (const _) of λ where
          refl → case ‼ Default.uniqueNotDefault default₁ value₁ notDefault₁ notDefault₃ ret (const _) of λ where
            refl → refl
