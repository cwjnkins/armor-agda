{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.TLV.Properties as TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Definitions.NonMalleable
open import Aeres.Prelude

module Aeres.Data.X690-DER.Int.Properties where

open Aeres.Grammar.Definitions              UInt8
open Aeres.Grammar.Definitions.NonMalleable UInt8

module MinRep where
  @0 unique : ∀ {b bs} → Unique (True (Base256.twosComplementMinRep? b bs))
  unique p₁ p₂ = T-unique p₁ p₂

nonempty : NonEmpty IntegerValue
nonempty (mkIntVal bₕ bₜ minRep val ()) refl

@0 unambiguous : Unambiguous IntegerValue
unambiguous (mkIntVal bₕ bₜ minRep val bs≡) (mkIntVal bₕ₁ bₜ₁ minRep₁ val₁ bs≡₁) =
  case (trans (sym bs≡) bs≡₁) ret (const _) of λ where
    refl → case (‼ uniqueSingleton val val₁) ret (const _) of λ where
      refl → case (‼ MinRep.unique minRep minRep₁) ret (const _) of λ where
        refl → case (‼ ≡-unique bs≡ bs≡₁) ret (const _) of λ where
          refl → refl

@0 nonmalleableVal : NonMalleable IntegerValue RawIntegerValue
NonMalleable.unambiguous nonmalleableVal = unambiguous
NonMalleable.injective nonmalleableVal (─ bs₁ , i₁@(mkIntVal bₕ₁ bₜ₁ minRep₁ (singleton v₁ v₁≡) bs≡₁)) (─ bs₂ , i₂@(mkIntVal bₕ₂ bₜ₂ minRep₂ (singleton v₂ v₂≡) bs≡₂)) eq =
  case bs₁≡bs₂ ret (const _) of λ where
    refl → case (‼ unambiguous i₁ i₂) ret (const _) of λ where
      refl → refl
  where
  open ≡-Reasoning
  import Data.Nat.Properties as Nat

  len≡ : length bs₁ ≡ length bs₂
  len≡ = case Nat.<-cmp (length bₜ₁) (length bₜ₂) ret (const _) of λ where
    (tri≈ _ len≡ _) → ‼ (begin
      length bs₁ ≡⟨ cong length bs≡₁ ⟩
      suc (length bₜ₁) ≡⟨ cong suc len≡ ⟩
      suc (length bₜ₂) ≡⟨ cong length (sym bs≡₂) ⟩
      length bs₂ ∎)
    (tri< bₜ₁<bₜ₂ _ _) →
      contradiction (toWitness minRep₂)
        (Base256.¬twosComplementMinRep
          bₕ₁ bₜ₁ bₕ₂ bₜ₂ bₜ₁<bₜ₂
          (trans (sym v₁≡) (trans eq v₂≡)))
    (tri> _ _ bₜ₂<bₜ₁) →
      contradiction (toWitness minRep₁)
        (Base256.¬twosComplementMinRep
          bₕ₂ bₜ₂ bₕ₁ bₜ₁ bₜ₂<bₜ₁
          (trans (sym v₂≡) (trans (sym eq) v₁≡)))

  bs₁≡bs₂ : bs₁ ≡ bs₂
  bs₁≡bs₂ = Base256.twosComplement-injective bs₁ bs₂ len≡ (begin
              Base256.twosComplement bs₁ ≡⟨ cong Base256.twosComplement bs≡₁ ⟩
              Base256.twosComplement (bₕ₁ ∷ bₜ₁) ≡⟨ sym v₁≡ ⟩
              v₁ ≡⟨ eq ⟩
              v₂ ≡⟨ v₂≡ ⟩
              Base256.twosComplement (bₕ₂ ∷ bₜ₂) ≡⟨ cong Base256.twosComplement (sym bs≡₂) ⟩
              Base256.twosComplement bs₂ ∎)

@0 nonmalleable : NonMalleable Int RawInt
nonmalleable = TLV.nonmalleable nonmalleableVal

instance
  IntegerValueEq : Eq (Exists─ (List UInt8) IntegerValue)
  Eq._≟_ IntegerValueEq (─ bs₁ , i₁@(mkIntVal bₕ₁ bₜ₁ minRep₁ (singleton v₁ v₁≡) bs≡₁)) (─ bs₂ , i₂@(mkIntVal bₕ₂ bₜ₂ minRep₂ (singleton v₂ v₂≡) bs≡₂)) =
    case v₁ ≟ v₂ ret (const _) of λ where
      (no  v₁≢v₂) → no λ where refl → contradiction refl v₁≢v₂
      (yes refl)  →
        case (‼ NonMalleable.injective nonmalleableVal (─ _ , i₁) (─ _ , i₂) refl) ret (const _) of λ where
          refl → yes refl

  eq≋ : Eq≋ IntegerValue
  eq≋ = Eq⇒Eq≋ it
