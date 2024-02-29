open import Armor.Binary
open import Armor.Data.X690-DER.Int.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.TLV.Properties as TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
open import Armor.Prelude

module Armor.Data.X690-DER.Int.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8

nonnegUnique : ∀ {bs} (a : Int bs) → Unique (ℤ.NonNegative (getVal a))
nonnegUnique a with getVal a
... | ℤ.+_ _ = ⊤-unique

@0 nonempty : NonEmpty IntegerValue
nonempty (mkIntVal bₕ bₜ minRep val ()) refl

@0 nonemptyNonNegative : NonEmpty NonNegativeInt
nonemptyNonNegative = Parallel.nonempty₁ TLV.nonempty

@0 unambiguousValue : Unambiguous IntegerValue
unambiguousValue (mkIntVal bₕ bₜ minRep val bs≡) (mkIntVal bₕ₁ bₜ₁ minRep₁ val₁ bs≡₁) =
  case (trans (sym bs≡) bs≡₁) ret (const _) of λ where
    refl → case (‼ uniqueSingleton val val₁) ret (const _) of λ where
      refl → case (‼ UInt8.uniqueTwosCompletementMinRep _ _ minRep minRep₁) ret (const _) of λ where
        refl → case (‼ ≡-unique bs≡ bs≡₁) ret (const _) of λ where
          refl → refl

@0 [_]unambiguous : (t : UInt8) → Unambiguous [ t ]Int
[ t ]unambiguous = TLV.unambiguous unambiguousValue

@0 unambiguous : Unambiguous Int
unambiguous = [ _ ]unambiguous

@0 unambiguousNonNegative : Unambiguous NonNegativeInt
unambiguousNonNegative = Parallel.unambiguous unambiguous nonnegUnique

@0 nonmalleableVal : NonMalleable RawIntegerValue
nonmalleableVal{bs₁ = bs₁}{bs₂} i₁@(mkIntVal bₕ₁ bₜ₁ minRep₁ (singleton v₁ v₁≡) bs≡₁) i₂@(mkIntVal bₕ₂ bₜ₂ minRep₂ (singleton v₂ v₂≡) bs≡₂) eq =
  case bs₁≡bs₂ ret (const _) of λ where
    refl → case (‼ unambiguousValue i₁ i₂) ret (const _) of λ where
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
      contradiction minRep₂
        (UInt8.¬twosComplementMinRep
          bₕ₁ bₜ₁ bₕ₂ bₜ₂ bₜ₁<bₜ₂
          (trans (sym v₁≡) (trans eq v₂≡)))
    (tri> _ _ bₜ₂<bₜ₁) →
      contradiction minRep₁
        (UInt8.¬twosComplementMinRep
          bₕ₂ bₜ₂ bₕ₁ bₜ₁ bₜ₂<bₜ₁
          (trans (sym v₂≡) (trans (sym eq) v₁≡)))

  bs₁≡bs₂ : bs₁ ≡ bs₂
  bs₁≡bs₂ = UInt8.twosComplement-injective bs₁ bs₂ len≡ (begin
              twosComplement bs₁ ≡⟨ cong twosComplement bs≡₁ ⟩
              twosComplement (bₕ₁ ∷ bₜ₁) ≡⟨ sym v₁≡ ⟩
              v₁ ≡⟨ eq ⟩
              v₂ ≡⟨ v₂≡ ⟩
              twosComplement (bₕ₂ ∷ bₜ₂) ≡⟨ cong twosComplement (sym bs≡₂) ⟩
              twosComplement bs₂ ∎)

@0 [_]nonmalleable : ∀ t → NonMalleable Raw[ t ]Int
[ t ]nonmalleable = TLV.nonmalleable nonmalleableVal

@0 nonmalleable : NonMalleable RawInt
nonmalleable = [ _ ]nonmalleable

nonNegativeℤ→ℕ-injective :
  ∀ i₁ i₂ (nn₁ : ℤ.NonNegative i₁) (nn₂ : ℤ.NonNegative i₂)
  → nonNegativeℤ→ℕ i₁ nn₁ ≡ nonNegativeℤ→ℕ i₂ nn₂
  → i₁ ≡ i₂
nonNegativeℤ→ℕ-injective (ℤ.+ n₁) (ℤ.+ n₂) _ _ refl = refl

private
  nonnegative-unique : ∀ {i₁} → (nn₁ nn₂ : ℤ.NonNegative i₁) → nn₁ ≡ nn₂
  nonnegative-unique {ℤ.+ n} tt tt = refl

@0 nonmalleableNonNegative : NonMalleable RawNonNegativeInt
nonmalleableNonNegative n₁@(mk×ₚ i₁ i₁≥0) n₂@(mk×ₚ i₂ i₂≥0) eq
  with nm
  where
  nm : (─ _ , i₁) ≡ (─ _ , i₂)
  nm = nonmalleable i₁ i₂
         (nonNegativeℤ→ℕ-injective (getVal i₁) (getVal i₂) i₁≥0 i₂≥0 eq)
... | refl
  with nonnegative-unique i₁≥0 i₂≥0
... | refl = refl

instance
  IntegerValueEq : Eq (Exists─ (List UInt8) IntegerValue)
  Eq._≟_ IntegerValueEq (─ bs₁ , i₁@(mkIntVal bₕ₁ bₜ₁ minRep₁ (singleton v₁ v₁≡) bs≡₁)) (─ bs₂ , i₂@(mkIntVal bₕ₂ bₜ₂ minRep₂ (singleton v₂ v₂≡) bs≡₂)) =
    case v₁ ≟ v₂ ret (const _) of λ where
      (no  v₁≢v₂) → no λ where refl → contradiction refl v₁≢v₂
      (yes refl)  →
        case (‼ nonmalleableVal i₁ i₂ refl) ret (const _) of λ where
          refl → yes refl

  eq≋ : Eq≋ IntegerValue
  eq≋ = Eq⇒Eq≋ it

  NonNegativeIntEq : Eq (Exists─ _ NonNegativeInt)
  NonNegativeIntEq = Parallel.eqΣₚ it (λ a → record { _≟_ = λ x y → yes (nonnegative-unique x y) })

  nneq≋ : Eq≋ NonNegativeInt
  nneq≋ = Eq⇒Eq≋ it
