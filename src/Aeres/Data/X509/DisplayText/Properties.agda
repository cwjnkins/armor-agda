{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.Unicode.UTF8
open import Aeres.Data.Unicode.UTF16
open import Aeres.Data.X509.DisplayText.TCB
open import Aeres.Data.X690-DER.Strings
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.SequenceOf
import      Aeres.Grammar.DSum
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Prelude
open import Data.List
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.DisplayText.Properties where

open Aeres.Data.X509.DisplayText.TCB.DisplayText 

open Aeres.Grammar.DSum        UInt8
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

@0 nonempty : NonEmpty DisplayText
nonempty{bs} (ia5String v _ ()) refl
nonempty{bs} (visibleString v _ ()) refl
nonempty{bs} (bmpString v _ ()) refl
nonempty{bs} (utf8String v _ ()) refl

@0 nonnesting : NonNesting DisplayText
nonnesting {xs₁ = []} {xs₂ = xs₂} xs₁++ys₁≡xs₂++ys₂ a₁ a₂ = contradiction refl (nonempty a₁)
nonnesting {xs₁ = x ∷ xs₁} {xs₂ = []} xs₁++ys₁≡xs₂++ys₂ a₁ a₂ = contradiction refl (nonempty a₂)
nonnesting {xs₁ = _ ∷ xs₁} {xs₂ = _ ∷ xs₂} xs₁++ys₁≡xs₂++ys₂ (ia5String v b refl) (ia5String v' b' refl) =
  TLV.nonnesting xs₁++ys₁≡xs₂++ys₂ v v'
nonnesting {xs₁ = _ ∷ xs₁} {xs₂ = _ ∷ xs₂} xs₁++ys₁≡xs₂++ys₂ (ia5String v b refl) (visibleString v' b' refl) =
  contradiction (∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂) (λ ())
nonnesting {xs₁ = _ ∷ xs₁} {xs₂ = x₁ ∷ xs₂} xs₁++ys₁≡xs₂++ys₂ (ia5String v b refl) (bmpString v' b' refl) =
  contradiction (∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂) (λ ())
nonnesting {xs₁ = _ ∷ xs₁} {xs₂ = x₁ ∷ xs₂} xs₁++ys₁≡xs₂++ys₂ (ia5String v b refl) (utf8String v' b' refl) =
  contradiction (∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂) (λ ())

nonnesting {xs₁ = _ ∷ xs₁} {xs₂ = x₁ ∷ xs₂} xs₁++ys₁≡xs₂++ys₂ (visibleString v b refl) (ia5String v' b' refl) =
  contradiction (∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂) (λ ())
nonnesting {xs₁ = _ ∷ xs₁} {xs₂ = x₁ ∷ xs₂} xs₁++ys₁≡xs₂++ys₂ (visibleString v b refl) (visibleString v' b' refl) =
  TLV.nonnesting xs₁++ys₁≡xs₂++ys₂ v v'
nonnesting {xs₁ = _ ∷ xs₁} {xs₂ = x₁ ∷ xs₂} xs₁++ys₁≡xs₂++ys₂ (visibleString v b refl) (bmpString v' b' refl) =
  contradiction (∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂) (λ ())
nonnesting {xs₁ = _ ∷ xs₁} {xs₂ = x₁ ∷ xs₂} xs₁++ys₁≡xs₂++ys₂ (visibleString v b refl) (utf8String v' b' refl) =
  contradiction (∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂) (λ ())

nonnesting {xs₁ = _ ∷ xs₁} {xs₂ = x₁ ∷ xs₂} xs₁++ys₁≡xs₂++ys₂ (bmpString v b refl) (ia5String v' b' refl) =
  contradiction (∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂) (λ ())
nonnesting {xs₁ = _ ∷ xs₁} {xs₂ = x₁ ∷ xs₂} xs₁++ys₁≡xs₂++ys₂ (bmpString v b refl) (visibleString v' b' refl) =
  contradiction (∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂) (λ ())
nonnesting {xs₁ = _ ∷ xs₁} {xs₂ = x₁ ∷ xs₂} xs₁++ys₁≡xs₂++ys₂ (bmpString v b refl) (bmpString v' b' refl) =
  TLV.nonnesting xs₁++ys₁≡xs₂++ys₂ v v'
nonnesting {xs₁ = _ ∷ xs₁} {xs₂ = x₁ ∷ xs₂} xs₁++ys₁≡xs₂++ys₂ (bmpString v b refl) (utf8String v' b' refl) =
  contradiction (∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂) (λ ())

nonnesting {xs₁ = _ ∷ xs₁} {xs₂ = x₁ ∷ xs₂} xs₁++ys₁≡xs₂++ys₂ (utf8String v b refl) (ia5String v' b' refl) =
  contradiction (∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂) (λ ())
nonnesting {xs₁ = _ ∷ xs₁} {xs₂ = x₁ ∷ xs₂} xs₁++ys₁≡xs₂++ys₂ (utf8String v b refl) (visibleString v' b' refl) =
  contradiction (∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂) (λ ())
nonnesting {xs₁ = _ ∷ xs₁} {xs₂ = x₁ ∷ xs₂} xs₁++ys₁≡xs₂++ys₂ (utf8String v b refl) (bmpString v' b' refl) =
  contradiction (∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂) (λ ())
nonnesting {xs₁ = _ ∷ xs₁} {xs₂ = x₁ ∷ xs₂} xs₁++ys₁≡xs₂++ys₂ (utf8String v b refl) (utf8String v' b' refl) =
  TLV.nonnesting xs₁++ys₁≡xs₂++ys₂ v v'

@0 noconfusionTLV
  : ∀ {t} {@0 A} → t ∉ Tag.IA5String ∷ Tag.VisibleString ∷ Tag.BMPString ∷ [ Tag.UTF8String ]
    → NoConfusion (TLV t A) DisplayText
noconfusionTLV{t}{A} t∉ {xs₂ = _ ∷ xs₂}xs₁++ys₁≡xs₂++ys₂ v (ia5String s b refl) =
  TLV.noconfusion (t∉ ∘ here) xs₁++ys₁≡xs₂++ys₂ v s
noconfusionTLV{t}{A} t∉ {xs₂ = _ ∷ xs₂}xs₁++ys₁≡xs₂++ys₂ v (visibleString s b refl) =
  TLV.noconfusion (t∉ ∘ there ∘ here) xs₁++ys₁≡xs₂++ys₂ v s
noconfusionTLV{t}{A} t∉ {xs₂ = _ ∷ xs₂}xs₁++ys₁≡xs₂++ys₂ v (bmpString s b refl) =
  TLV.noconfusion (t∉ ∘ there ∘ there ∘ here) xs₁++ys₁≡xs₂++ys₂ v s
noconfusionTLV{t}{A} t∉ {xs₂ = _ ∷ xs₂}xs₁++ys₁≡xs₂++ys₂ v (utf8String s b refl) =
  TLV.noconfusion (t∉ ∘ there ∘ there ∘ there ∘ here) xs₁++ys₁≡xs₂++ys₂ v s

@0 noconfusionSeq : ∀ {@0 A} → NoConfusion (Seq A) DisplayText
noconfusionSeq =
  noconfusionTLV pf
  where
  pf : Tag.Sequence  ∉ _
  pf (there (there (there (there ()))))

@0 unambiguous : Unambiguous DisplayText
unambiguous{xs = _ ∷ xs} (ia5String v b refl) (ia5String v' b' refl) =
  case (‼ TLV.unambiguous IA5String.unambiguous v v') ret (const _) of λ where
    refl → case inRange-unique{A = ℕ}{B = ℕ} b b' ret (const _) of λ where
      refl → refl
unambiguous{xs = _ ∷ xs} (ia5String v b refl) (visibleString v' b' ())
unambiguous{xs = _ ∷ xs} (ia5String v b refl) (bmpString v' b' ())
unambiguous{xs = _ ∷ xs} (ia5String v b refl) (utf8String v' b' ())

unambiguous{xs = _ ∷ xs} (visibleString v b refl) (visibleString v' b' refl) =
  case (‼ TLV.unambiguous VisibleString.unambiguous v v') ret (const _) of λ where
    refl →
      case inRange-unique{A = ℕ}{B = ℕ} b b' ret (const _) of λ where
        refl → refl
unambiguous{xs = _ ∷ xs} (visibleString v b refl) (ia5String  v' b' ())
unambiguous{xs = _ ∷ xs} (visibleString v b refl) (bmpString  v' b' ())
unambiguous{xs = _ ∷ xs} (visibleString v b refl) (utf8String v' b' ())

unambiguous{xs = _ ∷ xs} (bmpString v b refl) (bmpString v' b' refl) =
  case (‼ TLV.unambiguous (IList.unambiguous UTF16.BMP.unambiguous UTF16.BMP.nonempty UTF16.BMP.nonnesting) v v') ret (const _) of λ where
    refl →
      case inRange-unique{A = ℕ}{B = ℕ} b b' ret (const _) of λ where
        refl → refl
  where
  open import Aeres.Grammar.IList UInt8
unambiguous{xs = _ ∷ xs} (bmpString v b refl) (ia5String v' b' ())
unambiguous{xs = _ ∷ xs} (bmpString v b refl) (visibleString v' b' ())
unambiguous{xs = _ ∷ xs} (bmpString v b refl) (utf8String v' b' ())

unambiguous{xs = _ ∷ xs} (utf8String v b refl) (utf8String v' b' refl) =
  case (‼ TLV.unambiguous UTF8.unambiguous v v') ret (const _) of λ where
    refl →
      case inRange-unique{A = ℕ}{B = ℕ} b b' ret (const _) of λ where
        refl → refl
unambiguous{xs = _ ∷ xs} (utf8String v b refl) (ia5String v' b' ())
unambiguous{xs = _ ∷ xs} (utf8String v b refl) (bmpString v' b' ())
unambiguous{xs = _ ∷ xs} (utf8String v b refl) (visibleString v' b' ())

instance
  DisplayTextEq : Eq (Exists─ _ DisplayText)
  Eq._≟_ DisplayTextEq (─ bs₁ , ia5String v₁ r₁ l≡₁) (─ bs₂ , ia5String v₂ r₂ l≡₂) =
    case (─ bs₁ , v₁) ≟ (─ bs₂ , v₂) ret (const _) of λ where
      (no ¬p) → no λ where refl → contradiction refl ¬p
      (yes refl) → 
        case (inRange-unique{A = ℕ}{B = ℕ} r₁ r₂ ,′e ‼ ≡-unique l≡₁ l≡₂) ret (const _) of λ where
          (refl , refl) → yes refl
  Eq._≟_ DisplayTextEq (─ bs₁ , ia5String v₁ r₁ l≡₁) (─ bs₂ , bmpString v₂ r₂ l≡₂) =
    no λ ()
  Eq._≟_ DisplayTextEq (─ bs₁ , ia5String v₁ r₁ l≡₁) (─ bs₂ , visibleString v₂ r₂ l≡₂) =
    no λ ()
  Eq._≟_ DisplayTextEq (─ bs₁ , ia5String v₁ r₁ l≡₁) (─ bs₂ , utf8String v₂ r₂ l≡₂) =
    no λ ()

  Eq._≟_ DisplayTextEq (─ bs₁ , bmpString v₁ r₁ l≡₁) (─ bs₂ , ia5String v₂ r₂ l≡₂) =
    no λ ()
  Eq._≟_ DisplayTextEq (─ bs₁ , bmpString v₁ r₁ l≡₁) (─ bs₂ , bmpString v₂ r₂ l≡₂) =
    case (─ bs₁ , v₁) ≟ (─ bs₂ , v₂) ret (const _) of λ where
      (no ¬p) → no λ where refl → contradiction refl ¬p
      (yes refl) → 
        case (inRange-unique{A = ℕ}{B = ℕ} r₁ r₂ ,′e ‼ ≡-unique l≡₁ l≡₂) ret (const _) of λ where
          (refl , refl) → yes refl
  Eq._≟_ DisplayTextEq (─ bs₁ , bmpString v₁ r₁ l≡₁) (─ bs₂ , visibleString v₂ r₂ l≡₂) =
    no λ ()
  Eq._≟_ DisplayTextEq (─ bs₁ , bmpString v₁ r₁ l≡₁) (─ bs₂ , utf8String v₂ r₂ l≡₂) =
    no λ ()

  Eq._≟_ DisplayTextEq (─ bs₁ , visibleString v₁ r₁ l≡₁) (─ bs₂ , ia5String v₂ r₂ l≡₂) =
    no λ ()
  Eq._≟_ DisplayTextEq (─ bs₁ , visibleString v₁ r₁ l≡₁) (─ bs₂ , bmpString v₂ r₂ l≡₂) =
    no λ ()
  Eq._≟_ DisplayTextEq (─ bs₁ , visibleString v₁ r₁ l≡₁) (─ bs₂ , visibleString v₂ r₂ l≡₂) =
    case (─ bs₁ , v₁) ≟ (─ bs₂ , v₂) ret (const _) of λ where
      (no ¬p) → no λ where refl → contradiction refl ¬p
      (yes refl) → 
        case (inRange-unique{A = ℕ}{B = ℕ} r₁ r₂ ,′e ‼ ≡-unique l≡₁ l≡₂) ret (const _) of λ where
          (refl , refl) → yes refl
  Eq._≟_ DisplayTextEq (─ bs₁ , visibleString v₁ r₁ l≡₁) (─ bs₂ , utf8String v₂ r₂ l≡₂) =
    no λ ()

  Eq._≟_ DisplayTextEq (─ bs₁ , utf8String v₁ r₁ l≡₁) (─ bs₂ , ia5String v₂ r₂ l≡₂) =
    no λ ()
  Eq._≟_ DisplayTextEq (─ bs₁ , utf8String v₁ r₁ l≡₁) (─ bs₂ , bmpString v₂ r₂ l≡₂) =
    no λ ()
  Eq._≟_ DisplayTextEq (─ bs₁ , utf8String v₁ r₁ l≡₁) (─ bs₂ , visibleString v₂ r₂ l≡₂) =
    no λ ()
  Eq._≟_ DisplayTextEq (─ bs₁ , utf8String v₁ r₁ l≡₁) (─ bs₂ , utf8String v₂ r₂ l≡₂) =
    case Eq._≟_ (TLV.eqTLV ⦃ UTF8.UTF8Eq ⦄) (─ bs₁ , v₁) (─ bs₂ , v₂) ret (const _) of λ where
      (no ¬p) → no λ where refl → contradiction refl ¬p
      (yes refl) → 
        case (inRange-unique{A = ℕ}{B = ℕ} r₁ r₂ ,′e ‼ ≡-unique l≡₁ l≡₂) ret (const _) of λ where
          (refl , refl) → yes refl

  eq≋ : Eq≋ DisplayText
  eq≋ = Eq⇒Eq≋ it
