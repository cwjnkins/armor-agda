{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Equality where

open Base256
open import Aeres.Grammar.Definitions Dig
open import Aeres.Data.X509.Properties

module _ where
  open Generic

  seqElems≟ : ∀ {A} → Decidable-≋ A → Decidable-≋ (SeqElems A)
  seqElems≟ eq? (x ∷[]) (x₁ ∷[]) =
    case eq? x x₁ of λ where
      (no  x≢) → no λ where
        ≋-refl → contradiction ≋-refl x≢
      (yes ≋-refl) → yes ≋-refl
  seqElems≟ eq? (x ∷[]) (cons x₁) = no λ where (mk≋ refl ())
  seqElems≟ eq? (cons x) (x₁ ∷[]) = no λ where (mk≋ refl ())
  seqElems≟ eq? (cons (mkSeqElems h t refl)) (cons{bs'} (mkSeqElems h₁ t₁ bs≡₁)) =
    case eq? h h₁ of λ where
      (no  h≢) → no λ where
        ≋-refl → contradiction ≋-refl h≢
      (yes ≋-refl) →
        case seqElems≟ eq? t t₁ of λ where
          (no  t≢) → no λ where
            ≋-refl → contradiction ≋-refl t≢
          (yes ≋-refl) →
            yes (‼ (case bs≡₁ ret (λ x → cons (mkSeqElems h t refl) ≋ cons (mkSeqElems h t x)) of λ where
              refl → ≋-refl))

  minrep! : ∀ b bs → Unique (Length.MinRep b bs)
  minrep! b [] = ≤-irrelevant
  minrep! b (x ∷ bs) tt tt = refl

  length≟ : Decidable-≋ Length
  length≟ (Length.short (Length.mkShort l l<128 refl)) (Length.short (Length.mkShort l₁ l<129 refl))
    with l ≟ l₁
  ... | no  l≢ = no λ where
    (mk≋ refl refl) → contradiction refl l≢
  ... | yes refl
    with ‼ ≤-irrelevant l<128 l<129
  ... | refl = yes ≋-refl
  length≟ (Length.short x) (Length.long x₁) = no λ where (mk≋ refl ())
  length≟ (Length.long x) (Length.short x₁) = no λ where (mk≋ refl ())
  length≟ (Length.long (Length.mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl)) (Length.long (Length.mkLong l₁ l>129 lₕ₁ lₕ≢1 lₜ₁ lₜLen₁ lₕₜMinRep₁ refl))
    with l ≟ l₁
  ... | no  l≢ = no λ where
    ≋-refl → contradiction refl l≢
  ... | yes refl
    with ‼ ≤-irrelevant l>128 l>129
  ... | refl
    with lₕ ≟ lₕ₁
  ... | no  lₕ≢ = no λ where
    ≋-refl → contradiction refl lₕ≢
  ... | yes refl
    with ‼ ≤-irrelevant lₕ≢0 lₕ≢1
  ... | refl
    with lₜ ≟ lₜ₁
  ... | no  lₜ≢ = no λ where
    ≋-refl → contradiction refl lₜ≢
  ... | yes refl
    with ‼ ≡-unique lₜLen lₜLen₁
  ... | refl
    with ‼ minrep! _ _ lₕₜMinRep lₕₜMinRep₁
  ... | refl = yes ≋-refl

  tlv≟ : ∀ t {A} → Decidable-≋ A → Decidable-≋ (TLV t A)
  tlv≟ t {A} eq? (mkTLV{l = l}{v = v} len val len≡ refl) (mkTLV{l = l₁}{v = v₁} len₁ val₁ len≡₁ refl) =
    case length≟ len len₁ of λ where
      (no  len≢) → no λ where
        (mk≋ tlv≡ a≡) → ‼
          let @0 l≡ : l ≡ l₁
              l≡ = NonNesting.LengthNN (∷-injectiveʳ tlv≡) len len₁
          in
          case l≡ of λ where
            refl →
              contradiction (mk≋ refl (Unambiguous.LengthUA len len₁)) len≢
      (yes ≋-refl) →
        case eq? val val₁ of λ where
          (no  val≢) → no λ where
            (mk≋ tlv≡ a≡) → ‼
              let @0 v≡ : v ≡ v₁
                  v≡ = ++-cancelˡ (t ∷ l) tlv≡
              in
              case v≡ of λ where
                refl → case ‼ ≡-unique len≡ len≡₁ ret _ of λ where
                  refl → ‼
                    let @0 a≡' : mkTLV{t}{A}{l = l}{v} len val len≡ refl ≡ mkTLV{t}{A}{l = l}{v} len val₁ len≡ refl
                        a≡' = trans₀ (≡-elimₖ (λ eq → _ ≡ subst (TLV t A) eq _) refl tlv≡) a≡
                    in
                    contradiction (mk≋ refl (‼ (case a≡' ret _ of λ where refl → ‼ refl))) val≢
          (yes ≋-refl) →
            yes (mk≋ refl
              (subst₀ (λ x → mkTLV _ _ _ _ ≡ mkTLV _ _ x _) (‼ ≡-unique len≡ len≡₁) refl))

  oidLeastDigs! : ∀ bs → Unique (OIDLeastDigs bs)
  oidLeastDigs! [] tt tt = refl
  oidLeastDigs! (x ∷ bs) = ≤-irrelevant

  oidsub≟ : Decidable-≋ OIDSub
  oidsub≟ (mkOIDSub lₚ lₚ≥128 lₑ lₑ<128 leastDigs bs≡) (mkOIDSub lₚ₁ lₚ≥129 lₑ₁ lₑ<129 leastDigs₁ bs≡₁)
    with lₚ ≟ lₚ₁
  ... | no  lₚ≢ = no λ where
    ≋-refl → contradiction refl lₚ≢
  ... | yes refl
    with ‼ All.irrelevant ≤-irrelevant lₚ≥128 lₚ≥129
  ... | refl
    with lₑ ≟ lₑ₁
  ... | no lₑ≢ = no λ where
    ≋-refl → contradiction refl lₑ≢
  ... | yes refl
    with ‼ ≤-irrelevant lₑ<128 lₑ<129
  ... | refl
    with ‼ oidLeastDigs! lₚ leastDigs leastDigs₁
  ... | refl
    with ‼ bs≡
    |    ‼ bs≡₁
  ... | refl | refl
    with ‼ ≡-unique bs≡ bs≡₁
  ... | refl = yes ≋-refl

