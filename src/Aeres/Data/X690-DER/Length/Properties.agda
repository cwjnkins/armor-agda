{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X690-DER.Length.TCB
import      Aeres.Grammar.Definitions
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X690-DER.Length.Properties where

open Base256
open Aeres.Grammar.Definitions UInt8

elimMinRepLong
  : ∀ {ℓ} lₕ lₜ (P : UInt8 → List UInt8 → Set ℓ) →
    (lₜ ≡ [] → toℕ lₕ ≥ 128 → P lₕ lₜ) →
    (lₜ ≢ [] → P lₕ lₜ) →
    MinRepLong lₕ lₜ → P lₕ lₜ
elimMinRepLong lₕ lₜ P pf₁ pf₂ mr
  with lₜ ≟ []
... | no  lₜ≢[] = pf₂ lₜ≢[]
... | yes lₜ≡[] = pf₁ lₜ≡[] mr

uniqueMinRepLong : ∀ {lₕ lₜ} → Unique (MinRepLong lₕ lₜ)
uniqueMinRepLong{lₕ}{lₜ} p₁ p₂
  with lₜ ≟ []
... | no  lₜ≢[] = ⊤-unique p₁ p₂
... | yes lₜ≡[] = ≤-unique p₁ p₂

-- Smart constructors
shortₛ : ∀ l → {@0 _ : True (toℕ l <? 128)} → Length [ l ]
shortₛ l {l<128} = short (mkShort l (toWitness l<128) refl)

mkLongₛ : ∀ l lₕ lₜ →
        {@0 _ : True (128 <? toℕ l)}
        {@0 _ : True (toℕ lₕ >? 0)}
        {@0 _ : True (length lₜ ≟ (toℕ l - 129))}
        {@0 _ : True (lₜ ≠ [] ⊎-dec toℕ lₕ ≥? 128)}
        → Long (l ∷ lₕ ∷ lₜ)
mkLongₛ l lₕ lₜ {l>128} {lₕ≢0} {lₜLen} {mr} =
 (mkLong l
        (toWitness l>128) lₕ
        (toWitness lₕ≢0) lₜ
        (toWitness lₜLen) (go mr) refl)
 where
 go : True (lₜ ≠ [] ⊎-dec toℕ lₕ ≥? 128) → if ⌊ lₜ ≟ [] ⌋ then toℕ lₕ ≥ 128 else ⊤
 go mr
   with toWitness mr
 ... | inj₁ lₜ≢[]
   with lₜ ≟ []
 ... | no  _ = tt
 ... | yes lₜ≡[] = contradiction lₜ≡[] lₜ≢[]
 go mr | inj₂ y
   with lₜ ≟ []
 ... | no _ = tt
 ... | yes lₜ≡[] = y

longₛ : ∀ l lₕ lₜ →
      {@0 _ : True (128 <? toℕ l)}
      {@0 _ : True (toℕ lₕ >? 0)}
      {@0 _ : True (length lₜ ≟ (toℕ l - 129))}
      {@0 _ : True (lₜ ≠ [] ⊎-dec toℕ lₕ ≥? 128)}
          → Length (l ∷ lₕ ∷ lₜ)
longₛ l lₕ lₜ {l>128} {lₕ≢0} {lₜLen} {mr} =
  long (mkLongₛ l lₕ lₜ {l>128} {lₕ≢0} {lₜLen} {mr})

-- examples
_ : Length _
_ = shortₛ (# 3)

_ : Length _
_ = longₛ (# 130) (# 1) [ # 1 ]

@0 unambiguous : Unambiguous Length
unambiguous (short (mkShort l l<128 refl)) (short (mkShort .l l<129 refl)) =
  case ≤-irrelevant l<128 l<129 of λ where
    refl → refl
unambiguous (short (mkShort l l<128 refl)) (long (mkLong l₁ l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep ()))
unambiguous (long (mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl)) (short (mkShort l₁ l<128 ()))
unambiguous (long (mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl)) (long (mkLong .l l>129 .lₕ lₕ≢1 .lₜ lₜLen₁ lₕₜMinRep₁ refl)) =
  case _ × _ × _ × _ ∋ ≤-irrelevant l>128 l>129 , ≤-irrelevant lₕ≢0 lₕ≢1 , ≡-unique lₜLen lₜLen₁ , uniqueMinRepLong lₕₜMinRep lₕₜMinRep₁ of λ where
    (refl , refl , refl , refl) → refl

@0 unambiguous-getLength : ∀ {xs ys} → xs ≡ ys → (l₁ : Length xs) (l₂ : Length ys) → getLength l₁ ≡ getLength l₂
unambiguous-getLength refl l₁ l₂ = cong getLength (unambiguous l₁ l₂)

instance
  Length≋ : Eq≋ Length
  Eq≋._≋?_ Length≋ {bs₁} {bs₂} (short (mkShort l l<128 bs≡)) (short (mkShort l₁ l<129 bs≡₁))
    with l ≟ l₁
  ... | no ¬p = no λ where
    (mk≋ refl refl) → contradiction refl ¬p
  Eq≋._≋?_ Length≋ l₁@(short (mkShort l l<128 refl)) l₂@(short (mkShort .l l<129 refl)) | yes refl =
    yes (mk≋ refl (unambiguous l₁ l₂))
  Eq≋._≋?_ Length≋ {bs₁} {bs₂} (short x) (long x₁) = no λ where (mk≋ refl ())
  Eq≋._≋?_ Length≋ {bs₁} {bs₂} (long x) (short x₁) = no λ where (mk≋ refl ())
  Eq≋._≋?_ Length≋ {bs₁} {bs₂} (long (mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep bs≡)) (long (mkLong l₁ l>129 lₕ₁ lₕ≢1 lₜ₁ lₜLen₁ lₕₜMinRep₁ bs≡₁))
    with l ∷ lₕ ∷ lₜ ≟ l₁ ∷ lₕ₁ ∷ lₜ₁
  ... | no ¬p = no λ where
    (Aeres.Grammar.Definitions.mk≋ refl refl) → contradiction refl ¬p
  Eq≋._≋?_ Length≋ l₁@(long (mkLong l _ _ _ _ _ _ refl)) l₂@(long (mkLong .l _ ._ _ ._ _ _ refl)) | yes refl =
    yes (mk≋ refl (unambiguous l₁ l₂))

@0 nonnesting : NonNesting Length
nonnesting xs₁++ys₁≡xs₂++ys₂ (short (mkShort l l<128 refl)) (short (mkShort l₁ l<129 refl)) =
  cong [_] (∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂)
nonnesting xs₁++ys₁≡xs₂++ys₂ (short (mkShort l l<128 refl)) (long (mkLong l₁ l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl)) =
  contradiction l<128 (<⇒≯ (subst (λ i → 128 < toℕ i) (sym $ ∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂) l>128))
nonnesting xs₁++ys₁≡xs₂++ys₂ (long (mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl)) (short (mkShort l₁ l<128 refl)) =
  contradiction l<128 (<⇒≯ (subst (λ i → 128 < toℕ i)  (∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂) l>128))
nonnesting xs₁++ys₁≡xs₂++ys₂ (long (mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl)) (long (mkLong l₁ l>129 lₕ₁ lₕ≢1 lₜ₁ lₜLen₁ lₕₜMinRep₁ refl)) =
  begin (l ∷ lₕ ∷ lₜ   ≡⟨ cong (_∷ lₕ ∷ lₜ) (‼ l≡) ⟩
        l₁ ∷ lₕ ∷ lₜ   ≡⟨ cong (λ x → l₁ ∷ x ∷ lₜ) (‼ lₕ≡) ⟩
        l₁ ∷ lₕ₁ ∷ lₜ  ≡⟨ cong (λ x → l₁ ∷ lₕ₁ ∷ x) (‼ lₜ≡) ⟩
        l₁ ∷ lₕ₁ ∷ lₜ₁ ∎)
  where
  open ≡-Reasoning

  @0 l≡ : l ≡ l₁
  l≡ = ∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂

  @0 lₕ≡ : lₕ ≡ lₕ₁
  lₕ≡ = ∷-injectiveˡ (∷-injectiveʳ xs₁++ys₁≡xs₂++ys₂)

  @0 lₜ++ys₁≡ : lₜ ++ _ ≡ lₜ₁ ++ _
  lₜ++ys₁≡ = ∷-injectiveʳ (∷-injectiveʳ xs₁++ys₁≡xs₂++ys₂)

  @0 lₜ≡ : lₜ ≡ lₜ₁
  lₜ≡ =
    proj₁ $ Lemmas.length-++-≡ _ _ _ _ lₜ++ys₁≡
              (trans lₜLen (trans (cong (λ x → toℕ x ∸ 129) l≡) (sym lₜLen₁)))
