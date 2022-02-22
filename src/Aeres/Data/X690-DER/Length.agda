{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Prelude

module Aeres.Data.X690-DER.Length where

open Base256

module Length where
  open import Aeres.Data.X690-DER.TCB.Length public

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

open Length public
  using (Length)
  hiding (module Length)
