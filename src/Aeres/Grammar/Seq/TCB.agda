{-# OPTIONS --subtyping #-}

import      Aeres.Grammar.Definitions.NonMalleable.Base
open import Aeres.Prelude renaming (Σ to Sigma)

module Aeres.Grammar.Seq.TCB (Σ : Set) where

open Aeres.Grammar.Definitions.NonMalleable.Base Σ

record &ₚᵈ (@0 A : List Σ → Set) (@0 B : {bs₁ : List Σ} → A bs₁ → List Σ → Set) (@0 bs : List Σ) : Set where
  constructor mk&ₚ
  field
    @0 {bs₁ bs₂} : List Σ
    fstₚ : A bs₁
    sndₚ : B fstₚ bs₂
    @0 bs≡ : bs ≡ bs₁ ++ bs₂
open &ₚᵈ public using (fstₚ ; sndₚ)

&ₚ : (@0 A B : List Σ → Set) (@0 bs : List Σ) → Set
&ₚ A B = &ₚᵈ A λ _ → B

Raw&ₚ : {A : List Σ → Set} {B : {bs : List Σ} → A bs → List Σ → Set} → (ra : Raw A) (rb : Raw₁ ra B)
        → Raw (&ₚᵈ A B)
Raw.D (Raw&ₚ ra rb) = Sigma (Raw.D ra) (Raw₁.D rb)
Raw.to (Raw&ₚ ra rb) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = (Raw.to ra fstₚ₁) , (Raw₁.to rb _ sndₚ₁)
