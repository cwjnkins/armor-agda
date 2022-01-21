open import Aeres.Prelude

module Aeres.Data.Box where


【_】   : (ℕ → Set) → Set
【 A 】 = ∀ {n} → A n


infixr 0 _⟶_
_⟶_ : (A B : ℕ → Set) → ℕ → Set
A ⟶ B = λ n → A n → B n

record □_ (A : ℕ → Set) (n : ℕ) : Set where
  constructor mkBox
  field
    call : ∀ {m} → .(m < n) → A m

