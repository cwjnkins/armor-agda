open import Aeres.Prelude

module Aeres.Data.Parser (Σ : Set) where

record Success (A : List Σ → Set) (xs : List Σ) : Set where
  constructor _^S_[_]S
  field
    @0 {prefix} : List Σ
    value  : A prefix
    suffix : List Σ
    @0 ps≡    : prefix ++ suffix ≡ xs

record Parser (M : Set → Set) (A : List Σ → Set) : Set where
  constructor mkParser
  field
    runParser : (xs : List Σ) → M (Success A xs)
open Parser public


parseSingleDec : ⦃ _ : Eq Σ ⦄ → ∀ a → Parser Dec ([ a ] ≡_)
runParser (parseSingleDec a) [] = no λ where (refl ^S suffix [ () ]S)
runParser (parseSingleDec a) (x ∷ xs)
  with x ≟ a
... | yes refl = yes (refl ^S xs [ refl ]S)
... | no  x≢   = no λ where (refl ^S suffix [ refl ]S) → x≢ refl
