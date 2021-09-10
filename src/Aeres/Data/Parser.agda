open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

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

parseN : (n : ℕ) → Parser Dec λ xs → Σ[ ys ∈ List Σ ] (xs ≡ ys × length xs ≡ n)
runParser (parseN zero) xs = yes $ (([] , refl , refl) ^S xs [ refl ]S)
runParser (parseN (suc n)) [] = no $ λ where
  ((ys , refl , len-xs) ^S suffix [ ps≡ ]S) → 0≢1+n $ begin
    length{A = Σ} []          ≡⟨ cong length (sym (‼ ps≡)) ⟩
    length (ys ++ suffix)     ≡⟨ length-++ ys ⟩
    length ys + length suffix ≡⟨ cong (_+ length suffix) len-xs ⟩
    suc (n + length suffix)   ∎
    where
    open ≡-Reasoning
runParser (parseN (suc n)) (x ∷ xs)
  with runParser (parseN n) xs
... | no  proof₁ = no go
  where
  go : ¬ Success (λ xs → Σ[ ys ∈ List Σ ] (xs ≡ ys × length xs ≡ 1 + n)) (x ∷ xs)
  go ((x' ∷ ys , refl , ys-len) ^S suffix [ ps≡ ]S) =
    proof₁ (_^S_[_]S {prefix = ys} (ys , refl , suc-injective ys-len) suffix xs≡)
    where
    @0 xs≡ : ys ++ suffix ≡ xs
    xs≡ = ∷-injectiveʳ ps≡
... | yes S@((ys , ys≡ , ys-len) ^S suffix [ ps≡ ]S) =
  yes (_^S_[_]S {prefix = x ∷ Success.prefix S} (x ∷ ys , cong (x ∷_) ys≡ , cong suc ys-len ) suffix (cong (x ∷_) ps≡))
