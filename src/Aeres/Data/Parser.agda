open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.Parser (Σ : Set) where

record Success (A : List Σ → Set) (xs : List Σ) : Set where
  constructor success
  field
    @0 prefix : List Σ
    read   : ℕ
    @0 read≡ : read ≡ length prefix
    value  : A prefix
    suffix : List Σ
    @0 ps≡    : prefix ++ suffix ≡ xs

mapSuccess : ∀ {A B : List Σ → Set} → (∀ {@0 xs} → A xs → B xs) → ∀ {@0 xs} → Success A xs → Success B xs
mapSuccess f (success prefix read read≡ value suffix ps≡ ) = success prefix read read≡ (f value) suffix ps≡

record Parser (M : Set → Set) (A : List Σ → Set) : Set where
  constructor mkParser
  field
    runParser : (xs : List Σ) → M (Success A xs)
open Parser public

-- parseSingleDec : ⦃ _ : Eq Σ ⦄ → ∀ a → Parser Dec ([ a ] ≡_)
-- runParser (parseSingleDec a) [] = no λ where (refl ^S suffix [ () ]S)
-- runParser (parseSingleDec a) (x ∷ xs)
--   with x ≟ a
-- ... | yes refl = yes (refl ^S xs [ refl ]S)
-- ... | no  x≢   = no λ where (refl ^S suffix [ refl ]S) → x≢ refl

parseN : (n : ℕ) → Parser Dec λ xs → Σ[ ys ∈ List Σ ] (xs ≡ ys × length xs ≡ n)
runParser (parseN zero) xs = yes (success [] 0 refl ([] , refl , refl) xs refl)
runParser (parseN (suc n)) [] = no $ λ where
  (success prefix read read≡ (ys , refl , len-xs) suffix ps≡) → 0≢1+n $ begin
    length{A = Σ} [] ≡⟨ cong length (sym (‼ ps≡)) ⟩
    length (ys ++ suffix) ≡⟨ length-++ ys ⟩
    length ys + length suffix ≡⟨ cong (_+ length suffix) len-xs ⟩
    suc (n + length suffix) ∎
    where open ≡-Reasoning
runParser (parseN (suc n)) (x ∷ xs)
  with runParser (parseN n) xs
... | no  proof₁ = no $ ‼ go
  where
    @0 go : ¬ Success (λ xs → Σ[ ys ∈ List Σ ] (xs ≡ ys × length xs ≡ 1 + n)) (x ∷ xs)
    go (success .(x ∷ ys) .(length (x ∷ ys)) refl (x ∷ ys , refl , ysLen) suffix ps≡) =
      proof₁ (success ys (length ys) refl (ys , refl , suc-injective ysLen) suffix (∷-injectiveʳ ps≡))
... | yes (success prefix read read≡ (ys , ys≡ , ysLen) suffix ps≡) =
  yes (success (x ∷ prefix) (1 + read) (cong suc read≡) (x ∷ ys  , cong (x ∷_) ys≡ , cong suc ysLen) suffix (cong (x ∷_) ps≡))
