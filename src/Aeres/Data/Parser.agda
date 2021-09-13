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

-- Parse while a given guard is true, but it *must* be terminated by a symbol
-- for which the guard is false (rather than from running out of symbols)
-- TODO: erasure for prefix, allPrefix should be flipped
record ParseWhileₜ (A : Σ → Set) (xs : List Σ) : Set where
  constructor mkParseWhile
  field
    @0 prefix : List Σ
    @0 term   : Σ
    allPrefix : All A prefix
    ¬term     : ¬ A term
    @0 ps≡    : prefix ∷ʳ term ≡ xs

parseWhileₜ : ∀ {A : Σ → Set} (p : Decidable A) → Parser Dec (ParseWhileₜ A)
runParser (parseWhileₜ p) [] = no $ ‼ go
  where
  @0 go : ¬ Success (ParseWhileₜ _) []
  go (success .(prefix₁ ∷ʳ term) _ _ (mkParseWhile prefix₁ term allPrefix ¬term refl) suffix ps≡) =
    case [ term ] ≡ [] ∋ pf of λ ()
    where
    pf : [ term ] ≡ []
    pf = ++-conicalˡ [ term ] _ (++-conicalʳ prefix₁ _ (++-conicalˡ _ _ ps≡))
runParser (parseWhileₜ p) (x ∷ xs)
  with p x
... | no  pf = yes (success [ x ] _ refl (mkParseWhile [] x All.[] pf refl) xs refl)
... | yes a
  with runParser (parseWhileₜ p) xs
... | no  ¬parse = no $ ‼ go
  where
  @0 go : ¬ Success (ParseWhileₜ _) (x ∷ xs)
  go (success .([] ∷ʳ x) read read≡ (mkParseWhile [] .x allPrefix ¬term refl) suffix refl) =
    contradiction a ¬term
  go (success prefix₁@.((x ∷ xs₁) ∷ʳ term) read read≡ (mkParseWhile (x ∷ _) term (All._∷_ {xs = xs₁} px allPrefix) ¬term refl) suffix ps≡) =
    contradiction
      (success (xs₁ ∷ʳ term) _ refl
        (mkParseWhile xs₁ term allPrefix ¬term refl)
        suffix (∷-injectiveʳ ps≡))
      ¬parse
... | yes (success prefix read read≡ (mkParseWhile prefix₁ term allPrefix ¬term ps≡₁) suffix ps≡) =
  yes (success (x ∷ prefix) (1 + read) (cong suc read≡)
         (mkParseWhile (x ∷ prefix₁) term (All._∷_ {xs = {!!}} a allPrefix) ¬term (cong (x ∷_) ps≡₁))
         suffix (cong (x ∷_) ps≡))
-- runParser (parseWhile p) [] = success [] 0 refl All.[] [] refl
-- runParser (parseWhile p) (x ∷ xs)
--   with p x
-- ... | no  _ = success _ 0 refl All.[] (x ∷ xs) refl
-- ... | yes a = {!!}
