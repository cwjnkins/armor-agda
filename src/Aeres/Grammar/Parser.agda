{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Grammar.Parser (Σ : Set) where

open import Aeres.Grammar.Definitions Σ

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

record Parserᵢ (M : List Σ → Set → Set) (A : List Σ → Set) : Set where
  constructor mkParser
  field
    runParser : (xs : List Σ) → M xs (Success A xs)
open Parserᵢ public

Parser : (M : Set → Set) (A : List Σ → Set) → Set
Parser M = Parserᵢ (const M)

ParserWF : (M : Set → Set) (A : List Σ → Set) → Set
ParserWF M A = Parserᵢ (λ xs X → (@0 _ : Acc _<_ (length xs)) → M X) A

-- parseSingleDec : ⦃ _ : Eq Σ ⦄ → ∀ a → Parser Dec ([ a ] ≡_)
-- runParser (parseSingleDec a) [] = no λ where (refl ^S suffix [ () ]S)
-- runParser (parseSingleDec a) (x ∷ xs)
--   with x ≟ a
-- ... | yes refl = yes (refl ^S xs [ refl ]S)
-- ... | no  x≢   = no λ where (refl ^S suffix [ refl ]S) → x≢ refl

parseN : {M : Set → Set} ⦃ _ : Monad M ⦄ →
         (n : ℕ) → M (Level.Lift _ ⊤) → Parser (M ∘ Dec) λ xs → Σ[ ys ∈ List Σ ] (xs ≡ ys × length xs ≡ n)
runParser (parseN zero m) xs = return (yes (success [] 0 refl ([] , refl , refl) xs refl))
runParser (parseN (suc n) m) [] = do
  m
  return ∘ no $ λ where
    (success prefix read read≡ (ys , refl , len-xs) suffix ps≡) → ‼ 0≢1+n $ begin
      length{A = Σ} []          ≡⟨ cong length (sym (‼ ps≡)) ⟩
      length (ys ++ suffix)     ≡⟨ length-++ ys ⟩
      length ys + length suffix ≡⟨ cong (_+ length suffix) len-xs ⟩
      suc (n + length suffix)   ∎
  where
  open ≡-Reasoning
runParser (parseN (suc n) m) (x ∷ xs) = do
  yes (success prefix read read≡ (ys , ys≡ , ysLen) suffix ps≡) ← runParser (parseN n m) xs
    where no ¬parse → do
      return ∘ no $ ‼ λ where
        (success .(x ∷ ys) read read≡ (x ∷ ys , refl , ysLen) suffix ps≡) →
          contradiction
            (success ys (length ys) refl (ys , refl , cong pred ysLen) suffix (∷-injectiveʳ ps≡))
            ¬parse
  return (yes 
    (success (x ∷ ys) _ refl
      (x ∷ ys , refl , trans₀ (sym (cong suc (cong length ys≡))) (cong suc ysLen))
      suffix (cong (x ∷_) (trans (cong (_++ suffix) (sym ys≡)) ps≡))))

-- _×ₚ_ : (A B : List Σ → Set) → List Σ → Set
-- A ×ₚ B = λ xs → A xs × B xs
record _×ₚ_ (@0 A B : List Σ → Set) (@0 xs : List Σ) : Set where
  constructor mk×ₚ
  field
    @0 {bs} : List Σ
    fstₚ : A bs
    sndₚ : B bs
    @0 bs≡ : bs ≡ xs

parse≤ : ∀ {A} {M : Set → Set} ⦃ _ : Monad M ⦄ (n : ℕ) →
  Parser (M ∘ Dec) A → NonNesting A → M (Level.Lift _ ⊤) →
  Parser (M ∘ Dec) (A ×ₚ ((_≤ n) ∘ length))
runParser (parse≤{A} n p nn m) xs = do
  (yes (success pre₀ r₀ r₀≡ v₀ suf₀ ps≡₀)) ← runParser p xs
    where no ¬parse → do
      return ∘ no $ λ where
        (success prefix read read≡ (mk×ₚ v _ refl) suffix ps≡) →
          contradiction (success prefix _ read≡ v suffix ps≡) ¬parse
  case r₀ ≤? n of λ where
    (no  r₀≰n) → do
      m
      return ∘ no $ λ where
        (success prefix r r≡ (mk×ₚ v r≤n refl) suffix ps≡) →
          contradiction
            (begin (r₀           ≡⟨ r₀≡ ⟩
                   length pre₀   ≡⟨ cong length (nn (trans ps≡₀ (sym ps≡)) v₀ v) ⟩
                   length prefix ≤⟨ r≤n ⟩
                   n ∎))
            r₀≰n
    (yes r₀≤n) →
      return (yes (success pre₀ _ r₀≡ (mk×ₚ v₀ (subst₀ (λ i → i ≤ n) r₀≡ r₀≤n) refl) suf₀ ps≡₀))
  where open ≤-Reasoning

-- Parse while a given guard is true, but it *must* be terminated by a symbol
-- for which the guard is false (rather than from running out of symbols)
-- TODO: erasure for prefix, allPrefix should be flipped
record ParseWhileₜ (A : Σ → Set) (xs : List Σ) : Set where
  constructor mkParseWhile
  field
    prefix : List Σ
    term   : Σ
    @0 allPrefix : All A prefix
    @0 ¬term     : ¬ A term
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
         (mkParseWhile (x ∷ prefix₁) term (a All.∷ allPrefix) ¬term (cong (x ∷_) ps≡₁))
         suffix (cong (x ∷_) ps≡))
