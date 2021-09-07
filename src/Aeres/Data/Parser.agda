open import Aeres.Prelude

module Aeres.Data.Parser (Σ : Set) where

record Success (A : List Σ → Set) (xs : List Σ) : Set where
  constructor _^S_[_]S
  field
    {prefix} : List Σ
    value  : A prefix
    suffix : List Σ
    ps≡    : prefix ++ suffix ≡ xs

record Parser (M : Set → Set) (A : List Σ → Set) : Set where
  constructor mkParser
  field
    runParser : (xs : List Σ) → M (Success A xs)
open Parser public

parseSingleDec : ⦃ _ : Eq Σ ⦄ → ∀ a → Parser Dec ([ a ] ≡_)
runParser (parseSingleDec a) [] = no go
  where
  go : ¬ Success ([ a ] ≡_) []
  go (value ^S suffix [ ps≡ ]S)
    with ++-conicalˡ _ suffix ps≡
  ...| refl = case value of λ ()
runParser (parseSingleDec a) (x ∷ xs)
  with x ≟ a
...| yes refl = yes (refl ^S xs [ refl ]S)
...| no  x≢ = no go
  where
  go : ¬ Success ([ a ] ≡_) (x ∷ xs)
  go (refl ^S suffix [ refl ]S) = x≢ refl

-- record _×ₚ_ (A B : List Σ → Set) (xs : List Σ) : Set where
--   constructor mkProdₚ
--   field
--     prefix suffix : List Σ
--     prefix++suffix≡ : xs ≡ prefix ++ suffix
--     fstₚ : A prefix
--     sndₚ : B suffix

-- module _ {M : Set → Set} ⦃ m : Monad M ⦄ where
--   _⟨&⟩_ : ∀ {A B : List Σ → Set}
--           → Parser M A → Parser M B → Parser M (A ×ₚ B)
--   _⟨&⟩_ {A}{B} p₁ p₂ = mkParser go
--     where
--     open ≡-Reasoning

--     go : (xs : List Σ) → M (Success (A ×ₚ B) xs)
--     go xs = do
--       (mkSuccess pre₁ v₁ s₁ split₁) ← runParser p₁ xs
--       (mkSuccess pre₂ v₂ s₂ split₂) ← runParser p₂ s₁
--       return (mkSuccess (pre₁ ++ pre₂)
--                (mkProdₚ _ _ refl v₁ v₂)
--                s₂
--                (begin ((pre₁ ++ pre₂) ++ s₂ ≡⟨ ++-assoc pre₁ pre₂ s₂ ⟩
--                       pre₁ ++ (pre₂ ++ s₂)  ≡⟨ cong (pre₁ ++_) split₂ ⟩
--                       pre₁ ++ s₁            ≡⟨ split₁ ⟩
--                       xs                    ∎)))

-- module _ {M : Set → Set} ⦃ m : Monad M ⦄ ⦃ mz : MonadZero M ⦄ where
--   parseSingle : ⦃ _ : Eq Σ ⦄ → ∀ a → Parser M (_≡ [ a ])
--   runParser (parseSingle a) [] = ∅
--   runParser (parseSingle a) (x ∷ xs)
--     with x ≟ a
--   ...| yes x≡ = return (mkSuccess [ x ] (cong (_∷ []) x≡) xs refl)
--   ...| no  x≢ = ∅

--   -- Doesn't do what I want it to :(
--   -- EOF : Parser M (_≡ [])
--   -- runParser EOF [] = return (mkSuccess [] refl [] refl)
--   -- runParser EOF (_ ∷ _) = ∅
