open import Aeres.Prelude

open import Data.Fin.Properties
  renaming (≤-refl to Fin-≤-refl ; ≤-trans to Fin-≤-trans ; suc-injective to Fin-suc-injective)
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Induction.WellFounded

module Aeres.Binary where

Binary = Vec Bool

pattern #0 = false
pattern #1 = true

bitToℕ : Bool → ℕ
bitToℕ #0 = 0
bitToℕ #1 = 1

infixl 6 _b+_
_b+_ : Bool → ℕ → ℕ
b b+ n = bitToℕ b + n

divmod2 : ℕ → ℕ × Bool
divmod2 0 = 0 , #0
divmod2 1 = 0 , #1
divmod2 (suc (suc n)) = map₁ suc (divmod2 n)

divmod2-≤ : ∀ n → proj₁ (divmod2 n) ≤ n
divmod2-≤ zero = ≤-refl
divmod2-≤ (suc zero) = z≤n
divmod2-≤ (suc (suc n))
  with divmod2-≤ n
...| pf = ≤-trans (s≤s pf) (s≤s (n≤1+n n))

1≤2^n : ∀ n → 1 ≤ 2 ^ n
1≤2^n zero = ≤-refl
1≤2^n (suc n) = ≤-stepsʳ ((2 ^ n) + zero) (1≤2^n n)

divmod2-*2 : ∀ n → proj₂ (divmod2 n) b+ 2 * proj₁ (divmod2 n) ≡ n
divmod2-*2 zero = refl
divmod2-*2 (suc zero) = refl
divmod2-*2 (suc (suc n))
  with divmod2-*2 n
...| ih
  with divmod2 n
...| q , r = begin
  r b+ ((1 + q) + (1 + (q + 0))) ≡⟨ cong (r b+_) (+-suc (1 + q) (q + 0)) ⟩
  r b+ (2 + 2 * q) ≡⟨ sym (+-assoc (bitToℕ r) 2 (2 * q)) ⟩
  (r b+ 2) + 2 * q ≡⟨ cong (_+ 2 * q) (+-comm (bitToℕ r) 2) ⟩
  (2 + (bitToℕ r)) + 2 * q ≡⟨ +-assoc 2 (bitToℕ r) (2 * q) ⟩
  2 + (r b+ 2 * q) ≡⟨ cong (2 +_) ih ⟩
  2 + n ∎
  where open ≡-Reasoning

divmod2-2^ : ∀ n → proj₁ (divmod2 (2 ^ (1 + n))) ≡ 2 ^ n
divmod2-2^ n
  with divmod2-*2 (2 ^ (1 + n))
...| pf
  with help (2 ^ n)
  where
  help : ∀ n → proj₂ (divmod2 (2 * n)) ≡ #0
  help zero = refl
  help (suc n) rewrite +-suc n (n + 0) = help n
...| pf₂ rewrite pf₂ = *-injective (proj₁ (divmod2 (2 * 2 ^ n))) (2 ^ n) pf
  where
  *-injective : ∀ a b → 2 * a ≡ 2 * b → a ≡ b
  *-injective zero zero eq = refl
  *-injective (suc a) (suc b) eq
    rewrite +-suc a (a + 0)
    |       +-suc b (b + 0)
    = cong suc (*-injective a b (suc-injective (suc-injective eq)))

divmod2-<-^ : ∀ i n → 2 + i < 2 ^ (1 + n) → 1 + proj₁ (divmod2 i) < 2 ^ n
divmod2-<-^ i n i<
  with divmod2-*2 (2 + i)
...| pf = {!!}

-- divmod2-<-^ i 0 (s≤s (s≤s ()))
-- divmod2-<-^ zero (suc n) i< = *-monoʳ-≤ 2 (1≤2^n n)
-- divmod2-<-^ 1 (suc n) i< = *-monoʳ-≤ 2 (1≤2^n n)
-- divmod2-<-^ (suc (suc i)) (suc zero) (s≤s (s≤s (s≤s (s≤s ()))))
-- divmod2-<-^ (suc (suc i)) (suc (suc n)) i<
--   with divmod2-<-^ i (suc n) {!!}
-- ...| xxx = {!!}


toBinary : ∀ {n} → Fin.Fin (2 ^ n) → Binary n
toBinary{n} i = help n (Fin.toℕ i) (toℕ<n i) (<-wellFounded (Fin.toℕ i))
  where
  help : (n : ℕ) (i : ℕ) (i< : i < 2 ^ n) → Acc _<_ i → Binary n
  help zero i i< ac = []
  help (suc n) 0 i< (acc rs) = replicate #0
  help (suc n) 1 i< (acc rs) = #1 ∷ replicate #0
  help (suc n) i@(suc (suc i')) i< (acc rs)
     with divmod2-≤ i'
  ...| q≤i'
     with divmod2 i'
     |    inspect divmod2 i'
  ...| (q , r) | Reveal.[ eq ] = r ∷ help n (suc q) pf (rs (suc q) (s≤s (s≤s q≤i')))
    where
    pf : 1 + q < 2 ^ n
    pf rewrite sym (cong proj₁ eq) = divmod2-<-^ i' n i<

module Base256 where
  Dig = Binary 8

module Base64 where
  Dig = Binary 6

  charset : Vec Char.Char 64
  charset = fromList (String.toList charset')
    where
    charset' = "ABCDEFGHIJKLMNOPQRStUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

module Octets where
  base64To256 : Vec Base64.Dig 4 → Vec Base256.Dig 3
  base64To256
    (  (b₁₁ ∷ b₁₂ ∷ b₁₃ ∷ b₁₄ ∷ b₁₅ ∷ b₁₆ ∷ [])
     ∷ (b₂₁ ∷ b₂₂ ∷ b₂₃ ∷ b₂₄ ∷ b₂₅ ∷ b₂₆ ∷ [])
     ∷ (b₃₁ ∷ b₃₂ ∷ b₃₃ ∷ b₃₄ ∷ b₃₅ ∷ b₃₆ ∷ [])
     ∷ (b₄₁ ∷ b₄₂ ∷ b₄₃ ∷ b₄₄ ∷ b₄₅ ∷ b₄₆ ∷ [])
     ∷ [])
    =   (b₁₁ ∷ b₁₂ ∷ b₁₃ ∷ b₁₄ ∷ b₁₅ ∷ b₁₆ ∷ b₂₁ ∷ b₂₂ ∷ [])
      ∷ (b₂₃ ∷ b₂₄ ∷ b₂₅ ∷ b₂₆ ∷ b₃₁ ∷ b₃₂ ∷ b₃₃ ∷ b₃₄ ∷ [])
      ∷ (b₃₅ ∷ b₃₆ ∷ b₄₁ ∷ b₄₂ ∷ b₄₃ ∷ b₄₄ ∷ b₄₅ ∷ b₄₆ ∷ [])
      ∷ []

-- module Base64 where
--   Dig : Set
--   Dig = Σ[ d ∈ ℕ ] d ≤ 63


-- module Base256 where
--   Dig : Set
--   Dig = Σ[ d ∈ ℕ ] d ≤ 255

-- module Octets where
--   b64To256 : Vec Base64.Dig 4 → Vec Base256.Dig 3
--   b64To256 (d₁ ∷ d₂ ∷ d₃ ∷ d₄ ∷ []) = {!!}
