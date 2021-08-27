open import Aeres.Prelude

open import Data.Nat.Properties

module Aeres.Arith where

divmod2 : ℕ → ℕ × Bool
divmod2 0 = 0 , false
divmod2 1 = 0 , true
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

2^n≢0 : ∀ n → 2 ^ n ≢ 0
2^n≢0 n eq
  with 1≤2^n n
...| pf
  with 2 ^ n
2^n≢0 n refl | () | .0

divmod2-*2 : ∀ n → toℕ (proj₂ (divmod2 n)) + 2 * proj₁ (divmod2 n) ≡ n
divmod2-*2 zero = refl
divmod2-*2 (suc zero) = refl
divmod2-*2 (suc (suc n))
  with divmod2-*2 n
...| ih
  with divmod2 n
...| q , r = begin
  toℕ r + ((1 + q) + (1 + (q + 0))) ≡⟨ cong (toℕ r +_) (+-suc (1 + q) (q + 0)) ⟩
  toℕ r + (2 + 2 * q) ≡⟨ sym (+-assoc (toℕ r) 2 (2 * q)) ⟩
  (toℕ r + 2) + 2 * q ≡⟨ cong (_+ 2 * q) (+-comm (toℕ r) 2) ⟩
  (2 + (toℕ r)) + 2 * q ≡⟨ +-assoc 2 (toℕ r) (2 * q) ⟩
  2 + (toℕ r + 2 * q) ≡⟨ cong (2 +_) ih ⟩
  2 + n ∎
  where open ≡-Reasoning

divmod2-2^ : ∀ n → proj₁ (divmod2 (2 ^ (1 + n))) ≡ 2 ^ n
divmod2-2^ n
  with divmod2-*2 (2 ^ (1 + n))
...| pf
  with help (2 ^ n)
  where
  help : ∀ n → proj₂ (divmod2 (2 * n)) ≡ false
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
...| pf = TODO
  where
    postulate
      TODO : 2 + proj₁ (divmod2 i) ≤ 2 ^ n

-- divmod2-<-^ i 0 (s≤s (s≤s ()))
-- divmod2-<-^ zero (suc n) i< = *-monoʳ-≤ 2 (1≤2^n n)
-- divmod2-<-^ 1 (suc n) i< = *-monoʳ-≤ 2 (1≤2^n n)
-- divmod2-<-^ (suc (suc i)) (suc zero) (s≤s (s≤s (s≤s (s≤s ()))))
-- divmod2-<-^ (suc (suc i)) (suc (suc n)) i<
--   with divmod2-<-^ i (suc n) {!!}
-- ...| xxx = {!!}

