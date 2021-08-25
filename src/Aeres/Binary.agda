open import Aeres.Prelude

open import Data.Fin.Properties
  renaming (≤-refl to Fin-≤-refl ; ≤-trans to Fin-≤-trans)
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Induction.WellFounded

module Aeres.Binary where

Binary = Vec Bool

pattern #0 = false
pattern #1 = true

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
  ...| (q , r) = r ∷ help n (suc q) {!!} (rs (suc q) (s≤s (s≤s q≤i')))

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
