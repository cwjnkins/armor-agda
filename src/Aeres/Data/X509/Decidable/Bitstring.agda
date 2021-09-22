{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.Bitstring where

open Base256

module parseBitstring where
  open ≡-Reasoning

  here' = "parseBitstring"

  parseBitstring : Parser Dig (Logging ∘ Dec) Generic.Bitstring
  parseBitstring =
    parseTLV Tag.Bitstring here' Generic.BitstringValue p
    where
    p : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength Dig _ n)
    runParser (p n) xs = do
      yes (success .(bₕ ∷ bₜ) r₀ r₀≡ (mk×ₚ (singleton (bₕ ∷ bₜ) refl) bsLen refl) suf₀ ps≡₀) ←
        runParser (parseN Dig n (tell $ here' String.++ ": underflow")) xs
        where
          (yes (success .[] .0 refl (mk×ₚ (singleton [] refl) refl refl) .xs refl)) →
            return ∘ no $ λ where
              (success .(bₕ ∷ bₜ) read read≡ (mk×ₚ (Generic.mkBitstringValue bₕ bₕ<8 bₜ unusedBits refl) () refl) suffix ps≡)
          (no ¬parse) →
            return ∘ no $ λ where
              (success .(bₕ ∷ bₜ) read read≡ (mk×ₚ (Generic.mkBitstringValue bₕ bₕ<8 bₜ unusedBits refl) bsLen refl) suffix ps≡) →
                contradiction
                  (success (bₕ ∷ bₜ) read read≡ (mk×ₚ (singleton (bₕ ∷ bₜ) refl) bsLen refl) suffix ps≡)
                  ¬parse
      case toℕ bₕ <? 8 of λ where
        (no  bₕ≮8) → do
          tell $ here' String.++ ": unused bits filed too large"
          return ∘ no $ λ where
            (success .(bₕ' ∷ bₜ) read read≡ (mk×ₚ (Generic.mkBitstringValue bₕ' bₕ<8 bₜ unusedBits refl) bsLen refl) suffix ps≡) →
              contradiction
                (subst ((_< 8) ∘ toℕ) (∷-injectiveˡ (trans ps≡ (sym ps≡₀))) bₕ<8)
                bₕ≮8
        (yes bₕ<8) →
          (case bₜ ret (λ x → x ≡ bₜ → _) of λ where
            [] refl →
              case bₕ ≟ # 0 of λ where
                (no  bₕ≢0) → do
                  tell $ here' String.++ ": non-zero unused bits in 0-bit string"
                  return ∘ no $ λ where
                    (success ._ read read≡ (mk×ₚ (Generic.mkBitstringValue bₕ bₕ<8 [] unusedBits refl) bsLen refl) suffix ps≡) →
                      contradiction
                        (subst (_≡ # 0) (∷-injectiveˡ (trans ps≡ (sym ps≡₀))) unusedBits)
                        bₕ≢0
                    (success ._ read read≡ (mk×ₚ (Generic.mkBitstringValue bₕ bₕ<8 (bₜ₁ ∷ bₜ) unusedBits refl) bsLen' refl) suffix ps≡) →
                      case (1 ≡ 2 + (length bₜ)) ∋ trans bsLen (sym bsLen') of λ ()
                (yes bₕ≡0) →
                  return (yes
                    (success [ bₕ ] _ refl (mk×ₚ (Generic.mkBitstringValue bₕ bₕ<8 [] bₕ≡0 refl) bsLen refl) suf₀ ps≡₀))
            (bₜ₁ ∷ bₜ) refl →
              return (yes (success (bₕ ∷ bₜ₁ ∷ bₜ) r₀ r₀≡ (mk×ₚ (Generic.mkBitstringValue bₕ bₕ<8 (bₜ₁ ∷ bₜ) tt refl) bsLen refl) suf₀ ps≡₀)))
          refl

open parseBitstring public using (parseBitstring)
