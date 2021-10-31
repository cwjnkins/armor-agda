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

  parseBitstringValue : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength Dig Generic.BitstringValue n)
  runParser (parseBitstringValue n) xs = do
    yes (success .(bₕ ∷ bₜ) r₀ r₀≡ (mk×ₚ (singleton (bₕ ∷ bₜ) refl) bsLen refl) suf₀ ps≡₀) ←
      runParser (parseN Dig n (tell $ here' String.++ ": underflow")) xs
      where
        (yes (success .[] .0 refl (mk×ₚ (singleton [] refl) refl refl) .xs refl)) →
          return ∘ no $ λ where
            (success .(bₕ ∷ bₜ) read read≡ (mk×ₚ (Generic.mkBitstringValue bₕ bₜ bₕ<8 bits unusedBits refl) () refl) suffix ps≡)
        (no ¬parse) →
          return ∘ no $ λ where
            (success .(bₕ ∷ bₜ) read read≡ (mk×ₚ (Generic.mkBitstringValue bₕ bₜ bₕ<8 bits unusedBits refl) sndₚ₁ refl) suffix ps≡) →
              contradiction
                (success (bₕ ∷ bₜ) _ read≡ (mk×ₚ self sndₚ₁ refl) suffix ps≡)
                ¬parse
    case toℕ bₕ <? 8 of λ where
      (no bₕ≮8) → do
        tell $ here' String.++ ": unused bits field too large"
        return ∘ no $ λ where
          (success prefix read read≡ (mk×ₚ (Generic.mkBitstringValue bₕ bₜ bₕ<8 bits unusedBits refl) sndₚ₁ refl) suffix ps≡) →
            contradiction
              (≤-trans (Lemmas.≡⇒≤ (cong (suc ∘ toℕ) (∷-injectiveˡ (trans₀ ps≡₀ (sym ps≡))))) bₕ<8)
              bₕ≮8
      (yes bₕ<8) →
        case Generic.bitstringUnusedBits? bₕ bₜ of λ where
          (no ¬validunused) → do
            tell $ here' String.++ ": bad unused bits"
            return ∘ no $ λ where
              (success prefix read read≡ (mk×ₚ (Generic.mkBitstringValue bₕ' bₜ' _ _ unusedBits refl) sndₚ₁ refl) suffix ps≡) →
                contradiction
                  (subst₂ Generic.BitstringUnusedBits{x = bₕ'}{u = bₜ'}{bₜ}
                    (∷-injectiveˡ (trans₀ ps≡ (sym ps≡₀)))
                    (∷-injectiveʳ (exactLength-nonnesting _ (trans₀ ps≡ (sym ps≡₀))
                                    (mk×ₚ{A = Singleton} self sndₚ₁ refl)
                                    (mk×ₚ self bsLen refl)))
                    unusedBits)
                  ¬validunused
          (yes validunused) →
            return (yes
              (success (bₕ ∷ bₜ) _ r₀≡ (mk×ₚ (Generic.mkBitstringValue bₕ bₜ bₕ<8 self validunused refl) bsLen refl) suf₀ ps≡₀))

  parseBitstring : Parser Dig (Logging ∘ Dec) Generic.Bitstring
  parseBitstring =
    parseTLV Tag.Bitstring here' Generic.BitstringValue parseBitstringValue

  parseIssUID : Parser Dig (Logging ∘ Dec) X509.IssUID
  parseIssUID =
    parseTLV Tag.EightyOne "issUID" Generic.BitstringValue parseBitstringValue

  parseSubUID : Parser Dig (Logging ∘ Dec) X509.SubUID
  parseSubUID =
    parseTLV Tag.EightyTwo "subUID" Generic.BitstringValue parseBitstringValue

open parseBitstring public using (parseBitstringValue ; parseBitstring ; parseIssUID)

private
  module Test where

    Bitstring₁ : List Dig
    Bitstring₁ = Tag.Bitstring ∷ # 2 ∷ # 5 ∷ [ # 160 ]

    Bitstring₂ : List Dig
    Bitstring₂ = Tag.Bitstring ∷ # 2 ∷ # 0 ∷ [ # 160 ]

    Bitstring₃ : List Dig
    Bitstring₃ = Tag.Bitstring ∷ # 2 ∷ # 7 ∷ [ # 160 ]

    Bitstring₄ : List Dig
    Bitstring₄ = Tag.Bitstring ∷ # 2 ∷ # 8 ∷ [ # 160 ]

    Bitstring₅ : List Dig
    Bitstring₅ = Tag.Bitstring ∷ # 3 ∷ # 8 ∷ # 255 ∷ [ # 160 ]

    Bitstring₆ : List Dig
    Bitstring₆ = Tag.Bitstring ∷ # 1 ∷ [ # 0 ]

    Bitstring₇ : List Dig
    Bitstring₇ = Tag.Bitstring ∷ # 1 ∷ [ # 3 ]

    test₁ : Generic.Bitstring Bitstring₁
    test₁ = Success.value (toWitness {Q = Logging.val (runParser parseBitstring Bitstring₁)} tt)

    test₂ : Generic.Bitstring Bitstring₂
    test₂ = Success.value (toWitness {Q = Logging.val (runParser parseBitstring Bitstring₂)} tt)

    test₃ : ¬ Success _ Generic.Bitstring Bitstring₃
    test₃ = toWitnessFalse {Q = Logging.val (runParser parseBitstring Bitstring₃)} tt

    test₄ : ¬ Success _ Generic.Bitstring Bitstring₄
    test₄ = toWitnessFalse {Q = Logging.val (runParser parseBitstring Bitstring₄)} tt

    test₅ : ¬ Success _ Generic.Bitstring Bitstring₅
    test₅ = toWitnessFalse {Q = Logging.val (runParser parseBitstring Bitstring₅)} tt

    test₆ : Generic.Bitstring Bitstring₆
    test₆ = Success.value (toWitness {Q = Logging.val (runParser parseBitstring Bitstring₆)} tt)

    test₇ : ¬ Success _ Generic.Bitstring Bitstring₇
    test₇ = toWitnessFalse {Q = Logging.val (runParser parseBitstring Bitstring₇)} tt

