{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Grammar.Parser
open import Aeres.Data.X509

open import Data.Nat.Properties
  hiding (_≟_)
open import Data.List.Properties

module Aeres.Data.X509.Decidable.Length where

open Base256

module parseShortLen where
  here' = "parseShortLen"

  parseShortLen : Parser Dig (Logging ∘ Dec) Length.Short
  runParser parseShortLen [] = do
    tell $ here' String.++ ": underflow reading length"
    return ∘ no $ λ where
      (success .([ l ]) read read≡ (Length.mkShort l l<128 refl) suffix ())
  runParser parseShortLen (l ∷ xs)
    with toℕ l <? 128
  ... | no  l≮128 =
    return ∘ no $ λ where
      (success .([ l ]) read read≡ (Length.mkShort l l<128 refl) suffix refl) →
        contradiction l<128 l≮128
  ... | yes l<128 =
    return (yes (success [ l ] 1 refl (Length.mkShort l l<128 refl) xs refl))

open parseShortLen public using (parseShortLen)

module parseLongLen where
  here' = "parseLongLen"

  parseLongLen : Parser Dig (Logging ∘ Dec) Length.Long
  runParser parseLongLen [] = do
    tell $ here' String.++ ": underflow reading length"
    return ∘ no $ λ where
      (success .(l ∷ lₕ ∷ lₜ) read read≡ (Length.mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl) suffix ())
  runParser parseLongLen (l ∷ []) = do
    tell $ here' String.++ ": underflow reading (long) length"
    return ∘ no $ λ where
      (success .(l ∷ lₕ ∷ lₜ) read read≡ (Length.mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl) suffix ())
  runParser parseLongLen (l ∷ lₕ ∷ xs)
    with 128 <? toℕ l
  ... | no  l≯128 = do
    tell $ here' String.++ ": leading byte value to small for long length"
    return ∘ no $ λ where
      (success .(l ∷ lₕ ∷ lₜ) read read≡ (Length.mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl) suffix refl) →
        contradiction l>128 l≯128
  ... | yes l>128
    with toℕ lₕ ≟ 0
  ... | yes lₕ≡0 = do
    tell $ here' String.++ ": first byte of length sequence must not be zero"
    return ∘ no $ λ where
      (success .(l ∷ lₕ ∷ lₜ) read read≡ (Length.mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl) suffix refl) →
        contradiction lₕ≡0 lₕ≢0
  ... | no  lₕ≢0
    with runParser (parseN Dig (toℕ l - 129)) xs
  ... | no parseFail = do
    tell $ here' String.++ ": underflow reading length sequence: " String.++ (String.showNat $ toℕ l - 128)
    return ∘ no $ λ where
      (success .(l ∷ lₕ ∷ lₜ) read read≡ (Length.mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl) suffix refl) →
        contradiction (success lₜ (length lₜ) refl (lₜ , refl , lₜLen) suffix refl)
          parseFail
  ... | yes (success prefix read read≡ (lₜ , refl , lₜLen) suffix refl)
    with lₜ ≟ []
  ... | no  lₜ≢[] =
    return (yes (success (l ∷ lₕ ∷ lₜ) (2 + read) (cong (2 +_) read≡)
                         (Length.mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen (inj₁ lₜ≢[]) refl) suffix refl))
  ... | yes lₜ≡[]
    with toℕ lₕ ≥? 128
  ... | no  lₕ≱128 = do
    tell $ here' String.++ ": long length used where short length would suffice"
    return ∘ no $ ‼ go
    where
    @0 go : ¬ Success Dig Length.Long (l ∷ lₕ ∷ lₜ ++ suffix)
    go (success prefix' read' read≡' (Length.mkLong l' l'>128 lₕ' lₕ'≢0 lₜ' lₜ'Len lₕₜMinRep' refl) suffix' ps≡') =
      [_,_]
        (λ lₜ≢[] → contradiction (trans (proj₁ lₜ≡) lₜ≡[]) lₜ≢[])
        (λ lₕ≥128 → contradiction lₕ≥128 (subst (λ i → ¬ 128 ≤ toℕ i) (sym lₕ≡) lₕ≱128))
        lₕₜMinRep'
      where
      open ≡-Reasoning

      @0 l≡ : l' ≡ l
      l≡ = ∷-injectiveˡ ps≡'

      @0 lₕ≡ : lₕ' ≡ lₕ
      lₕ≡ = ∷-injectiveˡ (∷-injectiveʳ ps≡')

      @0 lₜ≡ : lₜ' ≡ lₜ × suffix' ≡ suffix
      lₜ≡ = Lemmas.length-++-≡ _ _ _ _ (∷-injectiveʳ (∷-injectiveʳ ps≡')) $ begin
        length lₜ'   ≡⟨ lₜ'Len ⟩
        toℕ l' - 129 ≡⟨ cong (λ i → toℕ i - 129) l≡ ⟩
        toℕ l - 129  ≡⟨ sym lₜLen ⟩
        length lₜ    ∎
  ... | yes lₕ≥128 =
    return (yes (success _ _ refl (Length.mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen (inj₂ lₕ≥128) refl) suffix refl))

open parseLongLen public using (parseLongLen)

module parseLen where
  here' = "parseLen"

  parseLen : Parser Dig (Logging ∘ Dec) Length
  runParser parseLen xs = do
    no ¬short ← runParser parseShortLen xs
      where yes short → return (yes (mapSuccess _ (λ {xs'} → Length.short {xs'}) short))
    no ¬long  ← runParser parseLongLen xs
      where yes long → return (yes (mapSuccess _ (λ {xs'} → Length.long {xs'}) long))
    return ∘ no $ λ where
      (success prefix read read≡ (Length.short short) suffix ps≡) →
        contradiction (success prefix read read≡ short suffix ps≡) ¬short
      (success prefix read read≡ (Length.long long) suffix ps≡) →
        contradiction (success _ _ read≡ long _ ps≡) ¬long

open parseLen public using (parseLen)


private
  module Test where

    len₁bs : List Dig
    len₁bs = # 130 ∷ # 13 ∷ [ # 82 ]

    len₁ : Length len₁bs
    len₁ = Length.longₛ (# 130) (# 13) [ # 82 ]

    len₁p : Logging.val (runParser parseLen len₁bs) ≡ yes (success _ 3 refl (Length.longₛ (# 130) (# 13) [ # 82 ]) [] refl)
    len₁p = refl

    len₂bs : List Dig
    len₂bs = [ # 127 ]

    len₂ : Length len₂bs
    len₂ = Length.shortₛ (# 127)

    len₂p : Logging.val (runParser parseLen len₂bs) ≡ yes (success _ 1 refl (Length.shortₛ (# 127)) [] refl)
    len₂p = refl

    len₃p : isNo (Logging.val (runParser parseLen [ # 128 ])) ≡ true
    len₃p = refl