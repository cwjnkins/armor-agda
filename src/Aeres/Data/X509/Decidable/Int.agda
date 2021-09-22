{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Properties
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.Int where

open Base256

module parseInt where
  here' = "parseInt"

  open import Aeres.Data.X509.Decidable.Length
  open ≡-Reasoning

  parseInt : Parser Dig (Logging ∘ Dec) Generic.Int
  runParser parseInt [] = do
    tell $ here' String.++ ": underflow reading tag"
    return ∘ no $ λ where
      (success prefix read read≡ value suffix ps≡) →
        ‼ NonEmpty.Int value (++-conicalˡ _ _ ps≡)
  runParser parseInt (x ∷ xs)
    with x ≟ Tag.Integer
  ... | no  x≢ = do
    tell $ here' String.++ ": tag mis-match"
    return ∘ no $ λ where
      (success .(Tag.Integer ∷ l ++ v) read read≡ (Generic.mkInt{l}{v} len val len≡ refl) suffix ps≡) →
        contradiction (∷-injectiveˡ (sym ps≡)) x≢
  ... | yes refl = do
    yes (success pre₀ r₀ r₀≡ len₀ suf₀ ps≡₀) ← runParser parseLen xs
      where no ¬parse → {!!}
    yes (success .v r₁ r₁≡ (v , refl , vLen) suf₁ ps≡₀) ←
      runParser (parseN Dig (getLength len₀) (tell $ here' String.++ ": underflow reading int")) suf₀
      where no ¬parse → {!!}
    return (yes
      (success (Tag.Integer ∷ pre₀ ++ v)
        (1 + r₀ + r₁)
        (cong suc
          (begin (r₀ + r₁ ≡⟨ cong (_+ r₁) r₀≡ ⟩
                 length pre₀ + r₁ ≡⟨ cong (length pre₀ +_) r₁≡ ⟩
                 length pre₀ + length v ≡⟨ sym $ length-++ pre₀ ⟩
                 length (pre₀ ++ v) ∎)))
        (Generic.mkInt len₀ (Generic.mkIntegerValue _ refl) (sym vLen) refl) suf₁ {!!}))
