{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.TLV where

open Base256

module parseTLV
  (t : Dig) (tName : String) (A : List Dig → Set)
  (p : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength Dig A n))
  where

  here' = "TLV: " String.++ tName

  open ≡-Reasoning

  parseTLV : Parser Dig (Logging ∘ Dec) (Generic.TLV t A)
  runParser parseTLV [] = do
    tell $ here' String.++ ": underflow reading tag"
    return ∘ no $ λ where
      (success .(t ∷ l ++ v) read read≡ (Generic.mkTLV {l} {v} len val len≡ refl) suffix ())
  runParser parseTLV (x ∷ xs) = do
    case x ≟ t of λ where
      (no  x≢) → do
        tell $ here' String.++ ": tag mismatch"
        return ∘ no $ λ where
          (success .(t ∷ l ++ v) read read≡ (Generic.mkTLV{l}{v} len val len≡ refl) suffix ps≡) →
            contradiction (sym (∷-injectiveˡ ps≡)) x≢
      (yes refl) → do
        yes (success pre₀ r₀ r₀≡ len₀ suf₀ ps≡₀) ← runParser parseLen xs
          where no ¬parse → do
            tell $ here' String.++ ": underflow parsing length"
            return ∘ no $ λ where
              (success .(x ∷ l ++ v) read read≡ (Generic.mkTLV{l}{v} len val len≡ refl) suffix ps≡) → ‼
                contradiction
                  (success l (length l) refl len (v ++ suffix)
                    (∷-injectiveʳ (begin (x ∷ l ++ v ++ suffix  ≡⟨ cong (x ∷_) (solve (++-monoid Dig)) ⟩
                                         x ∷ (l ++ v) ++ suffix ≡⟨ ps≡ ⟩
                                         x ∷ xs                 ∎))))
                  ¬parse
        yes (success pre₁ r₁ r₁≡ (mk×ₚ val (─ lenVal) refl) suf₁ ps≡₁) ← runParser (p (getLength len₀)) suf₀
          where no ¬parse → do
            tell $ here'
            return ∘ no $ λ where
              (success .(x ∷ l ++ v) read read≡ (Generic.mkTLV{l}{v} len val len≡ refl) suffix ps≡) → ‼
                let @0 xs≡ : pre₀ ++ suf₀ ≡ l ++ v ++ suffix
                    xs≡ = begin
                      pre₀ ++ suf₀       ≡⟨ ps≡₀ ⟩
                      xs                 ≡⟨ (sym $ ∷-injectiveʳ ps≡) ⟩
                      (l ++ v) ++ suffix ≡⟨ solve (++-monoid Dig) ⟩
                      l ++ v ++ suffix   ∎

                    @0 pre₀≡ : pre₀ ≡ l
                    pre₀≡ = Props.Length.nonnesting xs≡ len₀ len

                    @0 len≡' : getLength len ≡ getLength len₀
                    len≡' = begin
                      getLength len
                        ≡⟨ ≡-elim (λ eq → _ ≡ getLength (subst Length eq len)) refl (sym pre₀≡) ⟩
                      getLength (subst Length (sym pre₀≡) len)
                        ≡⟨ cong getLength (Props.Length.unambiguous (subst Length (sym pre₀≡) len) len₀) ⟩
                      getLength len₀
                        ∎
                in
                contradiction
                  (success v _ refl
                    (mk×ₚ val (─ trans (sym len≡) len≡') refl) suffix
                    (++-cancelˡ pre₀
                      (begin (pre₀ ++ v ++ suffix ≡⟨ cong (λ x → x ++ v ++ suffix) pre₀≡ ⟩
                              l ++ v ++ suffix    ≡⟨ solve (++-monoid Dig) ⟩
                              (l ++ v) ++ suffix  ≡⟨ ∷-injectiveʳ ps≡ ⟩
                              xs                  ≡⟨ sym ps≡₀ ⟩
                              pre₀ ++ suf₀        ∎))))
                  ¬parse
        return (yes
          (success
            (t ∷ pre₀ ++ pre₁) (1 + r₀ + r₁)
            (cong suc
              (begin (r₀ + r₁                   ≡⟨ cong (_+ r₁) r₀≡ ⟩
                      length pre₀ + r₁          ≡⟨ cong (length pre₀ +_) r₁≡ ⟩
                      length pre₀ + length pre₁ ≡⟨ (sym $ length-++ pre₀) ⟩
                      length (pre₀ ++ pre₁)     ∎)))
            (Generic.mkTLV len₀ val (sym lenVal) refl) suf₁
            (cong (x ∷_)
              (begin ((pre₀ ++ pre₁) ++ suf₁ ≡⟨ solve (++-monoid Dig) ⟩
                      pre₀ ++ pre₁ ++ suf₁   ≡⟨ cong (pre₀ ++_) ps≡₁ ⟩
                      pre₀ ++ suf₀           ≡⟨ ps≡₀ ⟩
                      xs                      ∎)))))

open parseTLV public using (parseTLV)
