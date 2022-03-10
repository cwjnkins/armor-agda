{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Properties as Props
import      Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.TLV where

open Base256
open Aeres.Grammar.Definitions Dig

module parseTLV
  (t : Dig) (tName : String) (A : List Dig → Set)
  (p : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength A n))
  where

  here' = "TLV: " String.++ tName

  open ≡-Reasoning

  parseTLV : Parser Dig (Logging ∘ Dec) (TLV t A)
  runParser parseTLV [] = do
    tell $ here' String.++ ": underflow reading tag"
    return ∘ no $ λ where
      (success .(t ∷ l ++ v) read read≡ (mkTLV {l} {v} len val len≡ refl) suffix ())
  runParser parseTLV (x ∷ xs) = do
    case x ≟ t of λ where
      (no  x≢) → do
        tell $ here' String.++ ": tag mismatch, got " String.++ String.fromList [ Char.fromℕ (toℕ x) ]
        return ∘ no $ λ where
          (success .(t ∷ l ++ v) read read≡ (mkTLV{l}{v} len val len≡ refl) suffix ps≡) →
            contradiction (sym (∷-injectiveˡ ps≡)) x≢
      (yes refl) → do
        yes (success pre₀ r₀ r₀≡ len₀ suf₀ ps≡₀) ← runParser parseLen xs
          where no ¬parse → do
            tell $ here' String.++ ": underflow parsing length"
            return ∘ no $ λ where
              (success .(x ∷ l ++ v) read read≡ (mkTLV{l}{v} len val len≡ refl) suffix ps≡) → ‼
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
              (success .(x ∷ l ++ v) read read≡ (mkTLV{l}{v} len val len≡ refl) suffix ps≡) → ‼
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
            (mkTLV len₀ val (sym lenVal) refl) suf₁
            (cong (x ∷_)
              (begin ((pre₀ ++ pre₁) ++ suf₁ ≡⟨ solve (++-monoid Dig) ⟩
                      pre₀ ++ pre₁ ++ suf₁   ≡⟨ cong (pre₀ ++_) ps≡₁ ⟩
                      pre₀ ++ suf₀           ≡⟨ ps≡₀ ⟩
                      xs                      ∎)))))

open parseTLV public using (parseTLV)

parseTLVLenBound
  : ∀ {t A} l u → Parser Dig (Logging ∘ Dec) (TLV t A)
    → Parser Dig (Logging ∘ Dec) (Σₚ (TLV t A) (TLVLenBounded l u))
runParser (parseTLVLenBound l u p) xs = do
  yes (success pre r r≡ v suf bs≡) ← runParser p xs
    where no ¬parse → do
      return ∘ no $ λ where
        (success pre' r' r'≡ (mk×ₚ v' _ refl) suf' bs≡') →
          contradiction (success pre' r' r'≡ v' suf' bs≡') ¬parse
  case inRange? l u (getLength (TLV.len v)) of λ where
    (yes l≤len≤u) →
      return (yes
        (success pre r r≡ (mk×ₚ v l≤len≤u refl) suf bs≡))
    (no  ¬l≤len≤u) → do
      tell $ "parseTLVLenBound" String.++ ": given length bounds violated"
      return ∘ no $ λ where
        (success pre' r' r'≡ (mk×ₚ v' l≤len≤u refl) suf' bs≡') → ‼
          let @0 len≡ : getLength (TLV.len v) ≡ getLength (TLV.len v')
              len≡ = TLV.getLengthLen≡ (trans₀ bs≡ (sym bs≡')) v v'
          in
          contradiction (subst (InRange l u) (sym len≡) l≤len≤u) ¬l≤len≤u

parseTLVNonEmpty
  : ∀ {t A} → Parser Dig (Logging ∘ Dec) (TLV t A)
    → Parser Dig (Logging ∘ Dec) (Σₚ (TLV t A) TLVNonEmptyVal)
runParser (parseTLVNonEmpty p) xs = do
  yes (success pre r r≡ v suf bs≡) ← runParser p xs
    where no ¬parse → do
      return ∘ no $ λ where
        (success pre' r' r'≡ (mk×ₚ v' _ refl) suf' bs≡') →
          contradiction (success pre' r' r'≡ v' suf' bs≡') ¬parse
  case 1 ≤? (getLength (TLV.len v)) of λ where
    (yes l≤len≤u) →
      return (yes
        (success pre r r≡ (mk×ₚ v l≤len≤u refl) suf bs≡))
    (no  ¬l≤len≤u) → do
      tell $ "parseTLVLenBound" String.++ ": given length bounds violated"
      return ∘ no $ λ where
        (success pre' r' r'≡ (mk×ₚ v' l≤len≤u refl) suf' bs≡') → ‼
          let @0 len≡ : getLength (TLV.len v) ≡ getLength (TLV.len v')
              len≡ = TLV.getLengthLen≡ (trans₀ bs≡ (sym bs≡')) v v'
          in
          contradiction (subst (1 ≤_) (sym len≡) l≤len≤u) ¬l≤len≤u

