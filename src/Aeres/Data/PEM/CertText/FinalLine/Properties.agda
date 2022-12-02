{-# OPTIONS --subtyping #-}


open import Aeres.Binary
  renaming (module Base64 to B64)
open import Aeres.Data.Base64
open import Aeres.Data.PEM.CertText.FinalLine.TCB
open import Aeres.Data.PEM.CertText.FullLine.TCB
open import Aeres.Data.PEM.RFC5234.TCB
import      Aeres.Data.PEM.RFC5234.Properties as RFC5234
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
open import Aeres.Prelude
import      Data.Nat.Properties as Nat
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.PEM.CertText.FinalLine.Properties where

open Aeres.Grammar.Definitions Char
open Aeres.Grammar.IList       Char

Rep : @0 List Char → Set
Rep = Σₚ (&ₚ Base64Str EOL)
         (λ _ → Erased ∘ InRange 1 64 ∘ length ∘ &ₚᵈ.bs₁ )

equiv : Equivalent Rep CertFinalLine
proj₁ equiv (mk×ₚ (mk&ₚ fstₚ₁ sndₚ₂ refl) (─ range) refl) =
  mkCertFinalLine fstₚ₁ range sndₚ₂ refl
proj₂ equiv (mkCertFinalLine line lineLen eol refl) =
  mk×ₚ (mk&ₚ line eol refl) (─ lineLen) refl

fromCertFullLine : ∀ {@0 bs} → CertFullLine bs → CertFinalLine bs
fromCertFullLine (mkCertFullLine (mk×ₚ line (─ lineLen) refl) eol refl) =
  mkCertFinalLine
    (Base64.Str.fromExactLength (mk×ₚ line (─ lineLen) refl))
      (Nat.≤-trans (toWitness{Q = 1 ≤? 64} tt) (Lemmas.≡⇒≤ (sym lineLen))
    , Lemmas.≡⇒≤ lineLen)
    eol refl

@0 char₁ : ∀ {@0 b bs} → CertFinalLine (b ∷ bs) → b ∈ B64.charset
char₁{b} (mkCertFinalLine{l}{e} (mk64Str  nil strLen pad refl) (str> , str<) eol bs≡) =
  Base64.Pad.char₁ (subst₀ Base64Pad (sym $ proj₂ l≡) pad)
  where
  @0 l≡ : Σ[ l' ∈ List Char ] (b ∷ l') ≡ l
  l≡ = caseErased (singleton l refl) ret (const _) of λ where
    (singleton [] refl) → contradiction str> λ ()
    (singleton (x ∷ x₁) refl) → ─ (x₁ , cong (_∷ x₁) (∷-injectiveˡ bs≡))
char₁{b}{bs} (mkCertFinalLine{e = e} (mk64Str{p = p} (consIList{bs₁}{bs₂} (mk64 c c∈ i refl) t refl) strLen pad refl) (str> , str<) eol bs≡) =
  subst₀ (_∈ B64.charset) (sym (∷-injectiveˡ bs≡)) c∈
  where
  open ≡-Reasoning


@0 lengthRange : ∀ {@0 bs} → CertFinalLine bs → InRange 2 66 (length bs)
lengthRange{bs} (mkCertFinalLine{l}{e} line lineLen eol bs≡) =
    (≤.begin
      2 ≤.≤⟨ Nat.+-mono-≤ (proj₁ lineLen) (proj₁ $ RFC5234.EOL.eolLen eol) ⟩
      length l + length e ≤.≡⟨ sym (length-++ l) ⟩
      length (l ++ e) ≤.≡⟨ cong length (sym bs≡) ⟩
      length bs ≤.∎ )
  , (≤.begin
      (length bs ≤.≡⟨ cong length bs≡ ⟩
      length (l ++ e) ≤.≡⟨ length-++ l ⟩
      length l + length e ≤.≤⟨ Nat.+-mono-≤ (proj₂ lineLen) (proj₂ $ RFC5234.EOL.eolLen eol) ⟩
      66 ≤.∎))
  where
  module ≤ = Nat.≤-Reasoning
