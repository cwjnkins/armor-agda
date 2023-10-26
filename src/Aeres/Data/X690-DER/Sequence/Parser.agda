{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Default
open import Aeres.Data.X690-DER.Sequence.Properties
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X690-DER.Sequence.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Seq         UInt8

module _ {A : @0 List UInt8 → Set} ⦃ _ : Eq≋ A ⦄ {@0 bs' : List UInt8} (default : A bs') (loc : String) where
  parseDefault₁
    : ∀ {B} → @0 Unambiguous A → @0 NoSubstrings A → @0 NoConfusion A B
      → Parser (Logging ∘ Dec) A → Parser (Logging ∘ Dec) B
      → Parser (Logging ∘ Dec) (&ₚ (Default A default) B)
  runParser (parseDefault₁ ua₁ ns₁ nc p₁ p₂) xs = do
    (yes (success pre r r≡ (mk&ₚ{pre₁}{pre₂} oa b refl) suf ps≡)) ← runParser (parseOption₁ loc ns₁ p₁ p₂) xs
      where no ¬p → do
        return ∘ no $ λ where
          (success pre r r≡ (mk&ₚ (mkDefault oa _) b refl) suf ps≡) →
            contradiction (success pre r r≡ (mk&ₚ oa b refl) suf ps≡)
            ¬p
    case Default.notDefault? {bs' = bs'} default oa ret (const _) of λ where
      (no ¬p) → do
        let
          a : Σ (A pre₁) ((oa ≡_) ∘ some)
          a = case (singleton oa refl) ret (const _) of λ where
            (singleton none refl) → contradiction tt ¬p
            (singleton (some x) refl) → x ,e refl{A = Option A pre₁}
        tell $ loc String.++ ": explicit default value"
        return ∘ no $ λ where
          (success pre' r' r'≡ (mk&ₚ (mkDefault none nd) b' refl) suf' ps≡') →
            let
              @0 ++≡ : pre₁ ++ pre₂ ++ suf ≡ pre' ++ suf'
              ++≡ = begin
                pre₁ ++ pre₂ ++ suf ≡⟨ sym (++-assoc pre₁ pre₂ suf) ⟩
                (pre₁ ++ pre₂) ++ suf ≡⟨ ps≡ ⟩
                _ ≡⟨ sym ps≡' ⟩
                pre' ++ suf' ∎
            in
            contradiction
              b'
              (nc ++≡ (proj₁ a))
          (success pre' r' r'≡ (mk&ₚ{pre₁'}{pre₂'} (mkDefault (some a') nd) b' refl) suf' ps≡') →
            let
              @0 ++≡ : pre₁ ++ pre₂ ++ suf ≡ pre₁' ++ pre₂' ++ suf'
              ++≡ = begin
                pre₁ ++ pre₂ ++ suf ≡⟨ sym (++-assoc pre₁ pre₂ suf) ⟩
                (pre₁ ++ pre₂) ++ suf ≡⟨ ps≡ ⟩
                _ ≡⟨ sym ps≡' ⟩
                (pre₁' ++ pre₂') ++ suf' ≡⟨ ++-assoc pre₁' pre₂' suf' ⟩
                _ ∎
            in
            ‼
            (case ns₁ ++≡ (proj₁ a) a' ret (const _) of λ where
              refl →
                contradiction
                  (subst (Default.NotDefault default)
                    (some a' ≡ oa ∋ (trans (cong some (ua₁ a' (proj₁ a))) (sym (proj₂ a))))
                    nd)
                  ¬p)
      (yes p) → return (yes
        (success pre r r≡ (mk&ₚ (mkDefault oa p) b refl) suf ps≡))
    where
    open ≡-Reasoning
