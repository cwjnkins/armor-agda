{-# OPTIONS --subtyping #-}

import      Aeres.Grammar.DSum.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Grammar.DSum.Parser (Σ : Set) where

open Aeres.Grammar.DSum.TCB    Σ
open Aeres.Grammar.Definitions Σ
open Aeres.Grammar.Parser      Σ

parse
  : ∀ {M n} → ⦃ _ : Monad M ⦄
    → {A : Vec Σ n → Set} {B : {xs : Vec Σ n} → A xs → List Σ → Set}
    → (underflow notFound ¬pb : M (Level.Lift _ ⊤))
    → Decidable A → @0 (∀ xs → Unique (A xs))
    → @0 (∀ {xs₁ xs₂} → (d : A xs₁) → B d xs₂ → n ≤ length xs₂)
    → (∀ {@0 xs₁} → (d : A xs₁) → Parser (M ∘ Dec) (B d))
    → Parser (M ∘ Dec) (DSum{n} A B)
runParser (parse{n = n}{A = A}{B = B} underflow notFound ¬pb d? uA bLen p) xs = do
  (yes (success .look ._ refl (mk×ₚ (singleton look refl) (─ v₁Len) refl) suf₁ ps≡₁)) ← runParser (parseN n underflow) xs
    where no ¬p → do
      notFound
      return ∘ no $ λ where
        (success prefix read read≡ (mkDSum{look = look} discr value look≡) suffix ps≡) →
          contradiction
            (success (Vec.toList look) _ refl
              (mk×ₚ self (─ (Lemmas.toListLength look)) refl)
              (drop n prefix ++ suffix)
              (begin
                Vec.toList look ++ drop n prefix ++ suffix ≡⟨ cong (_++ drop n prefix ++ suffix) look≡ ⟩
                take n prefix ++ drop n prefix ++ suffix ≡⟨ sym (++-assoc (take n prefix) (drop n prefix) suffix) ⟩
                (take n prefix ++ drop n prefix) ++ suffix ≡⟨ cong (_++ suffix) (take++drop n prefix) ⟩
                prefix ++ suffix ≡⟨ ps≡ ⟩
                xs ∎))
            ¬p
  let look' : Vec Σ n
      look' = subst₀ (Vec Σ) v₁Len (Vec.fromList look)
  case d? look' ret (const _) of λ where
    (no ¬p) → do
      notFound
      return ∘ no $ λ where
        (success prefix read read≡ (mkDSum{look = look“} discr value look≡) suffix ps≡) →
          let
            length-look : Erased (length look ≤ length prefix)
            length-look = ─ (≤.begin
              length look ≤.≡⟨ v₁Len ⟩
              n ≤.≡⟨ sym (Lemmas.toListLength look“) ⟩
              length (Vec.toList look“) ≤.≡⟨ cong length look≡ ⟩
              length (take n prefix) ≤.≡⟨ length-take n prefix ⟩
              n ⊓ length prefix ≤.≤⟨ Nat.m⊓n≤n n (length prefix) ⟩
              length prefix ≤.∎)

            look≡' : Erased (look' ≡ look“)
            look≡' = ─
              (caseErased v₁Len ret (λ eq → subst₀ (Vec Σ) eq (Vec.fromList look) ≡ look“) of λ where
                refl → ─ Lemmas.toList-injective (Vec.fromList look) look“
                  (begin
                    Vec.toList (Vec.fromList look) ≡⟨ Vec.toList∘fromList look ⟩
                    look ≡⟨ (sym $ Lemmas.take-length-++ look suf₁) ⟩
                    take n (look ++ suf₁) ≡⟨ cong (take n) ps≡₁ ⟩
                    take n xs ≡⟨ cong (take n) (sym ps≡) ⟩
                    take n (prefix ++ suffix) ≡⟨ Lemmas.take-≤-length-++ n prefix suffix (¡ length-look) ⟩
                    take n prefix ≡⟨ sym look≡ ⟩
                    Vec.toList look“ ∎))
          in
          contradiction (subst A (sym (¡ look≡')) discr) ¬p
    (yes discr) → do
      -- try 1
      (yes (success pre₂ r₂ r₂≡ v₂ suf₂ ps≡₂)) ← runParser (p discr) xs
        where no ¬p → do
          ¬pb
          return ∘ no $ λ where
            (success prefix read read≡ (mkDSum{look = look“} discr' value look≡) suffix ps≡) →
              let
                length-look : Erased (length look ≤ length prefix)
                length-look = ─ (≤.begin
                  length look ≤.≡⟨ v₁Len ⟩
                  n ≤.≡⟨ sym (Lemmas.toListLength look“) ⟩
                  length (Vec.toList look“) ≤.≡⟨ cong length look≡ ⟩
                  length (take n prefix) ≤.≡⟨ length-take n prefix ⟩
                  n ⊓ length prefix ≤.≤⟨ Nat.m⊓n≤n n (length prefix) ⟩
                  length prefix ≤.∎)
    
                look≡' : Erased (look' ≡ look“)
                look≡' = ─
                  (caseErased v₁Len ret (λ eq → subst₀ (Vec Σ) eq (Vec.fromList look) ≡ look“) of λ where
                    refl → ─ Lemmas.toList-injective (Vec.fromList look) look“
                      (begin
                        Vec.toList (Vec.fromList look) ≡⟨ Vec.toList∘fromList look ⟩
                        look ≡⟨ (sym $ Lemmas.take-length-++ look suf₁) ⟩
                        take n (look ++ suf₁) ≡⟨ cong (take n) ps≡₁ ⟩
                        take n xs ≡⟨ cong (take n) (sym ps≡) ⟩
                        take n (prefix ++ suffix) ≡⟨ Lemmas.take-≤-length-++ n prefix suffix (¡ length-look) ⟩
                        take n prefix ≡⟨ sym look≡ ⟩
                        Vec.toList look“ ∎))

                discr“ : A look'
                discr“ = subst₀ A (sym (¡ look≡')) discr'

                value' : B discr prefix
                value' =
                  case look≡' ret (const _) of λ where
                    (─ refl) →
                      case (‼ uA look' discr discr') ret (const _) of λ where
                        refl → value
              in
              contradiction (success prefix _ refl value' suffix ps≡) ¬p
      let
        lookPrefix : Erased (Vec.toList look' ≡ take n pre₂)
        lookPrefix = ─ (caseErased v₁Len ret (λ eq → Vec.toList (subst₀ (Vec Σ) eq (Vec.fromList look)) ≡ take n pre₂) of λ where
          refl → ─
            (begin
              Vec.toList (Vec.fromList look) ≡⟨ Vec.toList∘fromList look ⟩
              look ≡⟨ (sym $ Lemmas.take-length-++ look suf₁) ⟩
              take n (look ++ suf₁) ≡⟨ cong (take n) (trans ps≡₁ (sym ps≡₂)) ⟩
              take n (pre₂ ++ suf₂) ≡⟨ Lemmas.take-≤-length-++ n pre₂ suf₂ (bLen discr v₂) ⟩
              take n pre₂ ∎))
      return (yes
        (success pre₂ _ r₂≡ (mkDSum{look = look'} discr v₂ (¡ lookPrefix)) _ ps≡₂))
  where
  open ≡-Reasoning
  import Data.Nat.Properties as Nat
  module ≤ = Nat.≤-Reasoning
  import Data.Vec.Properties as Vec
