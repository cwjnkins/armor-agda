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
    → Decidable A → (∀ xs → Unique (A xs))
    → (∀ {@0 xs₁} → (d : A xs₁) → Parser (M ∘ Dec) (B d ∘ (Vec.toList xs₁ ++_)))
    → Parser (M ∘ Dec) (DSum{n} A B)
runParser (parse{n = n}{A = A}{B = B} underflow notFound ¬pb d? uA p) xs = do
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
      (yes (success pre₂ r₂ r₂≡ v₂ suf₂ ps≡₂)) ← runParser (p discr) suf₁
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

                value' : B{look'} discr (Vec.toList look' ++ drop n prefix)
                value' =
                  case look≡' ret (const _) of λ where
                    (─ refl) → case uA look' discr discr' ret (const _) of λ where
                      refl →
                        subst₀ (B discr)
                          (begin
                            prefix ≡⟨ sym (take++drop n prefix) ⟩
                            take n prefix ++ drop n prefix ≡⟨ cong (_++ drop n prefix) (sym look≡) ⟩
                            Vec.toList look' ++ drop n prefix ∎)
                          value
              in
              contradiction
                (success (drop n prefix) _ refl value' suffix
                  (++-cancelˡ look
                    (begin
                      look ++ drop n prefix ++ suffix ≡⟨ cong (_++ drop n prefix ++ suffix)
                        (begin
                          look ≡⟨ sym (Vec.toList∘fromList look) ⟩
                          Vec.toList (Vec.fromList look)
                            ≡⟨ ≡-elim (λ eq → Vec.toList (Vec.fromList look) ≡ Vec.toList (subst₀ (Vec Σ) eq (Vec.fromList look))) refl v₁Len ⟩
                          Vec.toList look' ≡⟨ cong Vec.toList (¡ look≡') ⟩
                          Vec.toList look“ ≡⟨ look≡ ⟩
                          take n prefix ∎) ⟩
                      take n prefix ++ drop n prefix ++ suffix ≡⟨ sym (++-assoc (take n prefix) (drop n prefix) suffix) ⟩
                      (take n prefix ++ drop n prefix) ++ suffix ≡⟨ cong (_++ suffix) (take++drop n prefix) ⟩
                      prefix ++ suffix ≡⟨ ps≡ ⟩
                      xs ≡⟨ sym ps≡₁ ⟩
                      look ++ suf₁ ∎)))
                ¬p
      let
        look≡ : Erased (Vec.toList look' ≡ look)
        look≡ = ─
          (caseErased v₁Len ret (λ eq → Vec.toList (subst₀ (Vec Σ) eq (Vec.fromList look)) ≡ look) of λ where
            refl → ─ Vec.toList∘fromList look)

        v₂' : B discr (look ++ pre₂)
        v₂' = subst₀ (λ x → B discr (x ++ pre₂)) (¡ look≡) v₂

        look≡' : Erased (Vec.toList look' ≡ take n (look ++ pre₂))
        look≡' = ─
          (begin
            (Vec.toList look' ≡⟨ ¡ look≡ ⟩
            look ≡⟨ sym (Lemmas.take-length-++ look pre₂) ⟩
            take (length look) (look ++ pre₂) ≡⟨ cong (λ x → take x (look ++ pre₂)) v₁Len ⟩
            take n (look ++ pre₂) ∎))
      return (yes
        (success (look ++ pre₂)
          (n + r₂)
          (begin
            n + r₂ ≡⟨ cong₂ _+_ (sym v₁Len) r₂≡ ⟩
            length look + length pre₂ ≡⟨ sym (length-++ look ) ⟩
            length (look ++ pre₂) ∎)
          (mkDSum discr v₂' (¡ look≡'))
          suf₂
          (begin
            (look ++ pre₂) ++ suf₂ ≡⟨ ++-assoc look pre₂ suf₂ ⟩
            look ++ pre₂ ++ suf₂ ≡⟨ cong (look ++_) ps≡₂ ⟩
            look ++ suf₁ ≡⟨ ps≡₁ ⟩
            xs ∎)))
      -- let
      --   look≡ : Erased (Vec.toList look' ≡ take n pre₂)
      --   look≡ = ─ (
      --     caseErased v₁Len ret (λ eq → Vec.toList (subst₀ (Vec Σ) eq (Vec.fromList look)) ≡ take n pre₂) of λ where
      --       refl → ─ (begin
      --         Vec.toList (Vec.fromList look) ≡⟨ Vec.toList∘fromList look ⟩
      --         look ≡⟨ {!!} ⟩
      --         take n (look ++ suf₁) ≡⟨ {!!} ⟩
      --         take n xs ≡⟨ {!!} ⟩
      --         take n (pre₂ ++ suf₂) ≡⟨ {!!} ⟩
      --         {!!}))
  where
  open ≡-Reasoning
  import Data.Nat.Properties as Nat
  module ≤ = Nat.≤-Reasoning
  import Data.Vec.Properties as Vec
