{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.UTF8.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Prelude
open import Data.Nat.Properties

module Aeres.Data.UTF8.Properties where

open Base256
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.IList       UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

noconfusion₃ : NoConfusion UTF8Char3 UTF8Char4
noconfusion₃{xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ a x =
  contradiction
    (toℕ (UTF8Char4.b₁ x) > 239 ∋ proj₁ (UTF8Char4.b₁range x))
    (<⇒≱ (subst₀ (λ z → toℕ z < 240) b₁≡ (s≤s $ proj₂ (UTF8Char3.b₁range a))))
  where
  open ≡-Reasoning

  @0 bs≡ :   UTF8Char3.b₁ a ∷ UTF8Char3.b₂ a ∷ UTF8Char3.b₃ a ∷ ys₁
           ≡ UTF8Char4.b₁ x ∷ UTF8Char4.b₂ x ∷ UTF8Char4.b₃ x ∷ UTF8Char4.b₄ x ∷ ys₂
  bs≡ = begin
    (UTF8Char3.b₁ a ∷ UTF8Char3.b₂ a ∷ UTF8Char3.b₃ a ∷ ys₁ ≡⟨ cong (_++ ys₁) (sym $ UTF8Char3.bs≡ a) ⟩
    xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
    xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) (UTF8Char4.bs≡ x) ⟩
    UTF8Char4.b₁ x ∷ UTF8Char4.b₂ x ∷ UTF8Char4.b₃ x ∷ UTF8Char4.b₄ x ∷ ys₂ ∎)

  @0 b₁≡ : UTF8Char3.b₁ a ≡ UTF8Char4.b₁ x
  b₁≡ = ∷-injectiveˡ (proj₁ (Lemmas.length-++-≡ [ UTF8Char3.b₁ a ] _ [ UTF8Char4.b₁ x ] _ bs≡ refl))

noconfusion₂ : NoConfusion UTF8Char2 (Sum UTF8Char3 UTF8Char4)
noconfusion₂ =
  NoConfusion.sumₚ{A = UTF8Char2} nc₁ nc₂
  where
  nc₁ : NoConfusion UTF8Char2 UTF8Char3
  nc₁{xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ a x =
    contradiction
      (toℕ (UTF8Char3.b₁ x) > 223 ∋ proj₁ (UTF8Char3.b₁range x))
      (<⇒≱ (subst (λ z → toℕ z < 224) b₁≡ (s≤s (proj₂ (UTF8Char2.b₁range a)))))
    where
    open ≡-Reasoning

    @0 bs≡ :   UTF8Char2.b₁ a ∷ UTF8Char2.b₂ a ∷ ys₁
             ≡ UTF8Char3.b₁ x ∷ UTF8Char3.b₂ x ∷ UTF8Char3.b₃ x ∷ ys₂
    bs≡ = begin
      (UTF8Char2.b₁ a ∷ UTF8Char2.b₂ a ∷ ys₁ ≡⟨ cong (_++ ys₁) (sym $ UTF8Char2.bs≡ a) ⟩
      xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
      xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) (UTF8Char3.bs≡ x) ⟩
      UTF8Char3.b₁ x ∷ UTF8Char3.b₂ x ∷ UTF8Char3.b₃ x ∷ ys₂ ∎)

    @0 b₁≡ : UTF8Char2.b₁ a ≡ UTF8Char3.b₁ x
    b₁≡ = ∷-injectiveˡ (proj₁ (Lemmas.length-++-≡ [ UTF8Char2.b₁ a ] _ [ UTF8Char3.b₁ x ] _ bs≡ refl))

  nc₂ : NoConfusion UTF8Char2 UTF8Char4
  nc₂{xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ a x =
    contradiction
      (toℕ (UTF8Char4.b₁ x) > 239 ∋ proj₁ (UTF8Char4.b₁range x))
      (<⇒≱ (subst (λ z → toℕ z < 240) b₁≡ (≤-trans (s≤s (proj₂ (UTF8Char2.b₁range a))) (toWitness{Q = 224 ≤? 240} _))))
    where
    open ≡-Reasoning

    @0 bs≡ :   UTF8Char2.b₁ a ∷ UTF8Char2.b₂ a ∷ ys₁
             ≡ UTF8Char4.b₁ x ∷ UTF8Char4.b₂ x ∷ UTF8Char4.b₃ x ∷ UTF8Char4.b₄ x ∷ ys₂
    bs≡ = begin
      (UTF8Char2.b₁ a ∷ UTF8Char2.b₂ a ∷ ys₁ ≡⟨ cong (_++ ys₁) (sym $ UTF8Char2.bs≡ a) ⟩
      xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
      xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) (UTF8Char4.bs≡ x) ⟩
      UTF8Char4.b₁ x ∷ UTF8Char4.b₂ x ∷ UTF8Char4.b₃ x ∷ UTF8Char4.b₄ x ∷ ys₂ ∎)

    @0 b₁≡ : UTF8Char2.b₁ a ≡ UTF8Char4.b₁ x
    b₁≡ = ∷-injectiveˡ (proj₁ (Lemmas.length-++-≡ [ UTF8Char2.b₁ a ] _ [ UTF8Char4.b₁ x ] _ bs≡ refl))

noconfusion₁ : NoConfusion UTF8Char1 (Sum UTF8Char2 (Sum UTF8Char3 UTF8Char4))
noconfusion₁ =
  NoConfusion.sumₚ{A = UTF8Char1} {!!}
    (NoConfusion.sumₚ {A = UTF8Char1} {!!} {!!})
  where
  nc₁ : NoConfusion UTF8Char1 UTF8Char2
  nc₁{xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ a x =
    contradiction
      (toℕ (UTF8Char2.b₁ x) > 191 ∋ proj₁ (UTF8Char2.b₁range x))
      (<⇒≱ (subst (λ z → toℕ z < 192) b₁≡ (≤-trans (UTF8Char1.b₁range a) (toWitness{Q = 128 ≤? 192} _))))
    where
    open ≡-Reasoning

    @0 bs≡ :   UTF8Char1.b₁ a ∷ ys₁
             ≡ UTF8Char2.b₁ x ∷ UTF8Char2.b₂ x ∷ ys₂
    bs≡ = begin
      (UTF8Char1.b₁ a ∷ ys₁ ≡⟨ cong (_++ ys₁) (sym $ UTF8Char1.bs≡ a) ⟩
      xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
      xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) (UTF8Char2.bs≡ x) ⟩
      UTF8Char2.b₁ x ∷ UTF8Char2.b₂ x ∷ ys₂ ∎)

    @0 b₁≡ : UTF8Char1.b₁ a ≡ UTF8Char2.b₁ x
    b₁≡ = ∷-injectiveˡ (proj₁ (Lemmas.length-++-≡ [ UTF8Char1.b₁ a ] _ [ UTF8Char2.b₁ x ] _ bs≡ refl))

  -- nc₂ : NoConfusion UTF8Char2 UTF8Char4
  -- nc₂{xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ a x =
  --   contradiction
  --     (toℕ (UTF8Char4.b₁ x) > 239 ∋ proj₁ (UTF8Char4.b₁range x))
  --     (<⇒≱ (subst (λ z → toℕ z < 240) b₁≡ (≤-trans (s≤s (proj₂ (UTF8Char2.b₁range a))) (toWitness{Q = 224 ≤? 240} _))))
  --   where
  --   open ≡-Reasoning

  --   @0 bs≡ :   UTF8Char2.b₁ a ∷ UTF8Char2.b₂ a ∷ ys₁
  --            ≡ UTF8Char4.b₁ x ∷ UTF8Char4.b₂ x ∷ UTF8Char4.b₃ x ∷ UTF8Char4.b₄ x ∷ ys₂
  --   bs≡ = begin
  --     (UTF8Char2.b₁ a ∷ UTF8Char2.b₂ a ∷ ys₁ ≡⟨ cong (_++ ys₁) (sym $ UTF8Char2.bs≡ a) ⟩
  --     xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
  --     xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) (UTF8Char4.bs≡ x) ⟩
  --     UTF8Char4.b₁ x ∷ UTF8Char4.b₂ x ∷ UTF8Char4.b₃ x ∷ UTF8Char4.b₄ x ∷ ys₂ ∎)

  --   @0 b₁≡ : UTF8Char2.b₁ a ≡ UTF8Char4.b₁ x
  --   b₁≡ = ∷-injectiveˡ (proj₁ (Lemmas.length-++-≡ [ UTF8Char2.b₁ a ] _ [ UTF8Char4.b₁ x ] _ bs≡ refl))

