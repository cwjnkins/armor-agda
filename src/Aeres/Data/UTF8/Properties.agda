{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.UTF8.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Prelude
open import Data.Nat.Properties
open import Relation.Binary
  hiding (NonEmpty)

module Aeres.Data.UTF8.Properties where

open Base256
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.IList       UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

module UTF8Char1Props where
  nonnesting : NonNesting UTF8Char1
  nonnesting xs₁++ys₁≡xs₂++ys₂ (mkUTF8Char1 b₁ b₁range refl) (mkUTF8Char1 b₂ b₁range₁ refl) =
    proj₁ $ Lemmas.length-++-≡ [ b₁ ] _ [ b₂ ] _ xs₁++ys₁≡xs₂++ys₂ refl

  noconfusion : NoConfusion UTF8Char1 (Sum UTF8Char2 (Sum UTF8Char3 UTF8Char4))
  noconfusion =
    NoConfusion.sumₚ{A = UTF8Char1} nc₁
      (NoConfusion.sumₚ{A = UTF8Char1} nc₂ nc₃)
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

    nc₂ : NoConfusion UTF8Char1 UTF8Char3
    nc₂{xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ a x =
      contradiction
        (toℕ (UTF8Char3.b₁ x) > 223 ∋ proj₁ (UTF8Char3.b₁range x))
        (<⇒≱ (subst (λ z → toℕ z < 224) b₁≡ (≤-trans (UTF8Char1.b₁range a) (toWitness{Q = 128 ≤? 224} _))))
      where
      open ≡-Reasoning

      @0 bs≡ :   UTF8Char1.b₁ a ∷ ys₁
               ≡ UTF8Char3.b₁ x ∷ UTF8Char3.b₂ x ∷ UTF8Char3.b₃ x ∷ ys₂
      bs≡ = begin
        (UTF8Char1.b₁ a ∷ ys₁ ≡⟨ cong (_++ ys₁) (sym $ UTF8Char1.bs≡ a) ⟩
        xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
        xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) (UTF8Char3.bs≡ x) ⟩
        UTF8Char3.b₁ x ∷ UTF8Char3.b₂ x ∷ UTF8Char3.b₃ x ∷ ys₂ ∎)

      @0 b₁≡ : UTF8Char1.b₁ a ≡ UTF8Char3.b₁ x
      b₁≡ = ∷-injectiveˡ (proj₁ (Lemmas.length-++-≡ [ UTF8Char1.b₁ a ] _ [ UTF8Char3.b₁ x ] _ bs≡ refl))

    nc₃ : NoConfusion UTF8Char1 UTF8Char4
    nc₃{xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ a x =
      contradiction
        (toℕ (UTF8Char4.b₁ x) > 239 ∋ proj₁ (UTF8Char4.b₁range x))
        (<⇒≱ (subst (λ z → toℕ z < 240) b₁≡ (≤-trans (UTF8Char1.b₁range a) (toWitness{Q = 128 ≤? 240} _))))
      where
      open ≡-Reasoning

      @0 bs≡ :   UTF8Char1.b₁ a ∷ ys₁
               ≡ UTF8Char4.b₁ x ∷ UTF8Char4.b₂ x ∷ UTF8Char4.b₃ x ∷ UTF8Char4.b₄ x ∷ ys₂
      bs≡ = begin
        UTF8Char1.b₁ a ∷ ys₁ ≡⟨ cong (_++ ys₁) (sym $ UTF8Char1.bs≡ a) ⟩
        xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
        xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) (UTF8Char4.bs≡ x) ⟩
        UTF8Char4.b₁ x ∷ UTF8Char4.b₂ x ∷ UTF8Char4.b₃ x ∷ UTF8Char4.b₄ x ∷ ys₂ ∎

      @0 b₁≡ : UTF8Char1.b₁ a ≡ UTF8Char4.b₁ x
      b₁≡ = ∷-injectiveˡ (proj₁ (Lemmas.length-++-≡ [ UTF8Char1.b₁ a ] _ [ UTF8Char4.b₁ x ] _ bs≡ refl))

module UTF8Char2Props where
  nonnesting : NonNesting UTF8Char2
  nonnesting xs₁++ys₁≡xs₂++ys₂ (mkUTF8Char2 b₁ b₂ b₁range b₂range refl) (mkUTF8Char2 b₃ b₄ b₁range₁ b₂range₁ refl) =
    proj₁ $ Lemmas.length-++-≡ (b₁ ∷ [ b₂ ]) _ (b₃ ∷ [ b₄ ]) _ xs₁++ys₁≡xs₂++ys₂ refl

  noconfusion : NoConfusion UTF8Char2 (Sum UTF8Char3 UTF8Char4)
  noconfusion =
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

module UTF8Char3Props where
  nonnesting : NonNesting UTF8Char3
  nonnesting xs₁++ys₁≡xs₂++ys₂ (mkUTF8Char3 b₁ b₂ b₃ b₁range b₂range b₃range refl) (mkUTF8Char3 b₄ b₅ b₆ b₁range₁ b₂range₁ b₃range₁ refl) =
    proj₁ (Lemmas.length-++-≡ (b₁ ∷ b₂ ∷ [ b₃ ]) _ (b₄ ∷ b₅ ∷ [ b₆ ]) _ xs₁++ys₁≡xs₂++ys₂ refl)

  Rep : @0 List UInt8 → Set
  Rep =
    Σₚ (ExactLengthString 3)
      λ _ els →
        Erased
          (InRange 224 239 (lookupELS els (# 0))
           × InRange 128 191 (lookupELS els (# 1))
           × InRange 128 191 (lookupELS els (# 2)))

  iso : Iso Rep UTF8Char3
  proj₁ (proj₁ iso) (mk×ₚ els@(mk×ₚ (singleton (b₁ ∷ b₂ ∷ b₃ ∷ [] ) refl) sndₚ₂ refl) (─ (b₁range , b₂range , b₃range)) refl) =
    mkUTF8Char3 (lookupELS els (# 0)) (lookupELS els (# 1)) (lookupELS els (# 2))
      b₁range b₂range b₃range refl
  proj₂ (proj₁ iso) (mkUTF8Char3 b₁ b₂ b₃ b₁range b₂range b₃range refl) =
    mk×ₚ (mk×ₚ self (─ refl) refl) (─ (b₁range , b₂range , b₃range)) refl
  proj₁ (proj₂ iso) (mk×ₚ (mk×ₚ (singleton (b₁ ∷ b₂ ∷ b₃ ∷ [] ) refl) (─ refl) refl) (─ (b₁range , b₂range , b₃range)) refl) =
    refl
  proj₂ (proj₂ iso) (mkUTF8Char3 b₁ b₂ b₃ b₁range b₂range b₃range refl) =
    refl

  noconfusion : NoConfusion UTF8Char3 UTF8Char4
  noconfusion{xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ a x =
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


module UTF8Char4Props where
  nonnesting : NonNesting UTF8Char4
  nonnesting xs₁++ys₁≡xs₂++ys₂ (mkUTF8Char4 b₁ b₂ b₃ b₄ b₁range b₂range b₃range b₄ranger refl) (mkUTF8Char4 b₅ b₆ b₇ b₈ b₁range₁ b₂range₁ b₃range₁ b₄range₁ refl) =
    proj₁ (Lemmas.length-++-≡ (b₁ ∷ b₂ ∷ b₃ ∷ [ b₄ ]) _ (b₅ ∷ b₆ ∷ b₇ ∷ [ b₈ ]) _ xs₁++ys₁≡xs₂++ys₂ refl)

  Rep : @0 List UInt8 → Set
  Rep =
    Σₚ (ExactLengthString 4)
      λ _ els →
        Erased
          (  InRange 240 247 (lookupELS els (# 0))
           × InRange 128 191 (lookupELS els (# 1))
           × InRange 128 191 (lookupELS els (# 2))
           × InRange 128 191 (lookupELS els (# 3)))

  equiv : Equivalent Rep UTF8Char4
  proj₁ equiv (mk×ₚ (mk×ₚ (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) refl) (─ refl) refl) (─ (fst , fst₁ , fst₂ , snd)) refl) =
    mkUTF8Char4 x x₁ x₂ x₃ fst fst₁ fst₂ snd refl
  proj₂ equiv (mkUTF8Char4 b₁ b₂ b₃ b₄ b₁range b₂range b₃range b₄range bs≡) =
    mk×ₚ (mk×ₚ (singleton (b₁ ∷ b₂ ∷ b₃ ∷ [ b₄ ]) refl) (─ refl) refl) (─ (b₁range , b₂range , b₃range , b₄range)) (sym bs≡)


module UTF8CharProps where
  Rep : @0 List UInt8 → Set
  Rep =  Sum UTF8Char1
        (Sum UTF8Char2
        (Sum UTF8Char3
             UTF8Char4))

  equiv : Equivalent Rep UTF8Char
  proj₁ equiv (inj₁ u1) = utf81 u1
  proj₁ equiv (inj₂ (inj₁ x)) = utf82 x
  proj₁ equiv (inj₂ (inj₂ (inj₁ x))) = utf83 x
  proj₁ equiv (inj₂ (inj₂ (inj₂ x))) = utf84 x
  proj₂ equiv (utf81 x) = inj₁ x
  proj₂ equiv (utf82 x) = inj₂ (inj₁ x)
  proj₂ equiv (utf83 x) = inj₂ (inj₂ (inj₁ x))
  proj₂ equiv (utf84 x) = inj₂ (inj₂ (inj₂ x))

  nonempty : NonEmpty UTF8Char
  nonempty (utf81 ()) refl
  nonempty (utf82 ()) refl
  nonempty (utf83 ()) refl
  nonempty (utf84 ()) refl

  nonnesting : NonNesting UTF8Char
  nonnesting =
    equivalent-nonnesting equiv
      (nonnestingSum
        UTF8Char1Props.nonnesting
        (nonnestingSum UTF8Char2Props.nonnesting
          (nonnestingSum
            UTF8Char3Props.nonnesting
            UTF8Char4Props.nonnesting
            UTF8Char3Props.noconfusion)
          UTF8Char2Props.noconfusion)
        UTF8Char1Props.noconfusion)
