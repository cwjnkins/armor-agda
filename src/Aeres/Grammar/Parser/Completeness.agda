{-# OPTIONS --subtyping #-}

import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser.Core
open import Aeres.Prelude

module Aeres.Grammar.Parser.Completeness (Σ : Set) where

open Aeres.Grammar.Definitions Σ
open Aeres.Grammar.Parser.Core Σ

module Definitions (M : Set → Set) (extract : ∀ {G} {@0 bs} → M (Success G bs) → Dec (Success G bs)) where

  infix 2 ∃[]-syntax
  ∃[]-syntax = Σ-syntax
  syntax ∃[]-syntax A (λ x → B) = ∃[ x ∈ A ] B

  Sound : ∀ {G : @0 List Σ → Set} → Parser M G → Set
  Sound{G} p = ∀ xs → (w : True (extract (runParser p xs))) → G (Success.prefix (toWitness w))

  WeaklyComplete : ∀ {G} → Parser M G → Set
  WeaklyComplete{G} p = ∀ xs → G xs → True (extract (runParser p xs))

  StronglyComplete : ∀ {G : @0 List Σ → Set} → Parser M G → Set
  StronglyComplete{G} p = ∀ xs → (xsInG : G xs) → ∃[ w ∈ True (extract (runParser p xs)) ] _≡_ {A = Exists─ _ G} (─ _ , xsInG) (─ _ , Success.value (toWitness w))

module Proofs (M : Set → Set) (extract : ∀ {G} {@0 bs} → M (Success G bs) → Dec (Success G bs)) where
  open Definitions M extract

  @0 soundness : ∀ {G} (p : Parser M G) → Sound p
  soundness p xs w = Success.value (toWitness w)

  private
    trivSuccess : ∀ {G : @0 List Σ → Set} {xs} → G xs → Success G xs
    trivSuccess{xs = xs} xs∈G = success xs (length xs) refl xs∈G [] (++-identityʳ xs)

  @0 weakCompleteness : ∀ {G} (p : Parser M G) → WeaklyComplete p
  weakCompleteness p xs xsInG = fromWitness {Q = extract (runParser p xs)} (trivSuccess xsInG)

  @0 strongCompleteness : ∀ {G : @0 List Σ → Set} (p : Parser M G) → Unambiguous G → NoSubstrings G → StronglyComplete p
  strongCompleteness{G} p ua nn xs xs∈G = w , secure xs xs∈G s
    where
    w = weakCompleteness p xs xs∈G
    s = toWitness w
    @0 secure : ∀ xs (inG : G xs) s → (─ _ , inG) ≡ (─ _ , Success.value s)
    secure xs inG (success prefix read read≡ value suffix ps≡) =
      case nn (trans (++-identityʳ xs) (‼ sym ps≡)) inG value ret (const _) of λ where
        refl → case ‼ ua inG value ret (const _) of λ where
          refl → refl
    -- case extract (runParser p xs) ret (λ d → True d And λ s → _≡_{A = Exists─ _ G} (─ _ , xs∈G) (─ Success.prefix s , Success.value s)) of λ where
    --   (no ¬s) → contradiction (success xs _ refl xs∈G [] (++-identityʳ xs)) ¬s
    --   (yes (success prefix _ _ v suffix ps≡)) →
    --    case ‼ nn (trans (++-identityʳ xs) (‼ sym ps≡)) xs∈G v ret (const _) of λ where
    --       refl → case ‼ ua xs∈G v ret (const _) of λ where
    --         refl → refl

-- UniqueParse : (List Σ → Set) → Set
-- UniqueParse A = ∀ {@0 bs} → Unique (Success A bs)

-- CompleteParse : (A : List Σ → Set) (M : Set → Set)
--                 → (extract : ∀ {@0 bs} → M (Dec (Success A bs)) → Dec (Success A bs))
--                 → (parser : Parser (M ∘ Dec) A)
--                 → Set
-- CompleteParse A M extract parser =
--   ∀ {bs} → (v : Success A bs) → True extract (runParser parser bs) And (v ≡_) 

-- module _ {@0 A : List Σ → Set} (unambiguousA : Unambiguous A) (nonnestingA : NonNesting A) where

--   @0 uniqueParse : UniqueParse A
--   uniqueParse p₁ p₂
--     with ‼ nonnestingA (trans (Success.ps≡ p₁) (sym (Success.ps≡ p₂))) (Success.value p₁) (Success.value p₂)
--   ... | refl
--     with ‼ Lemmas.++-cancel≡ˡ (Success.prefix p₁) _ refl (trans (Success.ps≡ p₁) (sym (Success.ps≡ p₂)))
--   ... | refl
--     with ‼ (trans (Success.read≡ p₁) (sym (Success.read≡ p₂)))
--   ... | refl
--     with ‼ ≡-unique (Success.read≡ p₂) (Success.read≡ p₁)
--     |    ‼ ≡-unique (Success.ps≡ p₂) (Success.ps≡ p₁)
--   ... | refl | refl
--     with ‼ unambiguousA (Success.value p₁) (Success.value p₂)
--   ... | refl = refl

--   module _ {M : Set → Set} (extract : ∀ {@0 bs} → M (Dec (Success A bs)) → Dec (Success A bs)) (parser : Parser (M ∘ Dec) A)
--     where

--     @0 completeParse : CompleteParse A M extract parser
--     completeParse{bs} v
--       with extract $ runParser parser bs
--     ... | (yes v') = uniqueParse v v'
--     ... | no ¬v    = contradiction v ¬v
