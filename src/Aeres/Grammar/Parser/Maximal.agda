{-# OPTIONS --subtyping #-}

import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser.Core
open import Aeres.Prelude
  renaming (Σ to Sigma)
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Grammar.Parser.Maximal
  (Σ : Set) where

open Aeres.Grammar.Definitions Σ
open Aeres.Grammar.Parser.Core Σ

module Generic (M : Set → Set) (Lift : (A : Set) (P : A → Set) → M A → Set) where
  GreatestSuccess : ∀ {A xs} → Success A xs → Set
  GreatestSuccess{A}{xs} s =
    ∀ pre' suf' → pre' ++ suf' ≡ xs → A pre'
    → length pre' ≤ Success.read s

  Maximal : ∀ {A} → Parser M A → Set
  Maximal{A} p = ∀ xs → Lift (Success A xs) GreatestSuccess (runParser p xs)

  record MaximalParser (@0 A : List Σ → Set) : Set where
    field
      parser : Parser M A
      max    : Maximal parser

module LogDec where
  Lift : (A : Set) (P : A → Set) → Logging (Dec A) → Set
  Lift A P (mkLogged _ (no  _)) = ⊤
  Lift A P (mkLogged _ (yes x)) = P x

  open Generic (Logging ∘ Dec) Lift public
  open ≡-Reasoning

  unlift : ∀ {@0 A} → (p : MaximalParser A)
           → ∀ xs {@0 pre} {suf} → pre ++ suf ≡ xs
           → A pre
           → Lift (Success A xs) GreatestSuccess (runParser (MaximalParser.parser p) xs)
           → Sigma (Success A xs) GreatestSuccess
  unlift p xs{pre}{suf} xs≡ a l
    with runParser (MaximalParser.parser p) xs
  ... | mkLogged log (no ¬p) = contradiction (success pre _ refl a suf xs≡) ¬p
  ... | mkLogged log (yes p₁) = p₁ , l

  mkMaximalParser
    : ∀ {@0 A}
      → (∀ xs → Sigma (Logging ∘ Dec $ Success A xs) (Lift (Success A xs) GreatestSuccess))
      → MaximalParser A
  runParser (MaximalParser.parser (mkMaximalParser {A} f)) xs =
    let (p , _) = f xs in p
  MaximalParser.max (mkMaximalParser {A} f) xs =
    let (_ , m) = f xs in m

  @0 nonnesting : ∀ {A} → NonNesting A → Parser (Logging ∘ Dec) A → MaximalParser A
  MaximalParser.parser (nonnesting nn p) = p
  MaximalParser.max (nonnesting{A} nn p) xs
    with runParser p xs
  ... | mkLogged log (no ¬p) = tt
  ... | (mkLogged log (yes p₁)) = help
    where
    help : (pre' suf' : List Σ) → pre' ++ suf' ≡ xs → A pre' → length pre' ≤ Success.read p₁
    help pre' suf' eq a =
      Lemmas.≡⇒≤
        (trans₀
          (‼ cong length
            (nn (trans eq (sym (Success.ps≡ p₁))) a (Success.value p₁)))
          (sym $ Success.read≡ p₁))

  parse&₁ : ∀ {@0 A B} → Parser (Logging ∘ Dec) A → NonNesting A → MaximalParser B → MaximalParser (&ₚ A B)
  parse&₁{A}{B} p₁ nn p₂ = mkMaximalParser help
    where
    help : ∀ xs
           → Sigma (Logging ∘ Dec $ Success (&ₚ A B) xs)
                   (Lift (Success (&ₚ A B) xs) GreatestSuccess)
    help xs =
      case runParser p₁ xs of λ where
        (mkLogged l₁ (no ¬p)) →
          mkLogged l₁ (no λ where
            (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} v₁ v₂ refl) suffix ps≡) →
              contradiction (success bs₁ _ refl v₁ (bs₂ ++ suffix) (trans (sym $ ++-assoc bs₁ bs₂ suffix) ps≡)) ¬p)
          , tt
        (mkLogged l₁ (yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁))) →
          case singleton (runParser (MaximalParser.parser{B} p₂) suf₁) refl of λ where
            (singleton (mkLogged l₂ (no ¬p)) p₂≡) →
              (mkLogged (l₁ ++ l₂) ∘ no $ λ where
                (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} v₁' v₂' refl) suffix ps≡') → ‼
                  let @0 xs≡ : bs₁ ++ bs₂ ++ suffix ≡ pre₁ ++ suf₁
                      xs≡ = begin bs₁ ++ bs₂ ++ suffix ≡⟨ (sym $ ++-assoc bs₁ _ _) ⟩
                                  (bs₁ ++ bs₂) ++ suffix ≡⟨ ps≡' ⟩
                                  xs ≡⟨ sym ps≡₁ ⟩
                                  pre₁ ++ suf₁ ∎
  
                      @0 bs₁≡ : bs₁ ≡ pre₁
                      bs₁≡ = nn xs≡ v₁' v₁
                  in
                  contradiction (success bs₂ _ refl v₂' suffix (Lemmas.++-cancel≡ˡ _ _ bs₁≡ xs≡)) ¬p)
              , tt  
            (singleton (mkLogged l₂ (yes (success pre₂ r₂ r₂≡ v₂ suf₂ ps≡₂))) p₂≡) →
              (mkLogged (l₁ ++ l₂) ∘ yes $
                success (pre₁ ++ pre₂) (r₁ + r₂)
                  (begin (r₁ + r₂ ≡⟨ cong₂ _+_ r₁≡ r₂≡ ⟩
                         length pre₁ + length pre₂ ≡⟨ (sym $ length-++ pre₁) ⟩
                         length (pre₁ ++ pre₂) ∎))
                  (mk&ₚ v₁ v₂ refl) suf₂
                  (begin (pre₁ ++ pre₂) ++ suf₂ ≡⟨ ++-assoc pre₁ _ _ ⟩
                         pre₁ ++ (pre₂ ++ suf₂) ≡⟨ cong (pre₁ ++_) ps≡₂ ⟩
                         pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
                         xs ∎))
              , λ where
                  pre' suf' xs≡ (mk&ₚ{bs₁}{bs₂} fstₚ₁ sndₚ₁ bs≡) →
                    uneraseDec
                      (≤-Reasoning.begin
                        length pre' ≤-Reasoning.≡⟨ cong length bs≡ ⟩
                        length (bs₁ ++ bs₂) ≤-Reasoning.≡⟨ length-++ bs₁ ⟩
                        length bs₁ + length bs₂
                          ≤-Reasoning.≡⟨
                            cong (λ x → length x + length bs₂)
                              (nn (begin (bs₁ ++ bs₂ ++ suf' ≡⟨ sym (++-assoc bs₁ _ _) ⟩
                                         (bs₁ ++ bs₂) ++ suf' ≡⟨ cong (_++ suf') (sym bs≡) ⟩
                                         pre' ++ suf' ≡⟨ xs≡ ⟩
                                         xs ≡⟨ sym ps≡₁ ⟩
                                         pre₁ ++ suf₁ ∎))
                                fstₚ₁ v₁)
                          ⟩
                        length pre₁ + length bs₂ ≤-Reasoning.≡⟨ cong (_+ length bs₂) (sym r₁≡) ⟩
                        r₁ + length bs₂
                          ≤-Reasoning.≤⟨
                            +-monoʳ-≤ r₁
                              (subst₀ (Lift (Success _ _) GreatestSuccess)
                                (sym p₂≡)
                                (MaximalParser.max p₂ suf₁)
                                bs₂ suf'
                                (Lemmas.++-cancel≡ˡ bs₁ pre₁
                                  ((nn (begin (bs₁ ++ bs₂ ++ suf' ≡⟨ sym (++-assoc bs₁ _ _) ⟩
                                         (bs₁ ++ bs₂) ++ suf' ≡⟨ cong (_++ suf') (sym bs≡) ⟩
                                         pre' ++ suf' ≡⟨ xs≡ ⟩
                                         xs ≡⟨ sym ps≡₁ ⟩
                                         pre₁ ++ suf₁ ∎))
                                fstₚ₁ v₁))
                                  (begin (bs₁ ++ bs₂ ++ suf' ≡⟨ (sym $ ++-assoc bs₁ _ _) ⟩
                                         (bs₁ ++ bs₂) ++ suf' ≡⟨ cong (_++ suf') (sym bs≡) ⟩
                                         pre' ++ suf' ≡⟨ xs≡ ⟩
                                         xs ≡⟨ sym ps≡₁ ⟩
                                         pre₁ ++ suf₁ ∎)))
                                sndₚ₁)
                          ⟩
                        r₁ + r₂ ≤-Reasoning.∎)
                      (_ ≤? _)
