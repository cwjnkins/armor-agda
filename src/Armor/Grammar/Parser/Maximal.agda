import      Armor.Grammar.Definitions
import      Armor.Grammar.Parser.Core
open import Armor.Prelude
  renaming (Σ to Sigma)
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Grammar.Parser.Maximal
  (Σ : Set) where

open Armor.Grammar.Definitions          Σ
open Armor.Grammar.Parser.Core          Σ
  hiding (parseErased)

GreatestSuccess : ∀ {A xs} → Success A xs → Set
GreatestSuccess{A}{xs} s =
  ∀ pre' suf' → pre' ++ suf' ≡ xs → A pre'
  → length pre' ≤ Success.read s

module Generic (M : List Σ → Set → Set) (Lift : (A : Set) (P : A → Set) → (xs : List Σ) → M xs A → Set) where

  Maximal : ∀ {A} → Parserᵢ M A → Set
  Maximal{A} p = ∀ xs → Lift (Success A xs) GreatestSuccess xs (runParser p xs)

  record MaximalParser (A : @0 List Σ → Set) : Set where
    field
      parser : Parserᵢ M A
      max    : Maximal parser

  runMaximalParser : ∀ {A : @0 List Σ → Set} → (p : MaximalParser A) → ∀ xs → Sigma (M xs (Success A xs)) (Lift (Success A xs) GreatestSuccess xs)
  proj₁ (runMaximalParser p xs) = runParser (MaximalParser.parser p) xs
  proj₂ (runMaximalParser p xs) = MaximalParser.max p xs

module GenericSimple
  (M : Set → Set) (Lift : (A : Set) (P : A → Set) → M A → Set) where

  open Generic (const M) (λ A P _ → Lift A P) public

module LogDec where
  Lift : (A : Set) (P : A → Set) → Logging (Dec A) → Set
  Lift A P (mkLogged _ (no  _)) = ⊤
  Lift A P (mkLogged _ (yes x)) = P x

  open GenericSimple (Logging ∘ Dec) Lift public
  open ≡-Reasoning

  unlift : ∀ {A : @0 List Σ → Set} → (p : MaximalParser A)
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

  equivalent : ∀ {A B : @0 List Σ → Set} → Equivalent A B → MaximalParser A → MaximalParser B
  equivalent{A}{B} eq@(eq₁ , eq₂) p = mkMaximalParser help
    where
    help : ∀ xs → Sigma (Logging ∘ Dec $ Success B xs) (Lift (Success B xs) GreatestSuccess)
    help xs =
      case (_,e_{B = Lift (Success A xs) GreatestSuccess}
              (runParser (MaximalParser.parser p) xs)
              (MaximalParser.max p xs))
      ret (const _) of λ where
        (mkLogged l₁ (no ¬p) , _) →
          (mkLogged l₁ (no (contraposition (mapSuccess eq₂) ¬p))) ,e tt
        (mkLogged l₁ (yes s@(success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁)) , m) →
          (mkLogged l₁ (yes (mapSuccess eq₁ s))) ,e λ where
            pre' suf' xs≡ b → m pre' suf' xs≡ (eq₂ b)

  nonnesting : ∀ {A : @0 List Σ → Set} → @0 NoSubstrings A → Parser (Logging ∘ Dec) A → MaximalParser A
  MaximalParser.parser (nonnesting nn p) = p
  MaximalParser.max (nonnesting{A} nn p) xs =
    case runParser p xs ret (Lift _ _) of λ where
      (mkLogged log (no ¬p)) → tt
      (mkLogged log (yes p₁)) → help p₁
    where
    module _ (p₁ : Success A xs) where
      help : (pre' suf' : List Σ) → pre' ++ suf' ≡ xs → A pre' → length pre' ≤ Success.read p₁
      help pre' suf' eq a =
        Lemmas.≡⇒≤
          (trans₀
            (‼ cong length
              (nn (trans eq (sym (Success.ps≡ p₁))) a (Success.value p₁)))
            (sym $ Success.read≡ p₁))


  parseErased : ∀ {A : @0 List Σ → Set} → MaximalParser A → MaximalParser (λ x → Erased (A x))
  parseErased{A} p = mkMaximalParser help
    where
    help : ∀ xs → Sigma (Logging ∘ Dec $ Success (λ x → Erased (A x)) xs) (Lift _ GreatestSuccess)
    help xs =
      case
        _,e_{B = Lift (Success A xs) GreatestSuccess}
        (runParser (MaximalParser.parser p) xs)
        (MaximalParser.max p xs)
      ret (const _) of λ where
        (mkLogged log (no ¬p) , _) →
          (mkLogged log (no λ where
            (success prefix read read≡ (─ value) suffix ps≡) →
              contradiction (success prefix _ read≡ value suffix ps≡) ¬p))
          ,e tt
        (mkLogged log (yes p@(success prefix read read≡ value suffix ps≡)) , m) →
          mkLogged log (yes (success prefix _ read≡ (─ value) suffix ps≡))
          ,e λ where
               pre' suf' xs≡ (─ v) →
                 uneraseDec (m pre' suf' xs≡ v) (_ ≤? _)
