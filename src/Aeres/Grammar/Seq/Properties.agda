{-# OPTIONS --subtyping #-}

import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option.TCB
import      Aeres.Grammar.Option.Properties
import      Aeres.Grammar.Seq.TCB
open import Aeres.Prelude renaming (Σ to Sigma)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Grammar.Seq.Properties (Σ : Set) where

open Aeres.Grammar.Definitions Σ
open Aeres.Grammar.Option.TCB  Σ
  hiding (module Option)
private
  module Option = Aeres.Grammar.Option.Properties Σ
open Aeres.Grammar.Seq.TCB     Σ

@0 nonempty₁ : ∀ {A} {B : ∀ {bs} → A bs → List Σ → Set} → NonEmpty A → NonEmpty (&ₚᵈ A B)
nonempty₁ ne (mk&ₚ fstₚ₁ sndₚ₁ bs≡) refl = ne fstₚ₁ (++-conicalˡ _ _ (sym bs≡))

@0 nosubstringsᵈ
  : {A : List Σ → Set} {B : {@0 bs₁ : List Σ} → A bs₁ → List Σ → Set}
    → NoSubstrings A → Unambiguous A → (∀ {@0 bs} (a : A bs) → NoSubstrings (B a))
    → NoSubstrings (&ₚᵈ A B)
nosubstringsᵈ{A}{B} nnA uA nnB {xs₁}{ys₁}{xs₂}{ys₂}xs₁++ys₁≡xs₂++ys₂ (mk&ₚ{bs₁₁}{bs₂₁} fstₚ₁ sndₚ₁ bs≡) (mk&ₚ{bs₁₂}{bs₂₂} fstₚ₂ sndₚ₂ bs≡₁) =
  begin xs₁          ≡⟨ bs≡ ⟩
        bs₁₁ ++ bs₂₁ ≡⟨ cong₂ _++_ bs₁≡ bs₂≡ ⟩
        bs₁₂ ++ bs₂₂ ≡⟨ sym bs≡₁ ⟩
        xs₂          ∎
  where
  open ≡-Reasoning

  @0 xs++ys≡' : bs₁₁ ++ bs₂₁ ++ ys₁ ≡ bs₁₂ ++ bs₂₂ ++ ys₂
  xs++ys≡' = begin bs₁₁ ++ bs₂₁ ++ ys₁   ≡⟨ solve (++-monoid Σ) ⟩
                   (bs₁₁ ++ bs₂₁) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
                   xs₁ ++ ys₁            ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
                   xs₂ ++ ys₂            ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
                   (bs₁₂ ++ bs₂₂) ++ ys₂ ≡⟨ solve (++-monoid Σ) ⟩
                   bs₁₂ ++ bs₂₂ ++ ys₂   ∎

  @0 bs₁≡ : bs₁₁ ≡ bs₁₂
  bs₁≡ = nnA xs++ys≡' fstₚ₁ fstₚ₂

  fstₚ≡ : fstₚ₁ ≡ subst A (sym bs₁≡) fstₚ₂
  fstₚ≡ = uA fstₚ₁ _

  B≡ : B fstₚ₁ bs₂₂ ≡ B fstₚ₂ bs₂₂
  B≡ = begin B fstₚ₁ bs₂₂ ≡⟨ cong (λ x → B x bs₂₂) fstₚ≡ ⟩
             B (subst A (sym bs₁≡) fstₚ₂) bs₂₂ ≡⟨ ≡-elim (λ {y} e → B (subst A e fstₚ₂) bs₂₂ ≡ B _ bs₂₂) refl (sym bs₁≡) ⟩
             B fstₚ₂ bs₂₂ ∎

  sndₚ₂' : B fstₚ₁ bs₂₂
  sndₚ₂' = subst {A = Set} id (sym B≡) sndₚ₂

  @0 bs₂≡ : bs₂₁ ≡ bs₂₂
  bs₂≡ = nnB fstₚ₁ (Lemmas.++-cancel≡ˡ _ _ bs₁≡ xs++ys≡') sndₚ₁ sndₚ₂'

@0 nosubstrings : ∀ {A B} → NoSubstrings A → NoSubstrings B → NoSubstrings (&ₚ A B)
nosubstrings nnA nnB {xs₁}{ys₁}{xs₂}{ys₂} xs++ys≡ (mk&ₚ{bs₁₁}{bs₂₁} a₁ b₁ bs≡) (mk&ₚ{bs₁₂}{bs₂₂} a₂ b₂ bs≡₁) =
  begin xs₁          ≡⟨ bs≡ ⟩
        bs₁₁ ++ bs₂₁ ≡⟨ cong (_++ bs₂₁) bs₁≡ ⟩
        bs₁₂ ++ bs₂₁ ≡⟨ cong (bs₁₂ ++_) bs₂≡ ⟩
        bs₁₂ ++ bs₂₂ ≡⟨ sym bs≡₁ ⟩
        xs₂          ∎
  where
  open ≡-Reasoning

  @0 xs++ys≡' : bs₁₁ ++ bs₂₁ ++ ys₁ ≡ bs₁₂ ++ bs₂₂ ++ ys₂
  xs++ys≡' = begin bs₁₁ ++ bs₂₁ ++ ys₁   ≡⟨ solve (++-monoid Σ) ⟩
                   (bs₁₁ ++ bs₂₁) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
                   xs₁ ++ ys₁            ≡⟨ xs++ys≡ ⟩
                   xs₂ ++ ys₂            ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
                   (bs₁₂ ++ bs₂₂) ++ ys₂ ≡⟨ solve (++-monoid Σ) ⟩
                   bs₁₂ ++ bs₂₂ ++ ys₂   ∎

  @0 bs₁≡ : bs₁₁ ≡ bs₁₂
  bs₁≡ = nnA xs++ys≡' a₁ a₂

  @0 bs₂≡ : bs₂₁ ≡ bs₂₂
  bs₂≡ = nnB (++-cancelˡ bs₁₁ (trans xs++ys≡' (cong (_++ bs₂₂ ++ ys₂) (sym bs₁≡)))) b₁ b₂

@0 nosubstringsOption₁ : ∀ {A B} → NoSubstrings A → NoSubstrings B → NoConfusion A B
                         → NoSubstrings (&ₚ (Option A) B)
nosubstringsOption₁ ns₁ ns₂ nc xs₁++ys₁≡xs₂++ys₂ (mk&ₚ none b₁ refl) (mk&ₚ none b₂ refl) =
  ns₂ xs₁++ys₁≡xs₂++ys₂ b₁ b₂
nosubstringsOption₁ ns₁ ns₂ nc {ys₁ = ys₁}{ys₂ = ys₂} xs₁++ys₁≡xs₂++ys₂ (mk&ₚ{bs₂ = bs₁₂} none b₁ refl) (mk&ₚ{bs₂₁}{bs₂₂} (some a₂) b₂ refl) =
  contradiction
    b₁
    (nc ++≡ a₂)
  where
  open ≡-Reasoning
  @0 ++≡ : bs₂₁ ++ bs₂₂ ++ ys₂ ≡ bs₁₂ ++ ys₁
  ++≡ = begin
    bs₂₁ ++ bs₂₂ ++ ys₂ ≡⟨ sym (++-assoc bs₂₁ _ _) ⟩
    (bs₂₁ ++ bs₂₂) ++ ys₂ ≡⟨ sym xs₁++ys₁≡xs₂++ys₂ ⟩
    bs₁₂ ++ ys₁ ∎
nosubstringsOption₁ ns₁ ns₂ nc {ys₁ = ys₁}{ys₂ = ys₂} xs₁++ys₁≡xs₂++ys₂ (mk&ₚ{bs₁₁}{bs₁₂} (some a₁) b₁ refl) (mk&ₚ{bs₂ = bs₂₂} none b₂ refl) =
  contradiction
    b₂
    (nc ++≡ a₁)
  where
  open ≡-Reasoning
  @0 ++≡ : bs₁₁ ++ bs₁₂ ++ ys₁ ≡ bs₂₂ ++ ys₂
  ++≡ = begin
    bs₁₁ ++ bs₁₂ ++ ys₁ ≡⟨ sym (++-assoc bs₁₁ _ _) ⟩
    (bs₁₁ ++ bs₁₂) ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
    bs₂₂ ++ ys₂ ∎
nosubstringsOption₁ ns₁ ns₂ nc xs₁++ys₁≡xs₂++ys₂ (mk&ₚ (some a₁) b₁ bs≡₁) (mk&ₚ (some a₂) b₂ bs≡₂) =
  nosubstrings ns₁ ns₂ xs₁++ys₁≡xs₂++ys₂ (mk&ₚ a₁ b₁ bs≡₁) (mk&ₚ a₂ b₂ bs≡₂)

@0 unambiguousᵈ
  : ∀ {A} {B : ∀ {bs} → A bs → List Σ → Set} → Unambiguous A → NoSubstrings A
    → (∀ {@0 bs} (a : A bs) → Unambiguous (B a))
    → Unambiguous (&ₚᵈ A B)
unambiguousᵈ{A}{B} ua nna ub (mk&ₚ{bs₁₁}{bs₂₁} fstₚ₁ sndₚ₁ bs≡) (mk&ₚ{bs₁₂}{bs₂₂} fstₚ₂ sndₚ₂ bs≡₁) =
  let @0 bs≡' : bs₁₁ ++ bs₂₁ ≡ bs₁₂ ++ bs₂₂
      bs≡' = trans (sym bs≡) bs≡₁
  in
  case nna bs≡' fstₚ₁ fstₚ₂ of λ where
    refl →
      case ‼ ua fstₚ₁ fstₚ₂ ret (const _) of λ where
        refl →
          case ‼ ++-cancelˡ bs₁₁ bs≡' ret (const _) of λ where
            refl →
              case ‼ ub fstₚ₁ sndₚ₁ sndₚ₂ ret (const _) of λ where
                refl →
                  case ‼ ≡-unique bs≡ bs≡₁ ret (const _) of λ where
                    refl → refl

@0 nonmalleableᵈ
  : ∀ {A} {B : ∀ {bs} → A bs → List Σ → Set} {ra : Raw A} {rb : Raw₁ ra B}
    → NonMalleable ra → NonMalleable₁ rb → NonMalleable (Raw&ₚᵈ ra rb)
nonmalleableᵈ nm₁ nm₂ (mk&ₚ fstₚ₁ sndₚ₁ refl) (mk&ₚ fstₚ₂ sndₚ₂ refl) eq =
  case Inverse.f⁻¹ Product.Σ-≡,≡↔≡ eq ret (const _) of λ where
    (fst≡ , snd≡) → case (nm₁ fstₚ₁ fstₚ₂ fst≡ ,′ singleton fst≡ refl) ret (const _) of λ where
      (refl , singleton refl refl) → case nm₂ sndₚ₁ sndₚ₂ snd≡ ret (const _) of λ where
        refl → refl
  where
  import Data.Product.Properties as Product

@0 nonmalleable
  : ∀ {A B} {ra : Raw A} {rb : Raw B}
    → NonMalleable ra → NonMalleable rb → NonMalleable (Raw&ₚ ra rb)
nonmalleable nm₁ nm₂ (mk&ₚ fstₚ₁ sndₚ₁ refl) (mk&ₚ fstₚ₂ sndₚ₂ refl) eq =
  case Inverse.f⁻¹ Product.Σ-≡,≡↔≡ eq ret (const _) of λ where
    (fst≡ , snd≡) → case (nm₁ fstₚ₁ fstₚ₂ fst≡ ,′ singleton fst≡ refl) ret (const _) of λ where
      (refl , singleton refl refl) → case nm₂ sndₚ₁ sndₚ₂ snd≡ ret (const _) of λ where
        refl → refl
  where
  import Data.Product.Properties as Product


@0 unambiguous : ∀ {A B} → Unambiguous A → NoSubstrings A → Unambiguous B → Unambiguous (&ₚ A B)
unambiguous ua ns ub = unambiguousᵈ ua ns (λ _ → ub)

@0 unambiguousOption₁
  : ∀ {A B} → Unambiguous A → NoSubstrings A → Unambiguous B → NoConfusion A B
    → Unambiguous (&ₚ (Option A) B)
unambiguousOption₁ ua₁ ns₁ ua₂ nc (mk&ₚ none b₁ refl) (mk&ₚ none b₂ refl) =
  case ua₂ b₁ b₂ ret (const _) of λ where
    refl → refl
unambiguousOption₁ ua₁ ns₁ ua₂ nc (mk&ₚ{bs₂ = bs₁₂} none b₁ refl) (mk&ₚ{bs₂₁}{bs₂₂} (some a₂) b₂ bs≡₂) =
  contradiction
    b₁
    (nc ++≡ a₂)
  where
  open ≡-Reasoning
  @0 ++≡ : bs₂₁ ++ bs₂₂ ≡ bs₁₂ ++ []
  ++≡ = begin
    bs₂₁ ++ bs₂₂ ≡⟨ sym bs≡₂ ⟩
    bs₁₂ ≡⟨ sym (++-identityʳ bs₁₂) ⟩
    bs₁₂ ++ [] ∎
unambiguousOption₁ ua₁ ns₁ ua₂ nc (mk&ₚ{bs₁₁}{bs₁₂} (some a₁) b₁ bs≡₁) (mk&ₚ{bs₂ = bs₂₂} none b₂ refl) =
  contradiction
    b₂
    (nc ++≡ a₁)
  where
  open ≡-Reasoning
  @0 ++≡ : bs₁₁ ++ bs₁₂ ≡ bs₂₂ ++ []
  ++≡ = begin
    bs₁₁ ++ bs₁₂ ≡⟨ sym bs≡₁ ⟩
    bs₂₂ ≡⟨ sym (++-identityʳ bs₂₂) ⟩
    bs₂₂ ++ [] ∎
unambiguousOption₁ ua₁ ns₁ ua₂ nc (mk&ₚ (some a₁) b₁ bs≡₁) (mk&ₚ (some a₂) b₂ bs≡₂) =
  case ‼ unambiguous ua₁ ns₁ ua₂ (mk&ₚ a₁ b₁ bs≡₁) (mk&ₚ a₂ b₂ bs≡₂) ret (const _) of λ where
    refl → refl

private
  -- TODO
  @0 noprogress : ∀ {A B bs₁ bs₂} → bs₁ ≡ bs₂
                  → NoSubstrings A → NonEmpty B → NoConfusion A B
                  → Option A bs₂ → ¬ (&ₚ (Option A) B) bs₂
  noprogress refl ns₁ ne₂ nc none (mk&ₚ oa₂ b₂ bs≡₂) =
    contradiction (++-conicalʳ _ _ (sym bs≡₂)) (ne₂ b₂)
  noprogress {bs₁ = bs₁} refl ns₁ ne₂ nc (some a₁) (mk&ₚ none b₂ refl) =
    contradiction
      b₂
      (nc (bs₁ ++ [] ≡ bs₁ ++ [] ∋ refl) a₁)
    where
    open ≡-Reasoning
  noprogress refl ns₁ ne₂ nc (some a₁) (mk&ₚ{bs₂₁}{bs₂₂} (some a₂) b₂ refl) =
    contradiction
      (++-identityʳ-unique _ bs₂₁≡)
      (ne₂ b₂)
    where
    open ≡-Reasoning
    @0 bs₂₁≡ : bs₂₁ ≡ bs₂₁ ++ bs₂₂
    bs₂₁≡ = ns₁{ys₁ = bs₂₂}{ys₂ = []} (sym (++-identityʳ (bs₂₁ ++ bs₂₂))) a₂ a₁

  @0 nooverlap₂
    : ∀ {A B C} → NonEmpty A → NoConfusion A B → NoConfusion A C
      → ∀ {bs₁ bs₂} → A bs₁ → ¬ &ₚ (Option B) (Option C) (bs₁ ++ bs₂)
  nooverlap₂ ne₁ nc₁₂ nc₁₃ {bs₁}{bs₂} a (mk&ₚ{bs₂₁}{bs₂₂} (some b) oc bs≡) =
    contradiction b (nc₁₂ bs≡ a)
  nooverlap₂ ne₁ nc₁₂ nc₁₃ {bs₁}{bs₂} a (mk&ₚ{bs₂₁}{bs₂₂} none (some c) bs≡) =
    contradiction c (nc₁₃ (trans bs≡ (sym (++-identityʳ _))) a)
  nooverlap₂ ne₁ nc₁₂ nc₁₃ {bs₁}{bs₂} a (mk&ₚ{bs₂₁}{bs₂₂} none none bs≡) =
    contradiction (++-conicalˡ _ _ bs≡) (ne₁ a)

@0 unambiguousOption₂
  : ∀ {A B} → Unambiguous A → NoSubstrings A → NonEmpty A
    → Unambiguous B → NonEmpty B
    → NoConfusion A B
    → Unambiguous (&ₚ (Option A) (Option B))
unambiguousOption₂{A}{B} ua₁ ns₁ ne₁ ua₂ ne₂ nc (mk&ₚ{bs₁₁} oa₁ none refl) (mk&ₚ{bs₂₁} oa₂ none bs≡₂) =
  case ‼ bs₁₁≡bs₂₁ ret (const _) of λ where
    refl → case ‼ ≡-unique refl bs≡₂ ret (const _) of λ where
      refl → case ‼ Option.unambiguous ua₁ ne₁ oa₁ oa₂ ret (const _) of λ where
        refl → refl{A = &ₚ (Option A) (Option B) (bs₁₁ ++ [])}
  where
  @0 bs₁₁≡bs₂₁ : bs₁₁ ≡ bs₂₁
  bs₁₁≡bs₂₁ = trans (sym (++-identityʳ _)) (trans bs≡₂ (++-identityʳ _))
unambiguousOption₂ ua₁ ns₁ ne₁ ua₂ ne₂ nc (mk&ₚ oa₁ none refl) (mk&ₚ oa₂ (some b₂) bs≡₂) =
  contradiction
    (mk&ₚ oa₂ b₂ (trans (sym (++-identityʳ _)) bs≡₂))
    (noprogress (sym (trans (sym (++-identityʳ _)) bs≡₂)) ns₁ ne₂ nc oa₁)
unambiguousOption₂ ua₁ ns₁ ne₁ ua₂ ne₂ nc (mk&ₚ oa₁ (some b₁) bs≡₁) (mk&ₚ oa₂ none refl) =
  contradiction
    (mk&ₚ oa₁ b₁ (trans (sym (++-identityʳ _)) bs≡₁))
    (noprogress (trans (sym bs≡₁) (++-identityʳ _)) ns₁ ne₂ nc oa₂)
unambiguousOption₂{A}{B} ua₁ ns₁ ne₁ ua₂ ne₂ nc (mk&ₚ oa₁ (some b₁) bs≡₁) (mk&ₚ oa₂ (some b₂) bs≡₂) =
  case ‼ unambiguousOption₁{A}{B} ua₁ ns₁ ua₂ nc (mk&ₚ oa₁ b₁ bs≡₁) (mk&ₚ oa₂ b₂ bs≡₂)
  ret (const _) of λ where
    refl → refl

@0 unambiguous₂Option₃
  : ∀ {A B C} → Unambiguous A → NoSubstrings A → NonEmpty A
    → Unambiguous B → NoSubstrings B → NonEmpty B
    → Unambiguous C → NonEmpty C
    → NoConfusion A B → NoConfusion A C → NoConfusion B C
    → Unambiguous (&ₚ (Option A) (&ₚ (Option B) (Option C)))
unambiguous₂Option₃{A}{B}{C} ua₁ ns₁ ne₁ ua₂ ns₂ ne₂ ua₃ ne₃ nc₁₂ nc₁₃ nc₂₃ = help
  where
  open ≡-Reasoning

  help : Unambiguous (&ₚ (Option A) (&ₚ (Option B) (Option C)))
  help (mk&ₚ{bs₁₁}{bs₁₂'} none a₁'@(mk&ₚ{bs₁₂}{bs₁₃} ob₁ oc₁ bs≡₁') refl) (mk&ₚ{bs₂₁}{bs₂₂'} none a₂'@(mk&ₚ{bs₂₂}{bs₂₃} ob₂ oc₂ bs≡₂') refl) =
    case ‼ unambiguousOption₂ ua₂ ns₂ ne₂ ua₃ ne₃ nc₂₃ a₁' a₂' ret (const _) of λ where
      refl → refl
  help (mk&ₚ{bs₁₁} none bc₁@(mk&ₚ{bs₁₂}{bs₁₃} ob₁ oc₁ refl) refl) (mk&ₚ{bs₂₁}{bs₂₂'} (some a₂) (mk&ₚ{bs₂₂}{bs₂₃} ob₂ oc₂ refl) bs≡₂) =
    contradiction
      (subst₀ (&ₚ (Option B) (Option C)) bs≡₂ bc₁)
      (nooverlap₂{A}{B}{C} ne₁ nc₁₂ nc₁₃ {bs₂ = bs₂₂'} a₂)
  help (mk&ₚ{bs₁₁}{bs₁₂'} (some a₁) (mk&ₚ{bs₁₂}{bs₁₃} ob₁ oc₁ refl) bs≡₁) (mk&ₚ{bs₂₁} none bc₂@(mk&ₚ{bs₂₂}{bs₂₃} ob₂ oc₂ refl) refl) =
    contradiction (subst₀ (&ₚ (Option B) (Option C)) bs≡₁ bc₂) (nooverlap₂{A}{B}{C} ne₁ nc₁₂ nc₁₃ {bs₂ = bs₁₂'} a₁)
  help (mk&ₚ{bs₁₁}{bs₁₂'} (some a₁) bc₁@(mk&ₚ{bs₁₂}{bs₁₃} ob₁ oc₁ bs≡₁') bs≡₁) (mk&ₚ{bs₂₁}{bs₂₂'} (some a₂) bc₂@(mk&ₚ{bs₂₂}{bs₂₃} ob₂ oc₂ bs≡₂') bs≡₂) =
    case ns₁ ++≡ a₁ a₂ ret (const _) of λ where
      refl → case ‼ ua₁ a₁ a₂ ret (const _) of λ where
        refl → case (bs₁₂' ≡ bs₂₂' ∋ ‼ ++-cancelˡ bs₁₁ ++≡') ret (const _) of λ where
          refl → case ‼ unambiguousOption₂ ua₂ ns₂ ne₂ ua₃ ne₃ nc₂₃ bc₁ bc₂ ret (const _) of λ where
            refl → case ‼ ≡-unique bs≡₁ bs≡₂ ret (const _) of λ where
              refl → refl
    where
    ++≡' : bs₁₁ ++ bs₁₂' ≡ bs₂₁ ++ bs₂₂'
    ++≡' = trans (sym bs≡₁) bs≡₂

    ++≡ : bs₁₁ ++ bs₁₂ ++ bs₁₃ ≡ bs₂₁ ++ bs₂₂ ++ bs₂₃
    ++≡ = begin bs₁₁ ++ bs₁₂ ++ bs₁₃ ≡⟨ cong (bs₁₁ ++_) (sym bs≡₁') ⟩
                bs₁₁ ++ bs₁₂' ≡⟨ ++≡' ⟩
                bs₂₁ ++ bs₂₂' ≡⟨ cong (bs₂₁ ++_) bs≡₂' ⟩
                bs₂₁ ++ bs₂₂ ++ bs₂₃ ∎
eq&ₚᵈ : ∀ {@0 A : @0 List Σ → Set} {@0 B : {@0 bs₁ : List Σ} → A bs₁ → @0 List Σ → Set}
        → Eq (Exists─ (List Σ) A)
        → (∀ {@0 bs₁} → (a : A bs₁) → Eq (Exists─ (List Σ) (B a)))
        → Eq (Exists─ (List Σ) (&ₚᵈ A B))
Eq._≟_ (eq&ₚᵈ eq₁ eq₂) (─ bs₁ , (mk&ₚ{bs₁₁}{bs₁₂} a₁ b₁ refl)) (─ bs₂ , mk&ₚ{bs₂₁}{bs₂₂} a₂ b₂ refl) =
  case Eq._≟_ eq₁ (─ bs₁₁ , a₁) (─ bs₂₁ , a₂) ret (const _) of λ where
    (no ¬p) → no λ where refl → contradiction refl ¬p
    (yes refl) →
      case Eq._≟_ (eq₂ a₁) (─ bs₁₂ , b₁) (─ bs₂₂ , b₂) ret (const _) of λ where
        (no ¬p) → no λ where refl → contradiction refl ¬p
        (yes refl) → yes refl

eq&ₚ : ∀ {@0 A B} → Eq (Exists─ (List Σ) A) → Eq (Exists─ (List Σ) B) → Eq (Exists─ (List Σ) (&ₚ A B))
Eq._≟_ (eq&ₚ eq₁ eq₂) (─ bs₁ , (mk&ₚ{bs₁₁}{bs₁₂} a₁ b₁ refl)) (─ bs₂ , mk&ₚ{bs₂₁}{bs₂₂} a₂ b₂ refl) =
  case Eq._≟_ eq₁ (─ bs₁₁ , a₁) (─ bs₂₁ , a₂) ret (const _) of λ where
    (no ¬p) → no λ where
      refl → contradiction refl ¬p
    (yes refl) → case Eq._≟_ eq₂ (─ bs₁₂ , b₁) (─ bs₂₂ , b₂) ret (const _) of λ where
      (no ¬p) → no λ where refl → contradiction refl ¬p
      (yes refl) → yes refl

eq≋&ₚ : ∀ {@0 A B} → Eq≋ A → Eq≋ B → Eq≋ (&ₚ A B)
eq≋&ₚ eq₁ eq₂ = Eq⇒Eq≋ (eq&ₚ (Eq≋⇒Eq eq₁) (Eq≋⇒Eq eq₂))

eq≋&ₚᵈ : ∀ {@0 A : @0 List Σ → Set} {@0 B : {@0 bs₁ : List Σ} → A bs₁ → @0 List Σ → Set}
         → Eq≋ A 
         → (∀ {@0 bs₁} → (a : A bs₁) → Eq≋ (B a))
         → Eq≋ (&ₚᵈ A B)
eq≋&ₚᵈ eq₁ eq₂ = Eq⇒Eq≋ (eq&ₚᵈ (Eq≋⇒Eq eq₁) (λ a → Eq≋⇒Eq (eq₂ a)))
