{-# OPTIONS --subtyping #-}

open import Aeres.Binary
  renaming (module Base64 to B64)
open import Aeres.Data.Base64
open import Aeres.Data.PEM.CertText.Exclusions
open import Aeres.Data.PEM.CertText.FinalLine
open import Aeres.Data.PEM.CertText.FullLine
open import Aeres.Data.PEM.CertText.TCB
open import Aeres.Data.PEM.RFC5234
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Relation.Definitions
open import Aeres.Prelude
import      Data.List.Relation.Unary.Any.Properties as Any
import      Data.Nat.Properties as Nat
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.PEM.CertText.Properties where

open Aeres.Grammar.Definitions          Char
open Aeres.Grammar.IList                Char
open Aeres.Grammar.Relation.Definitions Char

open ≡-Reasoning

finalLineFromLines : ∀ {@0 bs} → IList CertFullLine bs → Erased (bs ≡ []) ⊎ &ₚ (IList CertFullLine) (CertFinalLine ×ₚ CertFullLine) bs
finalLineFromLines nil = inj₁ (─ refl)
finalLineFromLines (consIList{bs₁}{.[]} head₁ nil bs≡) =
  inj₂ (mk&ₚ nil (mk×ₚ (FinalLine.fromCertFullLine head₁) head₁ refl)
          (begin (_ ≡⟨ bs≡ ⟩
                 bs₁ ++ [] ≡⟨ ++-identityʳ bs₁ ⟩
                 bs₁ ∎)))
finalLineFromLines{bs} (consIList{bs₁}{bs₂} head₁ tail₁@(consIList{bs₁ = bs₃} head₂ tail₂ bs≡₂) bs≡₁) =
  case finalLineFromLines tail₁ ret (const _) of λ where
    (inj₁ (─ refl)) →
      contradiction{P = bs₃ ≡ []} (++-conicalˡ bs₃ _ (sym bs≡₂)) (FullLine.nonempty head₂)
    (inj₂ (mk&ₚ{bs₅}{bs₆} fstₚ₁ sndₚ₁ refl)) →
      inj₂ (mk&ₚ (consIList head₁ fstₚ₁ refl) sndₚ₁
                    (begin _ ≡⟨ bs≡₁ ⟩
                           bs₁ ++ bs₅ ++ bs₆ ≡⟨ sym (++-assoc bs₁ bs₅ _) ⟩
                           (bs₁ ++ bs₅) ++ bs₆ ∎))

fullLineFromLine
  : ∀ {@0 xs₁ ys₁ xs₂ ys₂}
    → CertFinalLine xs₁ → CertFullLine xs₂
    → xs₁ ++ ys₁ ≡ xs₂ ++ ys₂
    → CertFullLine xs₁
fullLineFromLine{xs₁}{ys₁}{xs₂}{ys₂} (mkCertFinalLine{l}{e} line lineLen eol bs≡) (mkCertFullLine{l₁}{e₁} line₁ eol₁ bs≡₁) ++≡ =
  mkCertFullLine (subst₀ (ExactLength (IList Base64Char) 64) (sym l≡) line₁) eol bs≡
  where
  @0 l≡ : l ≡ l₁
  l≡ = noOverlapBoundary₂ RFC5234.EOL.noOverlap RFC5234.EOL.noOverlap
         (l ++ e ++ ys₁ ≡⟨ sym (++-assoc l _ _) ⟩
         (l ++ e) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
         xs₁ ++ ys₁ ≡⟨ ++≡ ⟩
         xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
         (l₁ ++ e₁) ++ ys₂ ≡⟨ ++-assoc l₁ _ _ ⟩
         l₁ ++ e₁ ++ ys₂ ∎)
         line eol (Base64.Str.fromExactLength line₁) eol₁

@0 char∈ : ∀ {@0 b bs} → b ∈ bs → CertText bs → b ∈ B64.charset ++ String.toList "=\r\n"
char∈ b∈ (mkCertText{b₁}{f₁} body₁ final₁ refl) =
  caseErased Any.++⁻ b₁ b∈ ret (const _) of λ where
    (inj₁ x) → ─ FullLine.char∈List x body₁
    (inj₂ y) → ─ FinalLine.char∈ y final₁

@0 foldFinalIntoBodyWF
  : ∀ {@0 b₁ f₁ b₂ f₂ suf₁ suf₂}
    → IList CertFullLine b₁ → CertFinalLine f₁
    → (body₂ : IList CertFullLine b₂) → CertFinalLine f₂
    → Acc _<_ (lengthIList body₂)
    → b₁ ++ f₁ ++ suf₁ ≡ b₂ ++ f₂ ++ suf₂
    → length b₁ < length b₂
    → Σ[ n ∈ ℕ ] b₂ ≡ b₁ ++ f₁ ++ take n suf₁
foldFinalIntoBodyWF{f₁ = f₁}{f₂ = f₂}{suf₁}{suf₂} nil fin₁ (consIList{l₂}{b₂} fu₁ body₂ refl) fin₂ ac ++≡ b₁< =
    Lemmas.⊆⇒++take
      ++≡
      (caseErased singleton body₂ refl ret (const _) of λ where
        (singleton nil refl) → ─
          (≤.begin
            length f₁ ≤.≤⟨ Nat.m≤m+n (length f₁) _ ⟩
            length f₁ + length (drop (length f₁) l₂) ≤.≡⟨ sym (length-++ f₁) ⟩
            length (f₁ ++ drop (length f₁) l₂)
              ≤.≡⟨ cong length (f₁ ++ drop (length f₁) l₂ ≡ l₂ ∋ sym
                (noOverlapBoundary₁
                  FinalLine.noOverlap
                  (l₂ ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
                  (l₂ ++ []) ++ f₂ ++ suf₂ ≡⟨ sym ++≡ ⟩
                  f₁ ++ suf₁ ∎)
                  (FinalLine.fromCertFullLine fu₁) fin₂ fin₁))
              ⟩
            length l₂ ≤.≡⟨ cong length (sym (++-identityʳ l₂)) ⟩
            length (l₂ ++ []) ≤.∎)
        (singleton (consIList{l₂'}{b₂'} fu₂ body₂' refl) refl) → ─
          (≤.begin
            (length f₁ ≤.≤⟨ proj₂ (FinalLine.lengthRange fin₁) ⟩
            66 ≤.≤⟨ Nat.+-mono-≤ (proj₁ $ FullLine.fullLineLen fu₁) (Nat.≤-trans (s≤s z≤n) (proj₁ $ FullLine.fullLineLen fu₂)) ⟩
            length l₂ + length l₂' ≤.≡⟨ sym (length-++ l₂) ⟩
            length (l₂ ++ l₂') ≤.≤⟨ Nat.m≤m+n _ _ ⟩
            length (l₂ ++ l₂') + length b₂' ≤.≡⟨ sym (length-++ (l₂ ++ l₂')) ⟩
            length ((l₂ ++ l₂') ++ b₂') ≤.≡⟨ cong length (++-assoc l₂ l₂' _) ⟩
            length (l₂ ++ l₂' ++ b₂') ≤.∎)))
  where
  module ≤ = Nat.≤-Reasoning
  
foldFinalIntoBodyWF{f₁ = f₁}{f₂ = f₂}{suf₁}{suf₂} (consIList{u₁}{b₁} fu₁ nil refl) fin₁ (consIList{u₂}{b₂} fu₂ nil refl) fin₂ ac ++≡ b₁< =
  contradiction
    (cong length (u₁ ≡ u₂ ∋
      noOverlapBoundary₂ noOverlapLines noOverlapLines ++≡' fu₁ fin₁ fu₂ fin₂))
    (Nat.<⇒≢
      (≤.begin
        suc (length u₁) ≤.≡⟨ cong (suc ∘ length) (sym (++-identityʳ u₁)) ⟩
        suc (length (u₁ ++ [])) ≤.≤⟨ b₁< ⟩
        length (u₂ ++ []) ≤.≡⟨ cong length (++-identityʳ u₂) ⟩
        length u₂ ≤.∎))
  where
  module ≤ = Nat.≤-Reasoning

  @0 ++≡' : u₁ ++ f₁ ++ suf₁ ≡ u₂ ++ f₂ ++ suf₂
  ++≡' =
    u₁ ++ f₁ ++ suf₁ ≡⟨ solve (++-monoid Char) ⟩
    (u₁ ++ []) ++ f₁ ++ suf₁ ≡⟨ ++≡ ⟩
    (u₂ ++ []) ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
    u₂ ++ f₂ ++ suf₂ ∎
foldFinalIntoBodyWF{f₁ = f₁}{f₂ = f₂}{suf₁}{suf₂} (consIList{u₁}{b₁} fu₁ nil refl) fin₁ (consIList{u₂}{b₂} fu₂ (consIList{u₂'}{b₂'} fu₂' body₂ refl) refl) fin₂ (WellFounded.acc rs) ++≡ b₁< =
  (proj₁ ih) ,
    (u₂ ++ u₂' ++ b₂' ≡⟨ cong (u₂ ++_) (proj₂ ih) ⟩
    u₂ ++ f₁ ++ take (proj₁ ih) suf₁ ≡⟨ cong (_++ f₁ ++ take (proj₁ ih) suf₁) (sym u₁≡) ⟩
    u₁ ++ f₁ ++ take (proj₁ ih) suf₁ ≡⟨ solve (++-monoid Char) ⟩
    (u₁ ++ []) ++ f₁ ++ take (proj₁ ih) suf₁ ∎)
  where
  module ≤ = Nat.≤-Reasoning

  @0 ++≡' : u₁ ++ b₁ ++ f₁ ++ suf₁ ≡ u₂ ++ u₂' ++ b₂' ++ f₂ ++ suf₂
  ++≡' = u₁ ++ b₁ ++ f₁ ++ suf₁ ≡⟨ solve (++-monoid Char) ⟩
         (u₁ ++ []) ++ f₁ ++ suf₁ ≡⟨ ++≡ ⟩
         (u₂ ++ u₂' ++ b₂') ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
         u₂ ++ u₂' ++ b₂' ++ f₂ ++ suf₂ ∎

  @0 u₁≡ : u₁ ≡ u₂
  u₁≡ = noOverlapBoundary₂ noOverlapLines FullLine.nooverlap ++≡' fu₁ fin₁ fu₂ fu₂'

  @0 ++≡ᵤ : f₁ ++ suf₁ ≡ u₂' ++ b₂' ++ f₂ ++ suf₂
  ++≡ᵤ = Lemmas.++-cancel≡ˡ _ _ u₁≡ ++≡'

  b₁<' : length u₁ + 0 < length u₁ + length (u₂' ++ b₂')
  b₁<' = ≤.begin
    (suc (length u₁ + 0) ≤.≡⟨ cong suc (sym (length-++ u₁)) ⟩
    suc (length (u₁ ++ [])) ≤.≤⟨ b₁< ⟩
    length (u₂ ++ u₂' ++ b₂') ≤.≡⟨ length-++ u₂ ⟩
    length u₂ + length (u₂' ++ b₂') ≤.≡⟨ cong (_+ length (u₂' ++ b₂')) (cong length (sym u₁≡)) ⟩
    length u₁ + length (u₂' ++ b₂') ≤.∎)

  ih = foldFinalIntoBodyWF nil fin₁ (consIList fu₂' body₂ refl) fin₂ (rs _ Nat.≤-refl)
         (f₁ ++ suf₁ ≡⟨ ++≡ᵤ ⟩
         u₂' ++ b₂' ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
         (u₂' ++ b₂') ++ f₂ ++ suf₂ ∎)
         (Nat.+-cancelˡ-< (length u₁) b₁<')

foldFinalIntoBodyWF{f₁ = f₁}{f₂ = f₂}{suf₁}{suf₂} (consIList{u₁}{b₁} fu₁ (consIList{u₁'}{b₁'} fu₁' body₁ refl) refl) fin₁ (consIList{u₂}{b₂} fu₂ nil refl) fin₂ ac ++≡ b₁< =
  contradiction{P = length (u₁' ++ b₁') < 0}
    (Nat.+-cancelˡ-< (length u₁) (≤.begin
      (1 + length u₁ + length (u₁' ++ b₁') ≤.≡⟨ cong suc (sym (length-++ u₁)) ⟩
      1 + length (u₁ ++ u₁' ++ b₁') ≤.≤⟨ b₁< ⟩
      length (u₂ ++ []) ≤.≡⟨ length-++ u₂ ⟩
      length u₂ + 0 ≤.≡⟨ cong (λ x → length x + 0) (sym u₁≡) ⟩
      length u₁ + 0 ≤.∎)))
    λ ()
  where
  module ≤ = Nat.≤-Reasoning

  b₁<' : length u₁ + length (u₁' ++ b₁') < length u₂ + 0
  b₁<' = ≤.begin
    (1 + length u₁ + length (u₁' ++ b₁') ≤.≡⟨ cong suc (sym (length-++ u₁)) ⟩
    1 + length (u₁ ++ u₁' ++ b₁') ≤.≤⟨ b₁< ⟩
    length (u₂ ++ []) ≤.≡⟨ length-++ u₂ ⟩
    length u₂ + 0 ≤.∎)

  ++≡' : u₁ ++ u₁' ++ b₁' ++ f₁ ++ suf₁ ≡ u₂ ++ f₂ ++ suf₂
  ++≡' = u₁ ++ u₁' ++ b₁' ++ f₁ ++ suf₁ ≡⟨ solve (++-monoid Char) ⟩
         (u₁ ++ u₁' ++ b₁') ++ f₁ ++ suf₁ ≡⟨ ++≡ ⟩
         (u₂ ++ []) ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
         u₂ ++ f₂ ++ suf₂ ∎

  u₁≡ : u₁ ≡ u₂
  u₁≡ = noOverlapBoundary₂ FullLine.nooverlap noOverlapLines ++≡' fu₁ fu₁' fu₂ fin₂

  ++≡ᵤ : u₁' ++ b₁' ++ f₁ ++ suf₁ ≡ f₂ ++ suf₂
  ++≡ᵤ = Lemmas.++-cancel≡ˡ _ _ u₁≡ ++≡'

foldFinalIntoBodyWF{f₁ = f₁}{f₂ = f₂}{suf₁}{suf₂} (consIList{u₁}{b₁} fu₁ (consIList{u₁'}{b₁'} fu₁' body₁ refl) refl) fin₁ (consIList{u₂}{b₂} fu₂ (consIList{u₂'}{b₂'} fu₂' body₂ refl) refl) fin₂ (WellFounded.acc rs) ++≡ b₁< =
  proj₁ ih ,
    (u₂ ++ u₂' ++ b₂' ≡⟨ cong (u₂ ++_) (proj₂ ih) ⟩
    u₂ ++ (u₁' ++ b₁') ++ f₁ ++ take (proj₁ ih) suf₁ ≡⟨ cong (_++ ((u₁' ++ b₁') ++ f₁ ++ take (proj₁ ih) suf₁)) (sym u₁≡) ⟩
    u₁ ++ (u₁' ++ b₁') ++ f₁ ++ take (proj₁ ih) suf₁ ≡⟨ cong (u₁ ++_) (++-assoc u₁' _ _) ⟩
    u₁ ++ u₁' ++ b₁' ++ f₁ ++ take (proj₁ ih) suf₁ ≡⟨ sym (++-assoc u₁ u₁' _) ⟩
    (u₁ ++ u₁') ++ b₁' ++ f₁ ++ take (proj₁ ih) suf₁ ≡⟨ sym (++-assoc (u₁ ++ u₁') _ _) ⟩
    ((u₁ ++ u₁') ++ b₁') ++ f₁ ++ take (proj₁ ih) suf₁ ≡⟨ cong (_++ f₁ ++ take (proj₁ ih) suf₁) (++-assoc u₁ u₁' _) ⟩
    (u₁ ++ u₁' ++ b₁') ++ f₁ ++ take (proj₁ ih) suf₁ ∎)
  where
  module ≤ = Nat.≤-Reasoning

  ++≡' : u₁ ++ u₁' ++ b₁' ++ f₁ ++ suf₁ ≡ u₂ ++ u₂' ++ b₂' ++ f₂ ++ suf₂
  ++≡' = u₁ ++ u₁' ++ b₁' ++ f₁ ++ suf₁ ≡⟨ solve (++-monoid Char) ⟩
         (u₁ ++ u₁' ++ b₁') ++ f₁ ++ suf₁ ≡⟨ ++≡ ⟩
         (u₂ ++ u₂' ++ b₂') ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
         u₂ ++ u₂' ++ b₂' ++ f₂ ++ suf₂ ∎

  u₁≡ : u₁ ≡ u₂
  u₁≡ = noOverlapBoundary₂ FullLine.nooverlap FullLine.nooverlap ++≡' fu₁ fu₁' fu₂ fu₂'

  ++≡ᵤ : (u₁' ++ b₁') ++ f₁ ++ suf₁ ≡ (u₂' ++ b₂') ++ f₂ ++ suf₂
  ++≡ᵤ = trans (++-assoc u₁' b₁' _) (trans (Lemmas.++-cancel≡ˡ _ _ u₁≡ ++≡') (sym (++-assoc u₂' b₂' _)))

  b₁<' : length (u₁' ++ b₁') < length (u₂' ++ b₂')
  b₁<' = Nat.+-cancelˡ-< (length u₁) (≤.begin
    (1 + length u₁ + length (u₁' ++ b₁') ≤.≡⟨ sym (cong suc (length-++ u₁)) ⟩
    1 + length (u₁ ++ u₁' ++ b₁') ≤.≤⟨ b₁< ⟩
    length (u₂ ++ u₂' ++ b₂') ≤.≡⟨ length-++ u₂ ⟩
    length u₂ + length (u₂' ++ b₂') ≤.≡⟨ cong (λ x → length x + length (u₂' ++ b₂')) (sym u₁≡) ⟩
    length u₁ + length (u₂' ++ b₂') ≤.∎))

  ih = foldFinalIntoBodyWF (consIList fu₁' body₁ refl) fin₁ (consIList fu₂' body₂ refl) fin₂ (rs _ Nat.≤-refl) ++≡ᵤ b₁<'

@0 foldFinalIntoBody
  : ∀ {@0 b₁ f₁ b₂ f₂ suf₁ suf₂}
    → IList CertFullLine b₁ → CertFinalLine f₁
    → IList CertFullLine b₂ → CertFinalLine f₂
    → b₁ ++ f₁ ++ suf₁ ≡ b₂ ++ f₂ ++ suf₂
    → length b₁ < length b₂
    → Σ[ n ∈ ℕ ] b₂ ≡ b₁ ++ f₁ ++ take n suf₁
foldFinalIntoBody fu₁ fi₁ fu₂ fi₂ ++≡ b₁< = foldFinalIntoBodyWF fu₁ fi₁ fu₂ fi₂ (<-wellFounded (lengthIList fu₂)) ++≡ b₁<
  where open import Data.Nat.Induction

@0 body< : ∀ {@0 b₁ f₁ b₂ f₂ suf₁ suf₂}
        → IList CertFullLine b₁ → CertFinalLine f₁
        → IList CertFullLine b₂ → CertFinalLine f₂
        → b₁ ++ f₁ ++ suf₁ ≡ b₂ ++ f₂ ++ suf₂
        → length b₁ < length b₂
        → length b₁ + length f₁ ≤ length b₂ + length f₂
body<{b₁}{f₁}{b₂}{f₂}{suf₁}{suf₂} body₁ fin₁ body₂ fin₂ ++≡ b₁< =
  ≤.begin
    length b₁ + length f₁ ≤.≤⟨ Nat.m≤m+n (length b₁ + length f₁) _ ⟩
    (length b₁ + length f₁) + length (take (proj₁ lem) suf₁) ≤.≡⟨ cong (_+ (length (take (proj₁ lem) suf₁))) (sym (length-++ b₁)) ⟩
    length (b₁ ++ f₁) + length (take (proj₁ lem) suf₁) ≤.≡⟨ sym (length-++ (b₁ ++ f₁)) ⟩
    length ((b₁ ++ f₁) ++ take (proj₁ lem) suf₁) ≤.≡⟨ cong length (++-assoc b₁ f₁ _) ⟩
    length (b₁ ++ f₁ ++ take (proj₁ lem) suf₁) ≤.≡⟨ cong length (sym (proj₂ lem)) ⟩
    length b₂ ≤.≤⟨ Nat.m≤m+n (length b₂) (length f₂) ⟩
    length b₂ + length f₂ ≤.∎
  where
  module ≤ = Nat.≤-Reasoning

  lem = foldFinalIntoBody body₁ fin₁ body₂ fin₂ ++≡ b₁<
