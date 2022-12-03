{-# OPTIONS --subtyping #-}

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
import      Data.Nat.Properties as Nat
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.PEM.CertText.Properties where

open Aeres.Grammar.Definitions          Char
open Aeres.Grammar.IList                Char
open Aeres.Grammar.Relation.Definitions Char

open ≡-Reasoning

finalLineFromLines : ∀ {@0 bs} → IList CertFullLine bs → Erased (bs ≡ []) ⊎ &ₚ (IList CertFullLine) CertFinalLine bs
finalLineFromLines nil = inj₁ (─ refl)
finalLineFromLines (consIList{bs₁}{.[]} head₁ nil bs≡) =
  inj₂ (mk&ₚ nil (FinalLine.fromCertFullLine head₁)
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

postulate
  finalLineToLines : ∀ {@0 bs} → &ₚ (IList CertFullLine) (CertFinalLine ×ₚ (Erased ∘ (_≥ 65) ∘ length)) bs → IList CertFullLine bs

@0 foldFinalIntoBody
  : ∀ {@0 b₁ f₁ b₂ f₂ suf₁ suf₂}
    → IList CertFullLine b₁ → CertFinalLine f₁
    → IList CertFullLine b₂ → CertFinalLine f₂
    → b₁ ++ f₁ ++ suf₁ ≡ b₂ ++ f₂ ++ suf₂
    → length b₁ < length b₂
    → Σ[ n ∈ ℕ ] b₂ ≡ b₁ ++ f₁ ++ take n suf₁
foldFinalIntoBody{f₂ = f₂}{suf₁}{suf₂} nil
  (mkCertFinalLine{l₁}{e₁} lineₗ lineLenₗ eolₗ refl)
  (consIList{bs₂ = bs₂} fullL@(mkCertFullLine{l}{e} (mk×ₚ line line≡ refl) eol refl) tail₁ refl)
  fin₂@(mkCertFinalLine{l₂}{e₂} line₂ lineLen₂ eol₂ refl)
  ++≡ b₁< =
  proj₁ ∃n , (begin
    ((l ++ e) ++ bs₂ ≡⟨ solve (++-monoid Char) ⟩
    l ++ e ++ bs₂ ≡⟨ cong (_++ e ++ bs₂) (sym $ proj₁ l₁≡×) ⟩
    l₁ ++ e ++ bs₂ ≡⟨ cong (l₁ ++_) (sym $ proj₂ ∃n) ⟩
    l₁ ++ e₁ ++ take (proj₁ ∃n) suf₁ ≡⟨ solve (++-monoid Char) ⟩
    (l₁ ++ e₁) ++ take (proj₁ ∃n) suf₁ ∎))
  where
  module ≤ = Nat.≤-Reasoning

  @0 ++≡' : l₁ ++ e₁ ++ suf₁ ≡ l ++ e ++ bs₂ ++ f₂ ++ suf₂
  ++≡' =
    l₁ ++ e₁ ++ suf₁ ≡⟨ sym (++-assoc l₁ _ _) ⟩
    (l₁ ++ e₁) ++ suf₁ ≡⟨ ++≡ ⟩
    ((l ++ e) ++ bs₂) ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
    l ++ e ++ bs₂ ++ f₂ ++ suf₂ ∎

  @0 l₁≤ : length l₁ ≤ length l
  l₁≤ = ≤.begin
    length l₁ ≤.≤⟨ proj₂ lineLenₗ ⟩
    64 ≤.≡⟨ (sym $ ¡ line≡) ⟩
    length l ≤.∎

  @0 l≡ : l ≡ l₁ ++ drop (length l₁) l
  l≡ = Lemmas.drop-length-≤ l₁ _ l _ ++≡' l₁≤

  @0 ++≡ₗ : e₁ ++ suf₁ ≡ drop (length l₁) l ++ e ++ bs₂ ++ f₂ ++ suf₂
  ++≡ₗ = ++-cancelˡ l₁
           (l₁ ++ e₁ ++ suf₁ ≡⟨ ++≡' ⟩
           l ++ e ++ bs₂ ++ f₂ ++ suf₂ ≡⟨ cong (_++ e ++ bs₂ ++ f₂ ++ suf₂) l≡ ⟩
           (l₁ ++ drop (length l₁) l) ++ e ++ bs₂ ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
           l₁ ++ drop (length l₁) l ++ e ++ bs₂ ++ f₂ ++ suf₂ ∎)

  @0 l₁Len≡ : length l₁ ≡ length l
  l₁Len≡ =
    caseErased
      RFC5234.EOL.noOverlap l₁ (drop (length l₁) l) _ e₁ _
        (sym ++≡ₗ)
        (subst₀ Base64Str l≡ (Base64.Str.fromExactLength (mk×ₚ line line≡ refl)))
        lineₗ
    ret (const _)
    of λ where
      (inj₁ ≡[]) → ─
        (sym $ length l ≡⟨ cong length l≡ ⟩
        length (l₁ ++ drop (length l₁) l) ≡⟨ length-++ l₁ ⟩
        length l₁ + length (drop (length l₁) l) ≡⟨ cong (λ x → length l₁ + length x) ≡[] ⟩
        length l₁ + 0 ≡⟨ Nat.+-identityʳ (length l₁) ⟩
        length l₁ ∎)
      (inj₂ y) → contradiction eolₗ y

  @0 l₁≡× : l₁ ≡ l × e₁ ++ suf₁ ≡ e ++ bs₂ ++ f₂ ++ suf₂
  l₁≡× = Lemmas.length-++-≡ _ _ _ _ ++≡' l₁Len≡

  @0 e₁≤ : length e₁ ≤ length (e ++ bs₂)
  e₁≤ = caseErased finalLineFromLines tail₁ ret (const _) of λ where
    (inj₁ (─ refl)) → ─ Nat.≮⇒≥ λ where
      e< →
        let
          e<' : Erased (length e < length e₁)
          e<' = ─ Nat.≤-trans (s≤s (Lemmas.≡⇒≤ (cong length (sym (++-identityʳ e))))) e<

          e₁≡ : Erased (e₁ ≡ e ++ drop (length e) e₁)
          e₁≡ = ─ Lemmas.drop-length-≤
                    e _ e₁ _ (sym (proj₂ l₁≡×)) (Nat.<⇒≤ (¡ e<'))
        in
        ‼ contradiction₂
          (RFC5234.EOL.noOverlap' e (drop (length e) e₁) suf₁ l₂ (e₂ ++ suf₂)
            (++-cancelˡ e
              (e ++ drop (length e) e₁ ++ suf₁ ≡⟨ sym (++-assoc e _ _) ⟩
              (e ++ drop (length e) e₁) ++ suf₁ ≡⟨ cong (_++ suf₁) (sym $ ¡ e₁≡) ⟩
              e₁ ++ suf₁ ≡⟨ proj₂ l₁≡× ⟩
              e ++ bs₂ ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
              e ++ bs₂ ++ l₂ ++ e₂ ++ suf₂ ∎))
            (subst₀ EOL (¡ e₁≡) eolₗ) eol)
          (λ ≡[] →
            contradiction
              (length e ≡⟨ sym (Nat.+-identityʳ (length e)) ⟩
              length e + 0 ≡⟨ cong (λ x → length e + length x) (sym ≡[]) ⟩
              length e + length (drop (length e) e₁) ≡⟨ sym (length-++ e) ⟩
              length (e ++ drop (length e) e₁) ≡⟨ cong length (sym $ ¡ e₁≡) ⟩
              length e₁ ∎)
              (Nat.<⇒≢ (¡ e<')))
          (contradiction (mk×ₚ line₂ (─ (proj₁ lineLen₂)) refl))
    (inj₂ (mk&ₚ{b'}{f'} fstₚ₁ sndₚ₁ refl)) → ─ (≤.begin
      (length e₁ ≤.≤⟨ (proj₂ $ RFC5234.EOL.eolLen eolₗ) ⟩
      2 ≤.≤⟨ Nat.+-mono-≤ (proj₁ $ RFC5234.EOL.eolLen eol) (Nat.≤-trans (s≤s z≤n) (proj₁ (FinalLine.lengthRange sndₚ₁))) ⟩
      length e + length f' ≤.≤⟨ Nat.m≤m+n (length e + length f') _ ⟩
      length e + length f' + length b' ≤.≡⟨ Nat.+-assoc (length e) _ _ ⟩
      length e + (length f' + length b') ≤.≡⟨ cong (length e +_) (Nat.+-comm (length f') _) ⟩
      length e + (length b' + length f') ≤.≡⟨ cong (length e +_) (sym (length-++ b')) ⟩
      length e + length (b' ++ f') ≤.≡⟨ sym (length-++ e) ⟩
      length (e ++ b' ++ f') ≤.∎))

  @0 e₁++bs₁≡ : e ++ bs₂ ≡ e₁ ++ drop (length e₁) (e ++ bs₂)
  e₁++bs₁≡ =
    Lemmas.drop-length-≤ e₁ suf₁ (e ++ bs₂) (f₂ ++ suf₂)
           (trans (proj₂ l₁≡×)
             (e ++ bs₂ ++ (l₂ ++ e₂) ++ suf₂
               ≡⟨ solve (++-monoid Char) ⟩
              (e ++ bs₂) ++ (l₂ ++ e₂) ++ suf₂ ∎))
           e₁≤
  
  @0 suf₁≡ : suf₁ ≡ drop (length e₁) (e ++ bs₂) ++ f₂ ++ suf₂
  suf₁≡ =
    ++-cancelˡ e₁
      (e₁ ++ suf₁ ≡⟨ proj₂ l₁≡× ⟩
      e ++ bs₂ ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
      (e ++ bs₂) ++ f₂ ++ suf₂ ≡⟨ cong (_++ f₂ ++ suf₂) e₁++bs₁≡ ⟩
      (e₁ ++ drop (length e₁) (e ++ bs₂)) ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
      e₁ ++ drop (length e₁) (e ++ bs₂) ++ f₂ ++ suf₂ ∎)

  ∃n : Σ[ n ∈ ℕ ] e₁ ++ take n suf₁ ≡ e ++ bs₂
  ∃n = length (drop (length e₁) (e ++ bs₂)) , sym (begin
    (e ++ bs₂ ≡⟨ e₁++bs₁≡ ⟩
    e₁ ++ drop (length e₁) (e ++ bs₂) ≡⟨ cong (e₁ ++_) (sym (Lemmas.take-length-++ (drop (length e₁) (e ++ bs₂)) (f₂ ++ suf₂))) ⟩
    e₁ ++ take (length (drop (length e₁) (e ++ bs₂))) ((drop (length e₁) (e ++ bs₂)) ++ f₂ ++ suf₂) ≡⟨ cong (λ x → e₁ ++ take (length (drop (length e₁) (e ++ bs₂))) x) (sym suf₁≡) ⟩
    e₁ ++ take (length (drop (length e₁) (e ++ bs₂))) suf₁ ∎))

foldFinalIntoBody{f₁ = f₁}{f₂ = f₂}{suf₁}{suf₂}
  (consIList{bs₁} head₁ nil refl) fin₁
  (consIList{bs₂} head₂ (consIList{bs₃}{bs₄} head₃ tail₃ refl) refl) fin₂ ++≡ b₁< =
  {!!}
  where
  @0 ++≡' : bs₂ ++ bs₃ ++ bs₄ ++ f₂ ++ suf₂ ≡ bs₁ ++ f₁ ++ suf₁
  ++≡' = bs₂ ++ bs₃ ++ bs₄ ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
         (bs₂ ++ bs₃ ++ bs₄) ++ f₂ ++ suf₂ ≡⟨ sym ++≡ ⟩
         (bs₁ ++ []) ++ f₁ ++ suf₁ ≡⟨ solve (++-monoid Char) ⟩
         bs₁ ++ f₁ ++ suf₁ ∎

  @0 bs₁≤bs₂ : length bs₁ ≤ length bs₂
  bs₁≤bs₂ = Nat.≮⇒≥ λ bs₂<bs₁ →
    let bs₁≡ : Erased (bs₁ ≡ bs₂ ++ drop (length bs₂) bs₁)
        bs₁≡ = ─ Lemmas.drop-length-≤ bs₂ (bs₃ ++ bs₄ ++ f₂ ++ suf₂) bs₁ (f₁ ++ suf₁) ++≡' (Nat.<⇒≤ bs₂<bs₁)

        ++≡“ : Erased (drop (length bs₂) bs₁ ++ f₁ ++ suf₁ ≡ bs₃ ++ bs₄ ++ f₂ ++ suf₂)
        ++≡“ = ─ ++-cancelˡ bs₂
          (bs₂ ++ drop (length bs₂) bs₁ ++ f₁ ++ suf₁ ≡⟨ solve (++-monoid Char) ⟩
          (bs₂ ++ drop (length bs₂) bs₁) ++ f₁ ++ suf₁ ≡⟨ cong (_++ f₁ ++ suf₁) (sym (¡ bs₁≡)) ⟩
          bs₁ ++ f₁ ++ suf₁ ≡⟨ sym ++≡' ⟩
          bs₂ ++ bs₃ ++ bs₄ ++ f₂ ++ suf₂ ∎)
    in
    contradiction₂
      (FullLine.nooverlap bs₂ (drop (length bs₂) bs₁) (f₁ ++ suf₁) bs₃ _ (¡ ++≡“) (subst₀ CertFullLine (¡ bs₁≡) head₁) head₂)
      (λ ≡[] →
        contradiction {P = length bs₂ ≡ length bs₁}
          (length bs₂ ≡⟨ sym (Nat.+-identityʳ (length bs₂)) ⟩
          length bs₂ + 0 ≡⟨ cong (length bs₂ +_) (cong length (sym ≡[])) ⟩
          length bs₂ + length (drop (length bs₂) bs₁) ≡⟨ sym (length-++ bs₂) ⟩
          length (bs₂ ++ drop (length bs₂) bs₁) ≡⟨ cong length (sym (¡ bs₁≡)) ⟩
          length bs₁ ∎)
          (Nat.<⇒≢ bs₂<bs₁))
      (contradiction head₃)

  @0 bs₂≡ : bs₂ ≡ bs₁ ++ drop (length bs₁) bs₂
  bs₂≡ = Lemmas.drop-length-≤ bs₁ _ bs₂ (bs₃ ++ bs₄ ++ f₂ ++ suf₂) (sym ++≡') bs₁≤bs₂

  @0 ++≡“ : drop (length bs₁) bs₂ ++ bs₃ ++ bs₄ ++ f₂ ++ suf₂ ≡ f₁ ++ suf₁
  ++≡“ = ++-cancelˡ bs₁
    (bs₁ ++ drop (length bs₁) bs₂ ++ bs₃ ++ bs₄ ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
    (bs₁ ++ drop (length bs₁) bs₂) ++ bs₃ ++ bs₄ ++ f₂ ++ suf₂ ≡⟨ cong (_++ bs₃ ++ _) (sym bs₂≡) ⟩
    bs₂ ++ bs₃ ++ bs₄ ++ f₂ ++ suf₂ ≡⟨ ++≡' ⟩
    bs₁ ++ f₁ ++ suf₁ ∎)

  @0 bs₁≡ : length bs₁ ≡ length bs₂
  bs₁≡ =
    [_,_]
      (λ ≡[] →
        length bs₁ ≡⟨ sym (Nat.+-identityʳ (length bs₁)) ⟩
        length bs₁ + 0 ≡⟨ cong (λ x → length bs₁ + length x) (sym ≡[]) ⟩
        length bs₁ + length (drop (length bs₁) bs₂) ≡⟨ sym (length-++ bs₁) ⟩
        length (bs₁ ++ drop (length bs₁) bs₂) ≡⟨ cong length (sym bs₂≡) ⟩
        length bs₂ ∎)
      (λ x → contradiction fin₁ x)
      (noOverlapLines bs₁ (drop (length bs₁) bs₂) _ f₁ _ ++≡“ (subst₀ CertFullLine bs₂≡ head₂) head₁)
-- {-# TERMINATING #-}
-- @0 body< : ∀ {@0 b₁ f₁ b₂ f₂ suf₁ suf₂}
--         → IList CertFullLine b₁ → CertFinalLine f₁
--         → IList CertFullLine b₂ → CertFinalLine f₂
--         → b₁ ++ f₁ ++ suf₁ ≡ b₂ ++ f₂ ++ suf₂
--         → length b₁ < length b₂
--         → length b₁ + length f₁ ≤ length b₂ + length f₂
-- body<{f₂ = f₂} nil (mkCertFinalLine{l₁}{e₁} lineₗ lineLenₗ eolₗ refl) (consIList{bs₂ = bs₂} fullL@(mkCertFullLine{l}{e} (mk×ₚ line line≡ refl) eol refl) tail₁ refl) fin₂ ++≡ b₁< =
--   ≤.begin
--     length (l₁ ++ e₁) ≤.≡⟨ length-++ l₁ ⟩
--     length l₁ + length e₁ ≤.≤⟨ Nat.+-mono-≤ (proj₂ lineLenₗ) (proj₂ $ RFC5234.EOL.eolLen eolₗ) ⟩
--     64 + 2 ≤.≤⟨ toWitness{Q = _ ≤? _} tt ⟩
--     65 + 2 ≤.≤⟨ Nat.+-mono-≤ (proj₁ (FullLine.fullLineLen fullL)) (proj₁ $ FinalLine.lengthRange fin₂ ) ⟩
--     length (l ++ e) + length f₂ ≤.≤⟨ Nat.+-monoˡ-≤ (length f₂) (Nat.m≤m+n (length (l ++ e)) (length bs₂)) ⟩
--     (length (l ++ e) + length bs₂) + length f₂ ≤.≡⟨ cong (_+ length f₂) (sym (length-++ (l ++ e))) ⟩
--     (length ((l ++ e) ++ bs₂)) + length f₂ ≤.∎ 
--   where module ≤ = Nat.≤-Reasoning
-- body<{f₁ = f₁}{f₂ = f₂}{suf₁}{suf₂} (consIList{bs₁} head₁ nil refl) fin₁ (consIList{bs₂} head₂ nil refl) fin₂ ++≡ b₁< =
--   let b₁<' : length bs₁ < length bs₂
--       b₁<' = subst₂ (λ x y → length x < length y) (++-identityʳ bs₁) (++-identityʳ bs₂) b₁<

--       bs₂≡ : Erased (bs₂ ≡ bs₁ ++ drop (length bs₁) bs₂)
--       bs₂≡ = ─ Lemmas.drop-length-≤ bs₁ (f₁ ++ suf₁) _ _ xs≡ (Nat.<⇒≤ b₁<')
--   in
--   caseErased noOverlapLines bs₁ (drop (length bs₁) bs₂) (f₂ ++ suf₂) f₁ suf₁
--                (++-cancelˡ bs₁ (begin
--                  (bs₁ ++ (drop (length bs₁) bs₂) ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
--                  (bs₁ ++ drop (length bs₁) bs₂) ++ f₂ ++ suf₂ ≡⟨ cong (_++ f₂ ++ suf₂) (sym (¡ bs₂≡)) ⟩
--                  bs₂ ++ f₂ ++ suf₂ ≡⟨ sym xs≡ ⟩
--                  bs₁ ++ f₁ ++ suf₁ ∎)))
--                (subst CertFullLine (¡ bs₂≡) head₂) head₁
--   ret (const _) of λ where
--     (inj₁ x) →
--       ─ contradiction
--           (begin (length bs₁ ≡⟨ cong length (sym (++-identityʳ bs₁)) ⟩
--                  length (bs₁ ++ []) ≡⟨ cong (length ∘ (bs₁ ++_)) (sym x) ⟩
--                  length (bs₁ ++ drop (length bs₁) bs₂) ≡⟨ cong length (sym (¡ bs₂≡)) ⟩
--                  length bs₂ ∎))
--           (Nat.<⇒≢ b₁<')
--     (inj₂ y) → ─ contradiction fin₁ y
--   where
--   xs≡ : bs₁ ++ f₁ ++ suf₁ ≡ bs₂ ++ f₂ ++ suf₂
--   xs≡ = begin (bs₁ ++ f₁ ++ suf₁ ≡⟨ solve (++-monoid Char) ⟩
--               (bs₁ ++ []) ++ f₁ ++ suf₁ ≡⟨ ++≡ ⟩
--               (bs₂ ++ []) ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
--               bs₂ ++ f₂ ++ suf₂ ∎)
-- body<{f₁ = f₁}{f₂ = f₂}{suf₁}{suf₂}
--   (consIList{bs₁} head₁ nil refl) fin₁
--   (consIList{bs₂} head₂ (consIList{bs₃}{bs₄} head₃ tail₃ refl) refl) fin₂ ++≡ b₁< =
--   caseErased Nat.<-cmp (length bs₁) (length bs₂) ret (const _) of λ where
--     (tri< bs₁< bs₁≢ _) →
--       let
--         bs₂≡ : Erased (bs₂ ≡ bs₁ ++ drop (length bs₁) bs₂)
--         bs₂≡ = ─ Lemmas.drop-length-≤ bs₁ (f₁ ++ suf₁) bs₂ (bs₃ ++ bs₄ ++ f₂ ++ suf₂) xs≡ (Nat.<⇒≤ bs₁<)

--         bs≡“ : Erased (f₁ ++ suf₁ ≡ drop (length bs₁) bs₂ ++ bs₃ ++ bs₄ ++ f₂ ++ suf₂)
--         bs≡“ = ─ ++-cancelˡ bs₁ (begin
--           (bs₁ ++ f₁ ++ suf₁ ≡⟨ xs≡ ⟩
--           bs₂ ++ bs₃ ++ bs₄ ++ f₂ ++ suf₂ ≡⟨ cong (_++ bs₃ ++ bs₄ ++ f₂ ++ suf₂) (¡ bs₂≡) ⟩
--           (bs₁ ++ drop (length bs₁) bs₂) ++ bs₃ ++ bs₄ ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
--           bs₁ ++ drop (length bs₁) bs₂ ++ bs₃ ++ bs₄ ++ f₂ ++ suf₂ ∎))
--       in
--       ─ contradiction₂
--         (noOverlapLines bs₁ (drop (length bs₁) bs₂) (bs₃ ++ bs₄ ++ f₂ ++ suf₂) f₁ suf₁
--           (sym $ ¡ bs≡“)
--           (subst₀ CertFullLine (¡ bs₂≡) head₂)
--           head₁)
--         (drop (length bs₁) bs₂ ≢ [] ∋ λ ≡[] →
--           contradiction (cong length ≡[]) (Nat.>⇒≢ (≤.begin
--             (1 ≤.≤⟨ Nat.m<n⇒0<n∸m bs₁< ⟩
--             length bs₂ - length bs₁ ≤.≡⟨ sym (length-drop (length bs₁) bs₂) ⟩
--             length (drop (length bs₁) bs₂) ≤.∎))))
--         (contradiction fin₁)
--     (tri> _ bs₁≢ bs₁>) → 
--       let
--         bs₂≡ : Erased (bs₁ ≡ bs₂ ++ drop (length bs₂) bs₁)
--         bs₂≡ = ─ Lemmas.drop-length-≤ bs₂ _ bs₁ _ (sym xs≡) (Nat.<⇒≤ bs₁>)

--         bs≡“ : Erased (drop (length bs₂) bs₁ ++ f₁ ++ suf₁ ≡ bs₃ ++ bs₄ ++ f₂ ++ suf₂)
--         bs≡“ = ─ ++-cancelˡ bs₂
--           (bs₂ ++ drop (length bs₂) bs₁ ++ f₁ ++ suf₁ ≡⟨ solve (++-monoid Char) ⟩
--           (bs₂ ++ drop (length bs₂) bs₁) ++ f₁ ++ suf₁ ≡⟨ cong (_++ f₁ ++ suf₁) (sym $ ¡ bs₂≡) ⟩
--           bs₁ ++ f₁ ++ suf₁ ≡⟨ xs≡ ⟩
--           _ ∎)
--       in
--       ─ contradiction₂
--           (FullLine.nooverlap bs₂ (drop (length bs₂) bs₁) (f₁ ++ suf₁) bs₃ _
--             (¡ bs≡“)
--             (subst₀ CertFullLine (¡ bs₂≡) head₁)
--             head₂)
--           (λ ≡[] →
--             contradiction (cong length ≡[]) (Nat.>⇒≢ (≤.begin
--               (1 ≤.≤⟨ Nat.m<n⇒0<n∸m bs₁> ⟩
--               length bs₁ - length bs₂ ≤.≡⟨ sym (length-drop (length bs₂) bs₁) ⟩
--               length (drop (length bs₂) bs₁) ≤.∎))))
--           (contradiction head₃)

--     (tri≈ _ bs₁≡ _) → ─
--       (let bs₂≡ : bs₁ ≡ bs₂
--            bs₂≡ = proj₁ (Lemmas.length-++-≡ _ _ _ _ xs≡ bs₁≡)

--            xs≡' : f₁ ++ suf₁ ≡ bs₃ ++ bs₄ ++ f₂ ++ suf₂
--            xs≡' = Lemmas.++-cancel≡ˡ _ _ bs₂≡ xs≡

--            f₁≤ : length f₁ ≤ length bs₃
--            f₁≤ = caseErased Nat.<-cmp (length f₁) (length bs₃) ret (const _) of λ where
--              (tri< f₁< _ _) → ─ (Nat.<⇒≤ f₁<)
--              (tri≈ _ f₁≡ _) → ─ (Lemmas.≡⇒≤ f₁≡)
--              (tri> _ _ f₁>) → ─
--                let f₁≡ : f₁ ≡ bs₃ ++ drop (length bs₃) f₁
--                    f₁≡ = Lemmas.drop-length-≤ bs₃ (bs₄ ++ f₂ ++ suf₂) _ _ (sym xs≡') (Nat.<⇒≤ f₁>)
--                in
--                contradiction₂
--                  (noOverlapLemma₁ bs₃ (drop (length bs₃) f₁) suf₁ (bs₄ ++ f₂) suf₂
--                     (++-cancelˡ bs₃
--                       (bs₃ ++ drop (length bs₃) f₁ ++ suf₁ ≡⟨ solve (++-monoid Char) ⟩
--                       (bs₃ ++ drop (length bs₃) f₁) ++ suf₁ ≡⟨ cong (_++ suf₁) (sym f₁≡) ⟩
--                       f₁ ++ suf₁ ≡⟨ xs≡' ⟩
--                       bs₃ ++ bs₄ ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
--                       bs₃ ++ (bs₄ ++ f₂) ++ suf₂ ∎))
--                     (subst₀ CertFinalLine f₁≡ fin₁)
--                     (FinalLine.fromCertFullLine head₃))
--                  (λ ≡[] →
--                    contradiction (cong length ≡[]) (Nat.>⇒≢ (≤.begin
--                      1 ≤.≤⟨ Nat.m<n⇒0<n∸m f₁> ⟩
--                      length f₁ - length bs₃ ≤.≡⟨ sym (length-drop (length bs₃) f₁) ⟩
--                      length (drop (length bs₃) f₁) ≤.∎)))
--                  (contradiction (mk&ₚ tail₃ fin₂ refl))

--            -- f₁≡ = caseErased Nat.<-cmp (length f₁) (length bs₃) ret (const _) of λ where
--            --         (tri< f₁< f₁≢ _) → ─
--            --           (let bs₃≡ : bs₃ ≡ f₁ ++ drop (length f₁) bs₃
--            --                bs₃≡ = Lemmas.drop-length-≤ f₁ suf₁ _ _ xs≡' (Nat.<⇒≤ f₁<)

--            --                xs≡“ : drop (length f₁) bs₃ ++ bs₄ ++ f₂ ++ suf₂ ≡ suf₁
--            --                xs≡“ = ++-cancelˡ f₁
--            --                         (f₁ ++ drop (length f₁) bs₃ ++ bs₄ ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
--            --                         (f₁ ++ drop (length f₁) bs₃) ++ bs₄ ++ f₂ ++ suf₂ ≡⟨ cong (_++ bs₄ ++ f₂ ++ suf₂) (sym bs₃≡) ⟩
--            --                         bs₃ ++ bs₄ ++ f₂ ++ suf₂ ≡⟨ sym xs≡' ⟩
--            --                         f₁ ++ suf₁ ∎)
--            --            in
--            --            contradiction₂
--            --              {!!}
--            --              {!!}
--            --              {!!}
--            --           )
--            --         (tri> _ f₁≢ f₁>) → {!!}
--            --         (tri≈ _ f₁≡ _) → ─ proj₁ (Lemmas.length-++-≡ _ _ _ _ xs≡' f₁≡)
--        in
--        ≤.begin (length (bs₁ ++ []) + length f₁ ≤.≡⟨ cong (λ x → length x + length f₁) (++-identityʳ bs₁) ⟩
--                length bs₁ + length f₁ ≤.≡⟨ cong (λ x → length x + length f₁) bs₂≡ ⟩
--                length bs₂ + length f₁ ≤.≤⟨ Nat.+-monoʳ-≤ (length bs₂) f₁≤ ⟩
--                length bs₂ + length bs₃ ≤.≡⟨ sym (length-++ bs₂) ⟩
--                length (bs₂ ++ bs₃) ≤.≤⟨ Nat.m≤m+n (length (bs₂ ++ bs₃)) _ ⟩
--                length (bs₂ ++ bs₃) + length bs₄ ≤.≡⟨ sym (length-++ (bs₂ ++ bs₃)) ⟩
--                length ((bs₂ ++ bs₃) ++ bs₄) ≤.≡⟨ cong length (++-assoc bs₂ bs₃ _) ⟩
--                length (bs₂ ++ bs₃ ++ bs₄) ≤.≤⟨ Nat.m≤m+n _ (length f₂) ⟩
--                length (bs₂ ++ bs₃ ++ bs₄) + length f₂ ≤.∎)
--        )

--   where
--   module ≤ = Nat.≤-Reasoning

--   xs≡ : bs₁ ++ f₁ ++ suf₁ ≡ bs₂ ++ bs₃ ++ bs₄ ++ f₂ ++ suf₂
--   xs≡ = begin (bs₁ ++ f₁ ++ suf₁ ≡⟨ solve (++-monoid Char) ⟩
--               (bs₁ ++ []) ++ f₁ ++ suf₁ ≡⟨ ++≡ ⟩
--               (bs₂ ++ bs₃ ++ bs₄) ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
--               bs₂ ++ bs₃ ++ bs₄ ++ f₂ ++ suf₂ ∎)

-- body<{f₁ = f₁}{f₂ = f₂} (consIList{bs₁} head₁ (consIList{bs₁ = bs₂ₕ}{bs₂ = bs₂ₜ} head₂ tail₂ refl) refl) fin₁ (consIList{bs₁ = bs₃} head₃ nil refl) fin₂ ++≡ b₁< =
--   contradiction b₁< (Nat.<⇒≱ (s≤s
--     (≤.begin
--       (length (bs₃ ++ []) ≤.≡⟨ cong length (++-identityʳ bs₃) ⟩
--       length bs₃ ≤.≤⟨ proj₂ (FullLine.fullLineLen head₃) ⟩
--       66 ≤.≤⟨ Nat.+-monoˡ-≤ 1 (proj₁ (FullLine.fullLineLen head₁)) ⟩
--       length bs₁ + 1 ≤.≤⟨ Nat.+-monoʳ-≤ (length bs₁) (s≤s z≤n) ⟩
--       length bs₁ + 65 ≤.≤⟨ Nat.+-monoʳ-≤ (length bs₁) (proj₁ (FullLine.fullLineLen head₂)) ⟩
--       length bs₁ + length bs₂ₕ ≤.≡⟨ sym (length-++ bs₁) ⟩
--       length (bs₁ ++ bs₂ₕ) ≤.≤⟨ Nat.m≤m+n _ (length bs₂ₜ) ⟩
--       length (bs₁ ++ bs₂ₕ) + length bs₂ₜ ≤.≡⟨ sym (length-++ (bs₁ ++ bs₂ₕ)) ⟩
--       length ((bs₁ ++ bs₂ₕ) ++ bs₂ₜ) ≤.≡⟨ cong length (++-assoc bs₁ _ _) ⟩
--       length (bs₁ ++ bs₂ₕ ++ bs₂ₜ) ≤.∎))))
  
--   where
--   module ≤ = Nat.≤-Reasoning

-- body<{f₁ = f₁}{f₂ = f₂}{suf₁}{suf₂} (consIList{bs₁} head₁ tail₁@(consIList{bs₂}{bs₃} head₂ tail₂ refl) refl) fin₁ (consIList{bs₄} head₃ tail₃@(consIList{bs₅}{bs₆} head₄ tail₄ refl) refl) fin₂ ++≡ b₁< =
--   caseErased Nat.<-cmp (length bs₁) (length bs₄) ret (const _) of λ where
--     (tri< bs₁< bs₁≢ _) → ─
--       (let bs₄≡ : bs₄ ≡ bs₁ ++ drop (length bs₁) bs₄
--            bs₄≡ = Lemmas.drop-length-≤ bs₁ _ _ _ xs≡ (Nat.<⇒≤ bs₁<)
--        in
--        case FullLine.nooverlap bs₁ (drop (length bs₁) bs₄) (bs₅ ++ bs₆ ++ f₂ ++ suf₂) bs₂ (bs₃ ++ f₁ ++ suf₁)
--               (++-cancelˡ bs₁
--                 (begin (bs₁ ++ drop (length bs₁) bs₄ ++ bs₅ ++ bs₆ ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
--                        (bs₁ ++ drop (length bs₁) bs₄) ++ bs₅ ++ bs₆ ++ f₂ ++ suf₂ ≡⟨ (cong (_++ _) ∘ sym $ bs₄≡) ⟩
--                        bs₄ ++ bs₅ ++ bs₆ ++ f₂ ++ suf₂ ≡⟨ sym xs≡ ⟩
--                        _ ∎)))
--               (subst CertFullLine bs₄≡ head₃) head₁
--        ret (const _) of λ where
--         (inj₁ x) → contradiction{P = length bs₄ ≡ length bs₁}
--                      (begin
--                        length bs₄ ≡⟨ cong length bs₄≡ ⟩
--                        length (bs₁ ++ drop (length bs₁) bs₄) ≡⟨ cong (length ∘ (bs₁ ++_)) x ⟩
--                        length (bs₁ ++ []) ≡⟨ cong length (++-identityʳ bs₁) ⟩
--                        length bs₁ ∎) 
--                      (Nat.>⇒≢ bs₁<)
--         (inj₂ y) → contradiction head₂ y)
--     (tri> _ bs₁≢ bs₁>) → ─
--       (let bs₁≡' : bs₁ ≡ bs₄ ++ drop (length bs₄) bs₁
--            bs₁≡' = Lemmas.drop-length-≤ bs₄ _ _ _ (sym xs≡) (Nat.<⇒≤ bs₁>)
--        in
--        case FullLine.nooverlap bs₄ (drop (length bs₄) bs₁) (bs₂ ++ bs₃ ++ f₁ ++ suf₁) bs₅ (bs₆ ++ f₂ ++ suf₂)
--               (++-cancelˡ bs₄
--                 (begin (bs₄ ++ drop (length bs₄) bs₁ ++ bs₂ ++ bs₃ ++ f₁ ++ suf₁ ≡⟨ solve (++-monoid Char) ⟩
--                        (bs₄ ++ drop (length bs₄) bs₁) ++ bs₂ ++ bs₃ ++ f₁ ++ suf₁ ≡⟨ cong (_++ _) (sym bs₁≡') ⟩
--                        bs₁ ++ bs₂ ++ bs₃ ++ f₁ ++ suf₁  ≡⟨ xs≡ ⟩
--                        _ ∎)))
--               (subst CertFullLine bs₁≡' head₁) head₃
--        ret (const _) of λ where
--          (inj₁ x) →
--            contradiction{P = length bs₁ ≡ length bs₄}
--              (begin (length bs₁ ≡⟨ cong length bs₁≡' ⟩
--                     length (bs₄ ++ drop (length bs₄) bs₁) ≡⟨ cong (length ∘ (bs₄ ++_)) x ⟩
--                     length (bs₄ ++ []) ≡⟨ cong length (++-identityʳ bs₄) ⟩
--                     length bs₄ ∎))
--              bs₁≢
--          (inj₂ y) → contradiction head₄ y
--       )
--     (tri≈ _ len≡ _) →
--       ─ (≤.begin (length (bs₁ ++ bs₂ ++ bs₃) + length f₁ ≤.≡⟨ cong (_+ length f₁) (length-++ bs₁) ⟩
--                  length bs₁ + length (bs₂ ++ bs₃) + length f₁ ≤.≡⟨ Nat.+-assoc (length bs₁) (length (bs₂ ++ bs₃)) (length f₁) ⟩
--                  length bs₁ + (length (bs₂ ++ bs₃) + length f₁) ≤.≤⟨ Nat.+-monoʳ-≤ (length bs₁) (rec len≡) ⟩
--                  length bs₁ + (length (bs₅ ++ bs₆) + length f₂) ≤.≡⟨ cong (_+ _) len≡ ⟩
--                  length bs₄ + (length (bs₅ ++ bs₆) + length f₂) ≤.≡⟨ sym (Nat.+-assoc (length bs₄) _ _) ⟩
--                  length bs₄ + length (bs₅ ++ bs₆) + length f₂ ≤.≡⟨ cong (_+ length f₂) (sym (length-++ bs₄)) ⟩
--                  length (bs₄ ++ bs₅ ++ bs₆) + length f₂ ≤.∎))
--   where
--   module ≤ = Nat.≤-Reasoning

--   xs≡ : bs₁ ++ bs₂ ++ bs₃ ++ f₁ ++ suf₁ ≡ bs₄ ++ bs₅ ++ bs₆ ++ f₂ ++ suf₂
--   xs≡ = begin bs₁ ++ bs₂ ++ bs₃ ++ f₁ ++ suf₁ ≡⟨ solve (++-monoid Char) ⟩
--               (bs₁ ++ bs₂ ++ bs₃) ++ f₁ ++ suf₁ ≡⟨ ++≡ ⟩
--               (bs₄ ++ bs₅ ++ bs₆) ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
--               bs₄ ++ bs₅ ++ bs₆ ++ f₂ ++ suf₂ ∎

--   module _ (@0 len≡ : length bs₁ ≡ length bs₄) where
--     bs₁≡ : Erased (bs₁ ≡ bs₄)
--     bs₁≡ = ─ proj₁ (Lemmas.length-++-≡ _ _ _ _ xs≡ len≡)

--     rec : (length (bs₂ ++ bs₃) + length f₁ ≤ length (bs₅ ++ bs₆) + length f₂)
--     rec = body<{suf₁ = suf₁}{suf₂} tail₁ fin₁ tail₃ fin₂
--                (Lemmas.++-cancel≡ˡ _ _ (¡ bs₁≡)
--                  (begin (bs₁ ++ (bs₂ ++ bs₃) ++ f₁ ++ suf₁ ≡⟨ solve (++-monoid Char) ⟩
--                         bs₁ ++ bs₂ ++ bs₃ ++ f₁ ++ suf₁ ≡⟨ xs≡ ⟩
--                         bs₄ ++ bs₅ ++ bs₆ ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
--                         bs₄ ++ (bs₅ ++ bs₆) ++ f₂ ++ suf₂ ∎)))
--                (Nat.+-cancelˡ-< (length bs₁)
--                  (≤.begin
--                    (1 + length bs₁ + length (bs₂ ++ bs₃) ≤.≡⟨ cong (1 +_) (sym (length-++ bs₁)) ⟩
--                    1 + length (bs₁ ++ bs₂ ++ bs₃) ≤.≤⟨ b₁< ⟩
--                    length (bs₄ ++ bs₅ ++ bs₆) ≤.≡⟨ length-++ bs₄ ⟩
--                    length bs₄ + length (bs₅ ++ bs₆) ≤.≡⟨ cong (_+ length (bs₅ ++ bs₆)) (cong length (sym (¡ bs₁≡))) ⟩
--                    length bs₁ + length (bs₅ ++ bs₆) ≤.∎)))      


