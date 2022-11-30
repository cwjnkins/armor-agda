{-# OPTIONS --subtyping #-}

open import Aeres.Binary
  renaming (module Base64 to B64)
open import Aeres.Data.Base64
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

module Aeres.Data.PEM.CertText.Properties where

open Aeres.Grammar.Definitions          Char
open Aeres.Grammar.IList                Char
open Aeres.Grammar.Relation.Definitions Char

open ≡-Reasoning

noOverlapLines : NoOverlap CertFullLine CertFinalLine
noOverlapLines ws [] ys₁ xs₂ ys₂ xs₁++ys₁≡xs₂++ys₂ f₁ f₂ = inj₁ refl
noOverlapLines ws xs₁@(x₁ ∷ xs₁') ys₁ xs₂ ys₂ xs₁++ys₁≡xs₂++ys₂
  (mkCertFullLine{l}{e} (mk×ₚ line (─ lineLen) refl) eol bs≡)
  (mkCertFullLine{l₁}{e₁} (mk×ₚ line₁ (─ lineLen₁) refl) eol₁ bs≡₁) =
  inj₂ noway
  where
  open ≡-Reasoning

  @0 bs≡' : l₁ ++ e₁ ++ xs₁ ≡ l ++ e
  bs≡' = l₁ ++ e₁ ++ xs₁ ≡⟨ sym (++-assoc l₁ e₁ xs₁) ⟩
         (l₁ ++ e₁) ++ xs₁ ≡⟨ cong (_++ xs₁) (sym bs≡₁) ⟩
         ws ++ xs₁ ≡⟨ bs≡ ⟩
         l ++ e ∎

  @0 l×e≡ : l₁ ≡ l × (e₁ ++ xs₁) ≡ e
  l×e≡ = Lemmas.length-++-≡ _ _ _ _ bs≡'
           (length l₁ ≡⟨ lineLen₁ ⟩
            64 ≡⟨ sym lineLen ⟩
            length l ∎)

  @0 x₁≡ : x₁ ≡ '\r' ⊎ x₁ ≡ '\n'
  x₁≡ = RFC5234.EOL.char∈ (subst₀ (x₁ ∈_) (proj₂ l×e≡) (Any.++⁺ʳ e₁ (here refl))) eol

  @0 x₁∉ : x₁ ∉ B64.charset
  x₁∉ = case x₁≡ ret (const _) of λ where
    (inj₁ refl) → toWitnessFalse{Q = _ ∈? _} tt
    (inj₂ refl) → toWitnessFalse{Q = _ ∈? _} tt

  @0 x₁≢ : x₁ ≢ '='
  x₁≢ = case x₁≡ ret (const _) of λ where
    (inj₁ refl) → λ ()
    (inj₂ refl) → λ ()

  noway : ¬ CertFinalLine xs₂
  noway (mkCertFinalLine{l'}{e'} line' lineLen' eol' bs≡“) =
    ‼ contradiction₂ l₁'∈
        (subst₀ (_∉ B64.charset) l₁'≡ x₁∉)
        (subst₀ (_≢ '=') l₁'≡ x₁≢)
    where
    abstract
      @0 l'≡ : Σ[ p ∈ Char × List Char ] uncurry _∷_ p ≡ l'
      l'≡ = case singleton l' refl ret (const _) of λ where
        (singleton [] refl) → contradiction lineLen' λ ()
        (singleton (x ∷ x₁) refl) → (x , x₁) , refl

    @0 l₁' : Char
    l₁' = proj₁ (proj₁ l'≡)

    @0 l“ : List Char
    l“  = proj₂ (proj₁ l'≡)

    @0 l₁'≡ : x₁ ≡ l₁'
    l₁'≡ = ∷-injectiveˡ
             (x₁ ∷ xs₁' ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
              xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡“ ⟩
              (l' ++ e') ++ ys₂ ≡⟨ ++-assoc l' e' ys₂ ⟩
              l' ++ e' ++ ys₂ ≡⟨ cong (λ x → x ++ e' ++ ys₂) (sym (proj₂ l'≡)) ⟩
              (l₁' ∷ l“) ++ e' ++ ys₂ ∎)

    line“ : Base64Str (l₁' ∷ l“)
    line“ = subst₀ Base64Str (sym (proj₂ l'≡)) line'

    @0 l₁'∈ : l₁' ∈ B64.charset ⊎ l₁' ≡ '='
    l₁'∈ = Base64.Str.char∈ (here refl) line“

noOverlapLemma₁ : NoOverlap CertFinalLine (&ₚ (IList CertFullLine) CertFinalLine)
noOverlapLemma₁ ws [] ys₁ xs₂ ys₂ x x₁ x₂ = inj₁ refl
noOverlapLemma₁ ws xs₁@(x₁ ∷ xs₁') ys₁ xs₂ ys₂ xs₁++ys₁≡xs₂++ys₂
  (mkCertFinalLine{l}{e} line lineLen eol bs≡) (mkCertFinalLine{l₁}{e₁} line₁ lineLen₁ eol₁ bs≡₁) =
  {!!}
  where
  open ≡-Reasoning

  @0 bs≡' : l₁ ++ e₁ ++ xs₁ ≡ l ++ e
  bs≡' = l₁ ++ e₁ ++ xs₁ ≡⟨ sym (++-assoc l₁ e₁ xs₁) ⟩
         (l₁ ++ e₁) ++ xs₁ ≡⟨ cong (_++ xs₁) (sym bs≡₁) ⟩
         ws ++ xs₁ ≡⟨ bs≡ ⟩
         l ++ e ∎

  module Len< (len< : length l₁ < length l) where
    @0 l≡ : l ≡ l₁ ++ drop (length l₁) l
    l≡ = Lemmas.drop-length-≤ l₁ _ _ _ bs≡' (Nat.<⇒≤ len<)

    @0 lenDrop : length (drop (length l₁) l) ≡ length l - length l₁
    lenDrop = length-drop (length l₁) l

    @0 lenDrop>0 : 0 < length (drop (length l₁) l)
    lenDrop>0 = Nat.≤-trans (Nat.m<n⇒0<n∸m len<) (Lemmas.≡⇒≤ (sym lenDrop))

    abstract
      @0 l≡∷ :  Σ[ p ∈ Char × List Char ] uncurry _∷_ p ≡ drop (length l₁) l
      l≡∷ = caseErased (singleton (drop (length l₁) l) refl) ret (const _) of λ where
        (singleton [] x≡) →
          contradiction{P = 0 < 0}
            (Nat.≤-trans lenDrop>0 (Lemmas.≡⇒≤ (cong length (sym x≡))))
            λ ()
        (singleton (x ∷ x₁) x≡) →
          ─ ((x , x₁) , x≡)

    @0 cₗ : _
    cₗ = proj₁ (proj₁ l≡∷)

    @0 cᵣ : _
    cᵣ = proj₂ (proj₁ l≡∷)

    line“ : Base64Str (l₁ ++ cₗ ∷ cᵣ)
    line“ = subst₀ Base64Str
              (l ≡⟨ l≡ ⟩
              l₁ ++ drop (length l₁) l ≡⟨ cong (l₁ ++_) (sym $ proj₂ l≡∷) ⟩
              l₁ ++ cₗ ∷ cᵣ ∎)
              line

    @0 cₗ∈ : cₗ ∈ B64.charset ⊎ cₗ ≡ '='
    cₗ∈ = Base64.Str.char∈ (Any.++⁺ʳ l₁ (here refl)) line“

    @0 bs≡“ : l₁ ++ e₁ ++ xs₁ ≡ l₁ ++ cₗ ∷ cᵣ ++ e
    bs≡“ = l₁ ++ e₁ ++ xs₁ ≡⟨ bs≡' ⟩
           l ++ e ≡⟨ cong (_++ e) l≡ ⟩
           (l₁ ++ drop (length l₁) l) ++ e ≡⟨ ++-assoc l₁ _ _ ⟩
           l₁ ++ drop (length l₁) l ++ e ≡⟨ cong (λ x → l₁ ++ x ++ e) (sym (proj₂ l≡∷)) ⟩
           l₁ ++ cₗ ∷ cᵣ ++ e ∎

    @0 bs≡ₗ : e₁ ++ xs₁ ≡ cₗ ∷ cᵣ ++ e
    bs≡ₗ = ++-cancelˡ l₁ bs≡“

    @0 cₗ≡ : cₗ ≡ '\r' ⊎ cₗ ≡ '\n'
    cₗ≡ = caseErased eol₁ ret (const _) of λ where
      crlf → ─ (inj₁ (sym (∷-injectiveˡ bs≡ₗ)))
      cr → ─ (inj₁ (sym (∷-injectiveˡ bs≡ₗ)))
      lf → ─ (inj₂ (sym (∷-injectiveˡ bs≡ₗ)))

    @0 cₗ∉ : cₗ ∉ B64.charset × cₗ ≢ '='
    cₗ∉ = caseErased cₗ≡ ret (const _) of λ where
      (inj₁ x) →
        ─   (subst₀ (_∉ B64.charset) (sym x) (toWitnessFalse{Q = _ ∈? _} tt)
          , subst₀ (_≢ '=') (sym x) (λ ()))
      (inj₂ y) →
        ─   (subst₀ (_∉ B64.charset) (sym y) (toWitnessFalse{Q = _ ∈? _} tt)
          , subst₀ (_≢ '=') (sym y) (λ ()))


  @0 l₁×≡ : l₁ ≡ l × e₁ ++ xs₁ ≡ e
  l₁×≡ = caseErased Nat.<-cmp (length l₁) (length l) ret (const _) of λ where
    (tri≈ _ len≡ _) → ─ (Lemmas.length-++-≡ _ _ _ _ bs≡' len≡)
    (tri< len< _ _) → ─ uncurry (contradiction₂ (Len<.cₗ∈ len<)) (Len<.cₗ∉ len<)
    (tri> _ _ len>) → {!!}

    -- Lemmas.length-++-≡ _ _ _ _ bs≡'
    --        (length l₁ ≡⟨ lineLen₁ ⟩
    --         64 ≡⟨ sym lineLen ⟩
    --         length l ∎)


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


