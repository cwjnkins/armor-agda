{-# OPTIONS --subtyping --allow-unsolved-metas #-}

open import Aeres.Binary
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Relation.Definitions
import      Aeres.Grammar.Sum
open import Aeres.Prelude
open import Aeres.Data.Base64
import      Aeres.Data.PEM.TCB as PEM
import      Data.Nat.Properties as Nat
open import Tactic.MonoidSolver using (solve ; solve-macro)

open Aeres.Grammar.Definitions          Char
open Aeres.Grammar.IList                Char
open Aeres.Grammar.Relation.Definitions Char
open Aeres.Grammar.Sum                  Char

module Aeres.Data.PEM.Properties where

module EOL where
  Rep =  Sum (_≡ '\r' ∷ [ '\n' ])
        (Sum (_≡ [ '\r' ])
             (_≡ [ '\n' ]))

  equiv : Equivalent Rep PEM.RFC5234.EOL
  proj₁ equiv (Sum.inj₁ refl) = PEM.RFC5234.crlf
  proj₁ equiv (Sum.inj₂ (Sum.inj₁ refl)) = PEM.RFC5234.cr
  proj₁ equiv (Sum.inj₂ (Sum.inj₂ refl)) = PEM.RFC5234.lf
  proj₂ equiv PEM.RFC5234.crlf = Sum.inj₁ refl
  proj₂ equiv PEM.RFC5234.cr = Sum.inj₂ (Sum.inj₁ refl)
  proj₂ equiv PEM.RFC5234.lf = Sum.inj₂ (Sum.inj₂ refl)

  postulate
    -- Joy
    @0 eolLen : ∀ {@0 bs} → PEM.RFC5234.EOL bs → InRange 1 2 (length bs)

    -- Christa
    noOverlap : NoOverlap Base64Str PEM.RFC5234.EOL

module CertBoundary where
  Rep : (ctrl : String) → @0 List Char → Set
  Rep ctrl = &ₚ (_≡ (String.toList $ "-----" String.++ ctrl String.++ " CERTIFICATE-----"))
                (Erased ∘ PEM.RFC5234.EOL)

  equiv : ∀ ctrl → Equivalent (Rep ctrl) (PEM.CertBoundary ctrl)
  proj₁ (equiv ctrl) (mk&ₚ refl (─ sndₚ₁) bs≡) = PEM.mkCertBoundary self sndₚ₁ bs≡
  proj₂ (equiv ctrl) (PEM.mkCertBoundary self eol bs≡) = mk&ₚ refl (─ eol) bs≡

module CertFullLine where
  Rep = &ₚ (ExactLength (IList Base64Char) 64) PEM.RFC5234.EOL

  equiv : Equivalent Rep PEM.CertFullLine
  proj₁ equiv (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = PEM.mkCertFullLine fstₚ₁ sndₚ₁ bs≡
  proj₂ equiv (PEM.mkCertFullLine line eol bs≡) = mk&ₚ line eol bs≡

  postulate
    nonempty   : NonEmpty PEM.CertFullLine
    nooverlap  : NoOverlap PEM.CertFullLine PEM.CertFullLine
    @0 fullLineLen : ∀ {@0 bs} → PEM.CertFullLine bs → InRange 65 65 (length bs)

module CertFinalLine where

  Rep : @0 List Char → Set
  Rep = Σₚ (&ₚ Base64Str PEM.RFC5234.EOL)
           (λ _ → Erased ∘ InRange 1 64 ∘ length ∘ &ₚᵈ.bs₁ )

  postulate
    equiv : Equivalent Rep PEM.CertFinalLine
    fromCertFullLine : ∀ {@0 bs} → PEM.CertFullLine bs → PEM.CertFinalLine bs
    lengthRange : ∀ {@0 bs} → PEM.CertFinalLine bs → InRange 2 66 (length bs)

module CertText where
  open ≡-Reasoning

  postulate
    noOverlapLines  : NoOverlap PEM.CertFullLine PEM.CertFinalLine
    noOverlapLemma₁ : NoOverlap PEM.CertFinalLine (&ₚ (IList PEM.CertFullLine) PEM.CertFinalLine)


  finalLineFromLines : ∀ {@0 bs} → IList PEM.CertFullLine bs → bs ≡ [] ⊎ &ₚ (IList PEM.CertFullLine) PEM.CertFinalLine bs
  finalLineFromLines nil = inj₁ refl
  finalLineFromLines (consIList{bs₁}{.[]} head₁ nil bs≡) =
    inj₂ (mk&ₚ nil (CertFinalLine.fromCertFullLine head₁)
            (begin (_ ≡⟨ bs≡ ⟩
                   bs₁ ++ [] ≡⟨ ++-identityʳ bs₁ ⟩
                   bs₁ ∎)))
  finalLineFromLines (consIList{bs₁}{bs₂} head₁ tail₁@(consIList{bs₁ = bs₃} head₂ tail₂ bs≡₂) bs≡₁) =
    case finalLineFromLines tail₁ ret (const _) of λ where
      (inj₁ refl) →
        contradiction{P = bs₃ ≡ []} (++-conicalˡ bs₃ _ (sym bs≡₂)) (CertFullLine.nonempty head₂)
      (inj₂ (mk&ₚ{bs₅}{bs₆} fstₚ₁ sndₚ₁ refl)) →
        inj₂ (mk&ₚ (consIList head₁ fstₚ₁ refl) sndₚ₁
                      (begin _ ≡⟨ bs≡₁ ⟩
                             bs₁ ++ bs₅ ++ bs₆ ≡⟨ sym (++-assoc bs₁ bs₅ _) ⟩
                             (bs₁ ++ bs₅) ++ bs₆ ∎))

  {-# TERMINATING #-}
  @0 body< : ∀ {@0 b₁ f₁ b₂ f₂ suf₁ suf₂}
          → IList PEM.CertFullLine b₁ → PEM.CertFinalLine f₁
          → IList PEM.CertFullLine b₂ → PEM.CertFinalLine f₂
          → b₁ ++ f₁ ++ suf₁ ≡ b₂ ++ f₂ ++ suf₂
          → length b₁ < length b₂
          → length b₁ + length f₁ ≤ length b₂ + length f₂
  body<{f₂ = f₂} nil (PEM.mkCertFinalLine{l₁}{e₁} lineₗ lineLenₗ eolₗ refl) (consIList{bs₂ = bs₂} fullL@(PEM.mkCertFullLine{l}{e} (mk×ₚ line line≡ refl) eol refl) tail₁ refl) fin₂ ++≡ b₁< =
    ≤.begin
      length (l₁ ++ e₁) ≤.≡⟨ length-++ l₁ ⟩
      length l₁ + length e₁ ≤.≤⟨ Nat.+-mono-≤ (proj₂ lineLenₗ) (proj₂ $ EOL.eolLen eolₗ) ⟩
      64 + 2 ≤.≤⟨ toWitness{Q = _ ≤? _} tt ⟩
      65 + 2 ≤.≤⟨ Nat.+-mono-≤ (proj₁ (CertFullLine.fullLineLen fullL)) (proj₁ $ CertFinalLine.lengthRange fin₂ ) ⟩
      length (l ++ e) + length f₂ ≤.≤⟨ Nat.+-monoˡ-≤ (length f₂) (Nat.m≤m+n (length (l ++ e)) (length bs₂)) ⟩
      (length (l ++ e) + length bs₂) + length f₂ ≤.≡⟨ cong (_+ length f₂) (sym (length-++ (l ++ e))) ⟩
      (length ((l ++ e) ++ bs₂)) + length f₂ ≤.∎ 
    where module ≤ = Nat.≤-Reasoning
  body<{f₁ = f₁}{f₂ = f₂}{suf₁}{suf₂} (consIList{bs₁} head₁ nil refl) fin₁ (consIList{bs₂} head₂ nil refl) fin₂ ++≡ b₁< =
    let b₁<' : length bs₁ < length bs₂
        b₁<' = subst₂ (λ x y → length x < length y) (++-identityʳ bs₁) (++-identityʳ bs₂) b₁<

        bs₂≡ : Erased (bs₂ ≡ bs₁ ++ drop (length bs₁) bs₂)
        bs₂≡ = ─ Lemmas.drop-length-≤ bs₁ (f₁ ++ suf₁) _ _ xs≡ (Nat.<⇒≤ b₁<')
    in
    caseErased noOverlapLines bs₁ (drop (length bs₁) bs₂) (f₂ ++ suf₂) f₁ suf₁
                 (++-cancelˡ bs₁ (begin
                   (bs₁ ++ (drop (length bs₁) bs₂) ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
                   (bs₁ ++ drop (length bs₁) bs₂) ++ f₂ ++ suf₂ ≡⟨ cong (_++ f₂ ++ suf₂) (sym (¡ bs₂≡)) ⟩
                   bs₂ ++ f₂ ++ suf₂ ≡⟨ sym xs≡ ⟩
                   bs₁ ++ f₁ ++ suf₁ ∎)))
                 (subst PEM.CertFullLine (¡ bs₂≡) head₂) head₁
    ret (const _) of λ where
      (inj₁ x) →
        ─ contradiction
            (begin (length bs₁ ≡⟨ cong length (sym (++-identityʳ bs₁)) ⟩
                   length (bs₁ ++ []) ≡⟨ cong (length ∘ (bs₁ ++_)) (sym x) ⟩
                   length (bs₁ ++ drop (length bs₁) bs₂) ≡⟨ cong length (sym (¡ bs₂≡)) ⟩
                   length bs₂ ∎))
            (Nat.<⇒≢ b₁<')
      (inj₂ y) → ─ contradiction fin₁ y
    where
    xs≡ : bs₁ ++ f₁ ++ suf₁ ≡ bs₂ ++ f₂ ++ suf₂
    xs≡ = begin (bs₁ ++ f₁ ++ suf₁ ≡⟨ solve (++-monoid Char) ⟩
                (bs₁ ++ []) ++ f₁ ++ suf₁ ≡⟨ ++≡ ⟩
                (bs₂ ++ []) ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
                bs₂ ++ f₂ ++ suf₂ ∎)
  body<{f₁ = f₁}{f₂ = f₂}{suf₁}{suf₂} (consIList{bs₁} head₁ nil refl) fin₁ (consIList{bs₂} head₂ (consIList{bs₃}{bs₄} head₃ tail₃ refl) refl) fin₂ ++≡ b₁< =
    caseErased Nat.<-cmp (length bs₁) (length bs₂) ret (const _) of λ where
      (tri< bs₁< bs₁≢ _) → {!!}
      (tri> _ bs₁≢ bs₁>) → {!!}
      (tri≈ _ bs₁≡ _) → ─
        (let bs₂≡ : bs₁ ≡ bs₂
             bs₂≡ = proj₁ (Lemmas.length-++-≡ _ _ _ _ xs≡ bs₁≡)

             xs≡' : f₁ ++ suf₁ ≡ bs₃ ++ bs₄ ++ f₂ ++ suf₂
             xs≡' = Lemmas.++-cancel≡ˡ _ _ bs₂≡ xs≡

             f₁≤ : length f₁ ≤ length bs₃
             f₁≤ = caseErased Nat.<-cmp (length f₁) (length bs₃) ret (const _) of λ where
               (tri< f₁< _ _) → ─ (Nat.<⇒≤ f₁<)
               (tri≈ _ f₁≡ _) → ─ (Lemmas.≡⇒≤ f₁≡)
               (tri> _ _ f₁>) → ─
                 (let f₁≡ : f₁ ≡ bs₃ ++ drop (length bs₃) f₁
                      f₁≡ = Lemmas.drop-length-≤ bs₃ (bs₄ ++ f₂ ++ suf₂) _ _ (sym xs≡') (Nat.<⇒≤ f₁>)
                  in
                  caseErased noOverlapLemma₁ bs₃ (drop (length bs₃) f₁) suf₁ (bs₄ ++ f₂) suf₂
                               {!!}
                               (subst PEM.CertFinalLine f₁≡ fin₁) (CertFinalLine.fromCertFullLine head₃)
                  ret (const _) of λ where
                    (inj₁ x) → ─ contradiction{P = f₁ ≡ bs₃} {!!} λ where refl → ‼ Nat.<⇒≢ f₁> refl
                    (inj₂ y) → ─ contradiction (mk&ₚ tail₃ fin₂ refl) y)
             -- f₁≡ : f₁ ≡ bs₃
             -- f₁≡ = caseErased Nat.<-cmp (length f₁) (length bs₃) ret (const _) of λ where
             --         (tri< f₁< f₁≢ _) → ─
             --           (let bs₃≡ : bs₃ ≡ f₁ ++ drop (length f₁) bs₃
             --                bs₃≡ = Lemmas.drop-length-≤ f₁ suf₁ _ _ xs≡' (Nat.<⇒≤ f₁<)
             --            in
             --            caseErased noOverlapLemma₁ f₁ (drop (length f₁) bs₃) (bs₄ ++ f₂ ++ suf₂) {!!} {!!}
             --                         {!!}
             --                         (subst PEM.CertFinalLine bs₃≡ (CertFinalLine.fromCertFullLine head₃)) fin₁
             --            ret (const _) of λ where
             --              x → {!!}
             --           )
             --         (tri> _ f₁≢ f₁>) → {!!}
             --         (tri≈ _ f₁≡ _) → ─ proj₁ (Lemmas.length-++-≡ _ _ _ _ xs≡' f₁≡)
         in
         ≤.begin (length (bs₁ ++ []) + length f₁ ≤.≡⟨ cong (λ x → length x + length f₁) (++-identityʳ bs₁) ⟩
                 length bs₁ + length f₁ ≤.≡⟨ cong (λ x → length x + length f₁) bs₂≡ ⟩
                 length bs₂ + length f₁ ≤.≡⟨ {!!} ⟩
                 {!!})
         )

    where
    module ≤ = Nat.≤-Reasoning

    xs≡ : bs₁ ++ f₁ ++ suf₁ ≡ bs₂ ++ bs₃ ++ bs₄ ++ f₂ ++ suf₂
    xs≡ = begin (bs₁ ++ f₁ ++ suf₁ ≡⟨ solve (++-monoid Char) ⟩
                (bs₁ ++ []) ++ f₁ ++ suf₁ ≡⟨ ++≡ ⟩
                (bs₂ ++ bs₃ ++ bs₄) ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
                bs₂ ++ bs₃ ++ bs₄ ++ f₂ ++ suf₂ ∎)
  body< (Aeres.Grammar.IList.cons (Aeres.Grammar.IList.mkIListCons {_} {_} head₁ (Aeres.Grammar.IList.cons x) refl)) fin₁ (Aeres.Grammar.IList.cons (Aeres.Grammar.IList.mkIListCons {_} {_} head₂ Aeres.Grammar.IList.nil refl)) fin₂ ++≡ b₁< = {!!}
  body<{f₁ = f₁}{f₂ = f₂}{suf₁}{suf₂} (consIList{bs₁} head₁ tail₁@(consIList{bs₂}{bs₃} head₂ tail₂ refl) refl) fin₁ (consIList{bs₄} head₃ tail₃@(consIList{bs₅}{bs₆} head₄ tail₄ refl) refl) fin₂ ++≡ b₁< =
    caseErased Nat.<-cmp (length bs₁) (length bs₄) ret (const _) of λ where
      (tri< bs₁< bs₁≢ _) → ─
        (let bs₄≡ : bs₄ ≡ bs₁ ++ drop (length bs₁) bs₄
             bs₄≡ = Lemmas.drop-length-≤ bs₁ _ _ _ xs≡ (Nat.<⇒≤ bs₁<)
         in
         case CertFullLine.nooverlap bs₁ (drop (length bs₁) bs₄) (bs₅ ++ bs₆ ++ f₂ ++ suf₂) bs₂ (bs₃ ++ f₁ ++ suf₁)
                (++-cancelˡ bs₁
                  (begin (bs₁ ++ drop (length bs₁) bs₄ ++ bs₅ ++ bs₆ ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
                         (bs₁ ++ drop (length bs₁) bs₄) ++ bs₅ ++ bs₆ ++ f₂ ++ suf₂ ≡⟨ (cong (_++ _) ∘ sym $ bs₄≡) ⟩
                         bs₄ ++ bs₅ ++ bs₆ ++ f₂ ++ suf₂ ≡⟨ sym xs≡ ⟩
                         _ ∎)))
                (subst PEM.CertFullLine bs₄≡ head₃) head₁
         ret (const _) of λ where
          (inj₁ x) → contradiction{P = length bs₄ ≡ length bs₁}
                       (begin
                         length bs₄ ≡⟨ cong length bs₄≡ ⟩
                         length (bs₁ ++ drop (length bs₁) bs₄) ≡⟨ cong (length ∘ (bs₁ ++_)) x ⟩
                         length (bs₁ ++ []) ≡⟨ cong length (++-identityʳ bs₁) ⟩
                         length bs₁ ∎) 
                       (Nat.>⇒≢ bs₁<)
          (inj₂ y) → contradiction head₂ y)
      (tri> _ bs₁≢ bs₁>) → ─
        (let bs₁≡' : bs₁ ≡ bs₄ ++ drop (length bs₄) bs₁
             bs₁≡' = Lemmas.drop-length-≤ bs₄ _ _ _ (sym xs≡) (Nat.<⇒≤ bs₁>)
         in
         case CertFullLine.nooverlap bs₄ (drop (length bs₄) bs₁) (bs₂ ++ bs₃ ++ f₁ ++ suf₁) bs₅ (bs₆ ++ f₂ ++ suf₂)
                (++-cancelˡ bs₄
                  (begin (bs₄ ++ drop (length bs₄) bs₁ ++ bs₂ ++ bs₃ ++ f₁ ++ suf₁ ≡⟨ solve (++-monoid Char) ⟩
                         (bs₄ ++ drop (length bs₄) bs₁) ++ bs₂ ++ bs₃ ++ f₁ ++ suf₁ ≡⟨ cong (_++ _) (sym bs₁≡') ⟩
                         bs₁ ++ bs₂ ++ bs₃ ++ f₁ ++ suf₁  ≡⟨ xs≡ ⟩
                         _ ∎)))
                (subst PEM.CertFullLine bs₁≡' head₁) head₃
         ret (const _) of λ where
           (inj₁ x) →
             contradiction{P = length bs₁ ≡ length bs₄}
               (begin (length bs₁ ≡⟨ cong length bs₁≡' ⟩
                      length (bs₄ ++ drop (length bs₄) bs₁) ≡⟨ cong (length ∘ (bs₄ ++_)) x ⟩
                      length (bs₄ ++ []) ≡⟨ cong length (++-identityʳ bs₄) ⟩
                      length bs₄ ∎))
               bs₁≢
           (inj₂ y) → contradiction head₄ y
        )
      (tri≈ _ len≡ _) →
        ─ (≤.begin (length (bs₁ ++ bs₂ ++ bs₃) + length f₁ ≤.≡⟨ cong (_+ length f₁) (length-++ bs₁) ⟩
                   length bs₁ + length (bs₂ ++ bs₃) + length f₁ ≤.≡⟨ Nat.+-assoc (length bs₁) (length (bs₂ ++ bs₃)) (length f₁) ⟩
                   length bs₁ + (length (bs₂ ++ bs₃) + length f₁) ≤.≤⟨ Nat.+-monoʳ-≤ (length bs₁) (rec len≡) ⟩
                   length bs₁ + (length (bs₅ ++ bs₆) + length f₂) ≤.≡⟨ cong (_+ _) len≡ ⟩
                   length bs₄ + (length (bs₅ ++ bs₆) + length f₂) ≤.≡⟨ sym (Nat.+-assoc (length bs₄) _ _) ⟩
                   length bs₄ + length (bs₅ ++ bs₆) + length f₂ ≤.≡⟨ cong (_+ length f₂) (sym (length-++ bs₄)) ⟩
                   length (bs₄ ++ bs₅ ++ bs₆) + length f₂ ≤.∎))
    where
    module ≤ = Nat.≤-Reasoning

    xs≡ : bs₁ ++ bs₂ ++ bs₃ ++ f₁ ++ suf₁ ≡ bs₄ ++ bs₅ ++ bs₆ ++ f₂ ++ suf₂
    xs≡ = begin bs₁ ++ bs₂ ++ bs₃ ++ f₁ ++ suf₁ ≡⟨ solve (++-monoid Char) ⟩
                (bs₁ ++ bs₂ ++ bs₃) ++ f₁ ++ suf₁ ≡⟨ ++≡ ⟩
                (bs₄ ++ bs₅ ++ bs₆) ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
                bs₄ ++ bs₅ ++ bs₆ ++ f₂ ++ suf₂ ∎

    module _ (@0 len≡ : length bs₁ ≡ length bs₄) where
      bs₁≡ : Erased (bs₁ ≡ bs₄)
      bs₁≡ = ─ proj₁ (Lemmas.length-++-≡ _ _ _ _ xs≡ len≡)

      rec : (length (bs₂ ++ bs₃) + length f₁ ≤ length (bs₅ ++ bs₆) + length f₂)
      rec = body<{suf₁ = suf₁}{suf₂} tail₁ fin₁ tail₃ fin₂
                 (Lemmas.++-cancel≡ˡ _ _ (¡ bs₁≡)
                   (begin (bs₁ ++ (bs₂ ++ bs₃) ++ f₁ ++ suf₁ ≡⟨ solve (++-monoid Char) ⟩
                          bs₁ ++ bs₂ ++ bs₃ ++ f₁ ++ suf₁ ≡⟨ xs≡ ⟩
                          bs₄ ++ bs₅ ++ bs₆ ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
                          bs₄ ++ (bs₅ ++ bs₆) ++ f₂ ++ suf₂ ∎)))
                 (Nat.+-cancelˡ-< (length bs₁)
                   (≤.begin
                     (1 + length bs₁ + length (bs₂ ++ bs₃) ≤.≡⟨ cong (1 +_) (sym (length-++ bs₁)) ⟩
                     1 + length (bs₁ ++ bs₂ ++ bs₃) ≤.≤⟨ b₁< ⟩
                     length (bs₄ ++ bs₅ ++ bs₆) ≤.≡⟨ length-++ bs₄ ⟩
                     length bs₄ + length (bs₅ ++ bs₆) ≤.≡⟨ cong (_+ length (bs₅ ++ bs₆)) (cong length (sym (¡ bs₁≡))) ⟩
                     length bs₁ + length (bs₅ ++ bs₆) ≤.∎)))      

