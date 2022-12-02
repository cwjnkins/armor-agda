{-# OPTIONS --subtyping #-}

open import Aeres.Data.Base64
open import Aeres.Data.PEM.CertText.Exclusions
open import Aeres.Data.PEM.CertText.FinalLine
open import Aeres.Data.PEM.CertText.FullLine
open import Aeres.Data.PEM.CertText.Properties
open import Aeres.Data.PEM.CertText.TCB
open import Aeres.Data.PEM.RFC5234
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Relation.Definitions
open import Aeres.Prelude
import      Data.Nat.Properties as Nat
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.PEM.CertText.Parser where

open Aeres.Grammar.Definitions          Char
open Aeres.Grammar.IList                Char
open Aeres.Grammar.Parser               Char
open Aeres.Grammar.Relation.Definitions Char

open ≡-Reasoning
module ≤ = Nat.≤-Reasoning

parseMaxCertText : LogDec.MaximalParser CertText
parseMaxCertText = LogDec.mkMaximalParser help
  where
  help : ∀ xs → Σ _ _
  help xs =
    case LogDec.runMaximalParser
           (parseIListMaxNoOverlap.parseIListMax
             (mkLogged [ "parseMaxCertText: underflow" ] tt)
             _ FullLine.nonempty FullLine.nooverlap parseCertFullLine)
           xs
      ret (const _) of λ where
      (mkLogged _ (no ¬p) , _) →
        contradiction (success _ _ refl nil _ refl) ¬p
      (mkLogged log₁ (yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁)) , max₁) →
        case LogDec.runMaximalParser parseCertFinalLine suf₁ of λ where
          (mkLogged log₂ (yes (success pre₂ r₂ r₂≡ v₂ suf₂ ps≡₂)) , max₂) →
            let
              r₁+r₂≡ : Erased (r₁ + r₂ ≡ length pre₁ + length pre₂)
              r₁+r₂≡ = ─ cong₂ _+_ r₁≡ r₂≡
            in
            mkLogged (log₁ ++ log₂)
              (yes
                (success (pre₁ ++ pre₂) (r₁ + r₂)
                  (trans (¡ r₁+r₂≡) (sym (length-++ pre₁)))
                  (mkCertText v₁ v₂ refl) suf₂
                  ((pre₁ ++ pre₂) ++ suf₂ ≡⟨ ++-assoc pre₁ _ _ ⟩
                  pre₁ ++ pre₂ ++ suf₂ ≡⟨ cong (pre₁ ++_) ps≡₂ ⟩
                  pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
                  xs ∎)))
            , λ where
              pre' suf' ps≡' (mkCertText{b}{f} body final bs≡) →
                let xs≡ : Erased (b ++ f ++ suf' ≡ pre₁ ++ pre₂ ++ suf₂)
                    xs≡ = ─ (begin (b ++ f ++ suf' ≡⟨ solve (++-monoid Char) ⟩
                                   (b ++ f) ++ suf' ≡⟨ (cong (_++ suf') ∘ sym $ bs≡) ⟩
                                   pre' ++ suf' ≡⟨ ps≡' ⟩
                                   xs ≡⟨ sym ps≡₁ ⟩
                                   pre₁ ++ suf₁ ≡⟨ cong (pre₁ ++_) (sym ps≡₂) ⟩
                                   pre₁ ++ pre₂ ++ suf₂ ∎))
                in
                  uneraseDec
                    (caseErased (Nat.<-cmp (length b) r₁) ret (const _) of λ where
                      (tri> b₁≮ _ b₁>) → ─
                        (contradiction b₁> (Nat.≤⇒≯
                          (max₁ _ (f ++ suf')
                            (begin (b ++ f ++ suf' ≡⟨ solve (++-monoid Char) ⟩
                                   (b ++ f) ++ suf' ≡⟨ cong (_++ suf') (sym bs≡) ⟩
                                   pre' ++ suf' ≡⟨ ps≡' ⟩
                                   xs ∎))
                            body)))
                      (tri≈ _ b≡ _) →
                        let pre₁≡ : Erased (pre₁ ≡ b)
                            pre₁≡ = ─ proj₁ (Lemmas.length-++-≡ _ (pre₂ ++ suf₂) _ (f ++ suf')
                                               (sym (¡ xs≡) )
                                               (trans (sym r₁≡) (sym b≡)))
                        in
                        ─ (Nat.≤-Reasoning.begin length pre' Nat.≤-Reasoning.≡⟨ cong length bs≡ ⟩
                                                 length (b ++ f) Nat.≤-Reasoning.≡⟨ length-++ b ⟩
                                                 length b + length f
                                                   Nat.≤-Reasoning.≤⟨
                                                     Nat.+-mono-≤ (Lemmas.≡⇒≤ b≡)
                                                       (max₂ _ suf'
                                                         (Lemmas.++-cancel≡ˡ _ _
                                                           (sym (¡ pre₁≡)) (trans (¡ xs≡) (cong (pre₁ ++_) ps≡₂)))
                                                         final)
                                                   ⟩
                                                 r₁ + r₂ Nat.≤-Reasoning.∎)
                      (tri< b< _ _) → ─
                        (≤.begin
                          (length pre' ≤.≡⟨ cong length bs≡ ⟩
                          length (b ++ f) ≤.≡⟨ length-++ b ⟩
                          length b + length f
                            ≤.≤⟨
                              body< body final v₁ v₂ (¡ xs≡) (Nat.≤-trans b< (Lemmas.≡⇒≤ r₁≡))
                            ⟩
                          length pre₁ + length pre₂ ≤.≡⟨ sym (¡ r₁+r₂≡) ⟩
                          r₁ + r₂ ≤.∎))

                    )
                    (_ ≤? _)
          (mkLogged log₂ (no ¬p) , snd) →
            case finalLineFromLines v₁ ret (const _) of λ where
              (inj₁ (─ refl)) →
                  (mkLogged (log₁ ++ log₂) (no (λ where
                    (success prefix read read≡ (mkCertText{b}{f} body final refl) suffix ps≡) →
                      let
                        b≡[] : Erased (b ≡ [])
                        b≡[] = ─
                          (caseErased
                            _,_{A = List Char}{B = (_≡ 0) ∘ length} b
                              (Nat.n≤0⇒n≡0
                                (Nat.≤-trans
                                  (max₁ b (f ++ suffix) (trans (sym (++-assoc b f suffix)) ps≡) body)
                                  (Lemmas.≡⇒≤ r₁≡)))
                           ret ((_≡ []) ∘ proj₁) of λ where
                          ([] , snd) → ─ refl)
                      in
                      contradiction
                        (success _ _ refl final suffix
                          (Lemmas.++-cancel≡ˡ _ _ (¡ b≡[])
                            (b ++ f ++ suffix ≡⟨ solve (++-monoid Char) ⟩
                            (b ++ f) ++ suffix ≡⟨ ps≡ ⟩
                            xs ≡⟨ sym ps≡₁ ⟩
                            suf₁ ∎)))
                        ¬p)))
                , tt
              (inj₂ (mk&ₚ fstₚ₁ sndₚ₁ bs≡)) →
                  mkLogged [] (yes
                    (success pre₁ _ r₁≡ (mkCertText fstₚ₁ sndₚ₁ bs≡) suf₁ ps≡₁))
                , λ where
                  pre' suf' ps≡' (mkCertText{b}{f} body final bs≡) →
                    let
                      bs≡' = ─
                        (b ++ f ++ suf' ≡⟨ solve (++-monoid Char) ⟩
                         (b ++ f) ++ suf' ≡⟨ cong (_++ suf') (sym bs≡) ⟩
                         pre' ++ suf' ≡⟨ ps≡' ⟩
                         xs ∎)

                      b≤ : Erased (length b ≤ length pre₁)
                      b≤ = ─ Nat.≤-trans
                             (max₁ _ _ (¡ bs≡') body)
                             (Lemmas.≡⇒≤ r₁≡)
                    in
                    {!!}
