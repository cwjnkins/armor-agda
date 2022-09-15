{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.Base64
open import Aeres.Data.PEM.TCB
open import Aeres.Data.PEM.Properties
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Sum
import      Aeres.Grammar.Parser
open import Aeres.Prelude
import      Data.Nat.Properties as Nat
open import Tactic.MonoidSolver using (solve ; solve-macro)

open Aeres.Grammar.Definitions Char
open Aeres.Grammar.IList       Char
open Aeres.Grammar.Sum         Char
open Aeres.Grammar.Parser      Char

module Aeres.Data.PEM.Parser where

module parseRFC5234 where

  parseMaxEOL : LogDec.MaximalParser RFC5234.EOL
  parseMaxEOL =
    LogDec.equivalent EOL.equiv
      (parseMaxSum
        (LogDec.nonnesting (λ where _ refl refl → refl)
          (parseLit (tell "parseCRLF: EOF") silent _))
        (parseMaxSum
          (LogDec.nonnesting (λ where _ refl refl → refl)
            (parseLit (tell "parseCR: EOF") silent _))
            (LogDec.nonnesting (λ where _ refl refl → refl)
              (parseLit (tell "parseLF: EOF") silent _))))

open parseRFC5234 public
  using (parseMaxEOL)

module parseCertBoundary where

  parseCertBoundary : ∀ ctrl → LogDec.MaximalParser (CertBoundary ctrl)
  parseCertBoundary ctrl =
    LogDec.equivalent (CertBoundary.equiv ctrl)
      (LogDec.parse&₁
        (parseLit (tell "parseCertBoundary: EOF") silent _)
        (λ where _ refl refl → refl)
        (LogDec.parseErased parseRFC5234.parseMaxEOL))

open parseCertBoundary public
  using (parseCertBoundary)

module parseCertFullLine where

  parseCertFullLine : LogDec.MaximalParser CertFullLine
  parseCertFullLine =
    LogDec.equivalent CertFullLine.equiv
      (LogDec.parse&₁
        (parseIList (tell "parseCertFullLine: underflow") _
          Base64.Char.nonempty Base64.Char.nonnesting
          parseBase64Char _)
        exactLength-nonnesting
        parseMaxEOL)

open parseCertFullLine public
  using (parseCertFullLine)

module parseCertFinalLine where

  open ≡-Reasoning

  parseCertFinalLine : LogDec.MaximalParser CertFinalLine
  parseCertFinalLine =
    LogDec.equivalent CertFinalLine.equiv
      (LogDec.mkMaximalParser help)
    where
    help : ∀ xs → Σ _ _
    help xs =
      case LogDec.runMaximalParser
             (LogDec.parse& parseMaxBase64Str parseMaxEOL CertFinalLine.noOverlap) xs
      of λ where
        (mkLogged log (no ¬p) , max) →
          (mkLogged log (no λ where
            (success prefix read read≡ (mk×ₚ fstₚ₁ sndₚ₁ refl) suffix ps≡) →
              contradiction
                (success prefix _ read≡ fstₚ₁ suffix ps≡)
                ¬p))
          , tt
        (mkLogged log (yes (success pre₁ r₁ r₁≡ v₁@(mk&ₚ{bs₁}{bs₂} str eol refl) suf₁ ps≡₁)) , max₁) →
          let bs₁' : Singleton bs₁
              bs₁' = Base64.Str.serialize str
          in
          case inRange? 1 64 (length (↑ bs₁')) ret (const _) of λ where
            (no ¬p) →
              (mkLogged (log ++ ["parseMaxCertFinalLine: overrun"]) (no λ where
                (success prefix read read≡ (mk×ₚ v₁'@(mk&ₚ{bs₁'}{bs₂'} str' eol' refl) ir refl) suffix ps≡) → ‼
                  let
                    xs≡ : Erased (pre₁ ++ suf₁ ≡ prefix ++ suffix)
                    xs≡ = ─ (begin (pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
                                   xs ≡⟨ sym ps≡ ⟩
                                   prefix ++ suffix ∎))

                    xs≡' : Erased (bs₁ ++ bs₂ ++ suf₁ ≡ bs₁' ++ bs₂' ++ suffix)
                    xs≡' = ─ (begin
                      bs₁ ++ bs₂ ++ suf₁ ≡⟨ solve (++-monoid Char) ⟩
                      (bs₁ ++ bs₂) ++ suf₁ ≡⟨ ¡ xs≡ ⟩
                      (bs₁' ++ bs₂') ++ suffix ≡⟨ solve (++-monoid Char) ⟩
                      bs₁' ++ bs₂' ++ suffix ∎)

                    prefix≤ : Erased (length prefix ≤ r₁)
                    prefix≤ = ─ max₁ _ _ ps≡ v₁'

                    pre₁≡ : Erased (pre₁ ≡ prefix ++ drop (length prefix) pre₁)
                    pre₁≡ = ─ Lemmas.drop-length-≤ prefix suffix _ suf₁ (sym $ ¡ xs≡) (Nat.≤-trans (¡ prefix≤) (Lemmas.≡⇒≤ r₁≡))

                    bs₁'≡ : Erased (bs₁ ≡ bs₁' ++ drop (length bs₁') bs₁)
                    bs₁'≡ = ─ Lemmas.drop-length-≤ bs₁' (bs₂' ++ suffix) _ (bs₂ ++ suf₁)
                                (sym (¡ xs≡'))
                                (caseErased (Nat.<-cmp (length bs₁') (length bs₁)) ret (const _) of λ where
                                  (tri< bs₁'< _ _) → ─ Nat.<⇒≤{x = length bs₁'} bs₁'<
                                  (tri≈ _ bs₁'≡ _) → ─ Lemmas.≡⇒≤ bs₁'≡
                                  (tri> _ _ bs₁'>) →
                                    let bs₁'≡ : Erased (bs₁' ≡ bs₁ ++ drop (length bs₁) bs₁')
                                        bs₁'≡ = ─ (Lemmas.drop-length-≤ bs₁ (bs₂ ++ suf₁) _ (bs₂' ++ suffix) (¡ xs≡') (Nat.<⇒≤ bs₁'>))
                                    in
                                    ─ (caseErased CertFinalLine.noOverlap bs₁ (drop (length bs₁) bs₁') (bs₂' ++ suffix) bs₂ suf₁
                                         (++-cancelˡ bs₁ (begin
                                           bs₁ ++ drop (length bs₁) bs₁' ++ bs₂' ++ suffix ≡⟨ solve (++-monoid Char) ⟩
                                           (bs₁ ++ drop (length bs₁) bs₁') ++ bs₂' ++ suffix ≡⟨ cong (_++ _) (sym (¡ bs₁'≡)) ⟩
                                           bs₁' ++ bs₂' ++ suffix ≡⟨ (sym $ ¡ xs≡') ⟩
                                           bs₁ ++ bs₂ ++ suf₁ ∎))
                                         (subst Base64Str (¡ bs₁'≡) str') str
                                       ret (const _) of λ where
                                      (inj₁ x) → ─ contradiction
                                                     (begin (length bs₁ ≡⟨ cong length (sym $ ++-identityʳ bs₁) ⟩
                                                            length (bs₁ ++ []) ≡⟨ cong (λ x → length (bs₁ ++ x)) (sym x) ⟩
                                                            length (bs₁ ++ drop (length bs₁) bs₁') ≡⟨ cong length $ sym (¡ bs₁'≡) ⟩
                                                            length bs₁' ∎))
                                                     (Nat.<⇒≢ bs₁'>)
                                      (inj₂ y) → ─ contradiction eol y))
                  in
                  case
                    CertFinalLine.noOverlap _ _ (bs₂ ++ suf₁) bs₂' suffix
                      (++-cancelˡ bs₁' (begin
                        bs₁' ++ drop (length bs₁') bs₁ ++ bs₂ ++ suf₁ ≡⟨ solve (++-monoid Char) ⟩
                        (bs₁' ++ drop (length bs₁') bs₁) ++ bs₂ ++ suf₁ ≡⟨ cong (_++ _) (sym (¡ bs₁'≡)) ⟩
                        bs₁ ++ bs₂ ++ suf₁ ≡⟨ ¡ xs≡' ⟩
                        bs₁' ++ bs₂' ++ suffix ∎))
                      (subst Base64Str (¡ bs₁'≡) str) str'
                  ret (const _) of λ where
                    (inj₁ x) → contradiction
                                 (subst (InRange 1 64 ∘ length)
                                   (bs₁' ≡ ↑ Base64.Str.serialize str ∋ (begin
                                     (bs₁' ≡⟨ sym (++-identityʳ bs₁') ⟩
                                     bs₁' ++ [] ≡⟨ cong (bs₁' ++_) (sym x) ⟩
                                     bs₁' ++ drop (length bs₁') bs₁ ≡⟨ sym (¡ bs₁'≡) ⟩
                                     bs₁ ≡⟨ (sym ∘ Singleton.x≡ ∘ Base64.Str.serialize $ str) ⟩
                                     ↑ Base64.Str.serialize str ∎)))
                                   (¡ ir))
                                 ¬p
                    (inj₂ y) → contradiction eol' y))
              , tt
            (yes p) →
              let ir : Erased (InRange 1 64 (length bs₁))
                  ir = ─ subst (InRange 1 64 ∘ length) (Singleton.x≡ bs₁') p
              in
              (mkLogged log (yes
                (success pre₁ _ r₁≡ (mk×ₚ v₁ ir refl) suf₁ ps≡₁)))
              , λ where
                pre' suf' ps≡' (mk×ₚ{.pre'} v' _ refl) →
                  max₁ _ _ ps≡' v'

module parseCertText where
  
  parseMaxCertText : LogDec.MaximalParser CertText
  parseMaxCertText = LogDec.mkMaximalParser help
    where
    help : ∀ xs → Σ _ _
    help xs =
      case LogDec.runMaximalParser (parseIListMax (mkLogged ["parseCertMaxText: underflow"] tt) _ CertFullLine.nonempty {!!} {!!}) {!!} ret (const _) of λ where
        x → {!!}
-- module parsePEM where

