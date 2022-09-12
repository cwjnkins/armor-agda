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

-- module parsePEM where

--   hereLine = "parseCertLine"

--   parseCertBoundary : ∀ ctrl → LogDec.MaximalParser (CertBoundary ctrl)
--   parseCertBoundary ctrl =
--     LogDec.equivalent (CertBoundary.equiv ctrl)
--       (LogDec.parse&₁
--         (parseLit
--           (tell "parseCertBoundary: underflow")
--           (tell "parseCertBoudnary: mismatch")
--           _)
--         (λ where _ refl refl → refl)
--         (LogDec.parseErased parseRFC5234.parseEOL))

--   parseCertHeader = parseCertBoundary "BEGIN"
--   parseCertFooter = parseCertBoundary "END"

--   parseCertFullLine : LogDec.MaximalParser CertFullLine
--   parseCertFullLine =
--     LogDec.equivalent CertFullLine.equiv
--       (LogDec.parse&₁
--         (parseIList (tell "parseCertFullLine: underflow") Base64Char Base64.Char.nonempty
--           Base64.Char.nonnesting parseBase64Char _)
--         exactLength-nonnesting
--         parseRFC5234.parseEOL)

--   parseCertFinalLine : LogDec.MaximalParser CertFinalLine
--   parseCertFinalLine = LogDec.mkMaximalParser help
--     where
--     open ≡-Reasoning

--     help : ∀ xs → Σ (Logging ∘ Dec $ Success CertFinalLine xs) _
--     help xs =
--       let p₁ : Dec $ Success (ParseWhileₜ λ x → Base64Char [ x ]) xs
--           p₁ = runParser (parseWhileₜ (base64Char? ∘ [_])) xs
--       in
--       case p₁ of λ where
--         (no ¬p) →
--           (mkLogged [ "parseCertFinalLine: underflow" ]
--             (no λ where
--               (success ._ read read≡ (mkCertFinalLine{e = e} (mk64Str{s}{p = p} str strLen (pad0 refl) refl) lineLen eol refl) suffix ps≡) → ‼
--                 let f : ∀ {@0 e} → RFC5234.EOL e → ∃₂ λ c e' → e ≡ c ∷ e'
--                     f = λ where
--                       RFC5234.crlf → _ , _ , refl
--                       RFC5234.cr → _ , _ , refl
--                       RFC5234.lf → _ , _ , refl

--                     @0 e≡ : ∃₂ λ c e' → e ≡ c ∷ e'
--                     e≡ = case eol of f

--                     @0 c : _
--                     c = proj₁ e≡

--                     @0 e' : _
--                     e' = proj₁ (proj₂ e≡)

--                     c∉64 : ¬ Base64Char [ c ]
--                     c∉64 = case eol ret (λ x → ¬ Base64Char [ proj₁ (f x) ]) of λ where
--                       RFC5234.crlf → λ { (mk64 c c∈ i refl) → contradiction c∈ (toWitnessFalse{Q = '\r' ∈? _} tt)}
--                       RFC5234.cr → λ { (mk64 c c∈ i refl) → contradiction c∈ (toWitnessFalse{Q = _ ∈? _} tt)}
--                       RFC5234.lf → λ { (mk64 c c∈ i refl) → contradiction c∈ (toWitnessFalse{Q = _ ∈? _} tt)}
--                 in
--                 contradiction
--                   (success (s ∷ʳ c) _ refl
--                     (mkParseWhile _ c (Base64.Char.iList2All str) c∉64 refl)
--                     (e' ++ suffix)
--                     (begin (s ++ [ c ]) ++ e' ++ suffix   ≡⟨ sym (++-assoc (s ++ [ c ]) e' suffix) ⟩
--                            ((s ++ [ c ]) ++ e') ++ suffix ≡⟨ cong (_++ suffix) (++-assoc s [ c ] e') ⟩
--                            (s ++ [ c ] ++ e') ++ suffix   ≡⟨ ++-assoc s ([ c ] ++ e') suffix ⟩
--                            s ++ ([ c ] ++ e') ++ suffix   ≡⟨ cong (λ x → s ++ x ++ suffix) (sym $ proj₂ (proj₂ e≡)) ⟩
--                            s ++ e ++ suffix               ≡⟨ solve (++-monoid Char) ⟩
--                            (s ++ e) ++ suffix             ≡⟨ cong (λ x → (x ++ e) ++ suffix) (sym (++-identityʳ s)) ⟩
--                            ((s ++ []) ++ e) ++ suffix     ≡⟨ ps≡ ⟩
--                            xs                             ∎))
--                   ¬p
--               (success ._ read read≡ (mkCertFinalLine{e = e} (mk64Str{s}{p = p} str strLen (pad1 (mk64P1{b₁}{b₂}{b₃} c₁@(mk64 ._ b₁∈ _ refl) c₂@(mk64 ._ b₂∈ _ refl) c₃@(mk64 ._ b₃∈ _ refl) pad refl)) refl) lineLen eol refl) suffix ps≡) →
--                 contradiction
--                   (success
--                     (s ++ b₁ ∷ b₂ ∷ b₃ ∷ [ '=' ]) _ refl
--                     (mkParseWhile (s ++ b₁ ∷ b₂ ∷ [ b₃ ]) '=' (All.++⁺ (Base64.Char.iList2All str) (c₁ All.∷ c₂ All.∷ c₃ All.∷ All.[])) {!!} {!!})
--                     (e ++ suffix)
--                     {!!})
--                   ¬p
--               (success ._ read read≡ (mkCertFinalLine{e = e} (mk64Str{p = p} str strLen (pad2 x) refl) lineLen eol refl) suffix ps≡) → {!!}
--                 ))
--           , tt
--         (yes (success pre₁ r₁ r₁≡ (mkParseWhile prefix term allPrefix ¬term ps≡) suf₁ ps≡₁)) → {!!}

