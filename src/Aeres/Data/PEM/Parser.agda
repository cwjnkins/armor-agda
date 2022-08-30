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
  parseWSP : Parser (Logging ∘ Dec) RFC5234.WSP
  parseWSP =
    parseSum
      (parseLit (tell "parseWSP: EOF") (return (Level.lift tt)) [ ' ' ])
      (parseLit (tell "parseWSP: EOF") (return (Level.lift tt)) [ '\t' ])

  abstract
    parseCRLF : Parser (Logging ∘ Dec) (_≡ '\r' ∷ [ '\n' ])
    parseCRLF = parseLit (tell "parseCRLF: EOF") silent ('\r' ∷ [ '\n' ])

    parseCR : Parser (Logging ∘ Dec) (_≡ [ '\r' ])
    parseCR = parseLit (tell "parseCR: EOF") silent [ '\r' ]

    parseLF : Parser (Logging ∘ Dec) (_≡ [ '\n' ])
    parseLF = parseLit silent silent ([ '\n' ])

  parseEOL : LogDec.MaximalParser RFC5234.EOL
  parseEOL =
    record { parser = mkParser (λ xs → proj₁ $ help xs)
           ; max = λ xs → proj₂ $ help xs }
    where
    help : ∀ xs → Σ (Logging ∘ Dec $ (Success RFC5234.EOL xs)) (LogDec.Lift (Success RFC5234.EOL xs) LogDec.GreatestSuccess)
    help xs =
      case runParser parseCRLF xs of λ where
        (mkLogged l₁ (yes p@(success pre r refl refl suf refl))) →
          (mkLogged l₁ (yes (mapSuccess (λ where refl → RFC5234.crlf) p))) ,
          λ where
            .('\r' ∷ [ '\n' ]) suf' eq RFC5234.crlf → Nat.≤-refl
            .([ '\r' ]) suf' eq RFC5234.cr → s≤s z≤n
        (mkLogged l₁ (no ¬p₁)) →
          case runParser parseCR xs of λ where
            (mkLogged l₂ (yes p@(success pre r refl refl suf refl))) →
              (mkLogged (l₁ ++ l₂) (yes (mapSuccess (λ where refl → RFC5234.cr) p))) ,
              (λ where
                .('\r' ∷ [ '\n' ]) suf' eq RFC5234.crlf →
                  contradiction (success _ _ refl refl _ eq) ¬p₁
                .([ '\r' ]) suf' eq RFC5234.cr → Nat.≤-refl)
            (mkLogged l₂ (no ¬p₂)) →
              case runParser parseLF xs of λ where
                (mkLogged l₃ (yes p@(success pre r refl refl suf refl))) →
                  (mkLogged (l₁ ++ l₂ ++ l₃) (yes (mapSuccess (λ where refl → RFC5234.lf) p)))
                  , λ where
                      .([ '\n' ]) suf' eq RFC5234.lf → Nat.≤-refl
                (mkLogged l₃ (no ¬p₃)) →
                  (mkLogged (l₁ ++ l₂ ++ l₃)
                    (no (λ where
                          (success .('\r' ∷ [ '\n' ]) read read≡ RFC5234.crlf suffix ps≡) →
                            contradiction (success _ _ refl refl _ ps≡) ¬p₁
                          (success .([ '\r' ]) read read≡ RFC5234.cr suffix ps≡) →
                            contradiction (success _ _ refl refl _ ps≡) ¬p₂
                          (success .([ '\n' ]) read read≡ RFC5234.lf suffix ps≡) →
                            contradiction (success _ _ refl refl _ ps≡) ¬p₃)))
                  , tt

module parsePEM where

  hereLine = "parseCertLine"

  parseCertBoundary : ∀ ctrl → LogDec.MaximalParser (CertBoundary ctrl)
  parseCertBoundary ctrl =
    LogDec.equivalent (CertBoundary.equiv ctrl)
      (LogDec.parse&₁
        (parseLit
          (tell "parseCertBoundary: underflow")
          (tell "parseCertBoudnary: mismatch")
          _)
        (λ where _ refl refl → refl)
        (LogDec.parseErased parseRFC5234.parseEOL))

  parseCertHeader = parseCertBoundary "BEGIN"
  parseCertFooter = parseCertBoundary "END"

  parseCertFullLine : LogDec.MaximalParser CertFullLine
  parseCertFullLine =
    LogDec.equivalent CertFullLine.equiv
      (LogDec.parse&₁
        (parseIList (tell "parseCertFullLine: underflow") Base64Char Base64.Char.nonempty
          Base64.Char.nonnesting parseBase64Char _)
        exactLength-nonnesting
        parseRFC5234.parseEOL)

  parseCertFinalLine : LogDec.MaximalParser CertFinalLine
  parseCertFinalLine = LogDec.mkMaximalParser help
    where
    open ≡-Reasoning

    help : ∀ xs → Σ (Logging ∘ Dec $ Success CertFinalLine xs) _
    help xs =
      let p₁ : Dec $ Success (ParseWhileₜ λ x → Base64Char [ x ]) xs
          p₁ = runParser (parseWhileₜ (base64Char? ∘ [_])) xs
      in
      case p₁ of λ where
        (no ¬p) →
          (mkLogged [ "parseCertFinalLine: underflow" ]
            (no λ where
              (success ._ read read≡ (mkCertFinalLine{e = e} (mk64Str{s}{p = p} str strLen (pad0 refl) refl) lineLen eol refl) suffix ps≡) → ‼
                let f : ∀ {@0 e} → RFC5234.EOL e → ∃₂ λ c e' → e ≡ c ∷ e'
                    f = λ where
                      RFC5234.crlf → _ , _ , refl
                      RFC5234.cr → _ , _ , refl
                      RFC5234.lf → _ , _ , refl

                    @0 e≡ : ∃₂ λ c e' → e ≡ c ∷ e'
                    e≡ = case eol of f

                    @0 c : _
                    c = proj₁ e≡

                    @0 e' : _
                    e' = proj₁ (proj₂ e≡)

                    c∉64 : ¬ Base64Char [ c ]
                    c∉64 = case eol ret (λ x → ¬ Base64Char [ proj₁ (f x) ]) of λ where
                      RFC5234.crlf → λ { (mk64 c c∈ i refl) → contradiction c∈ (toWitnessFalse{Q = '\r' ∈? _} tt)}
                      RFC5234.cr → λ { (mk64 c c∈ i refl) → contradiction c∈ (toWitnessFalse{Q = _ ∈? _} tt)}
                      RFC5234.lf → λ { (mk64 c c∈ i refl) → contradiction c∈ (toWitnessFalse{Q = _ ∈? _} tt)}
                in
                contradiction
                  (success (s ∷ʳ c) _ refl
                    (mkParseWhile _ c (Base64.Char.iList2All str) c∉64 refl)
                    (e' ++ suffix)
                    (begin (s ++ [ c ]) ++ e' ++ suffix   ≡⟨ sym (++-assoc (s ++ [ c ]) e' suffix) ⟩
                           ((s ++ [ c ]) ++ e') ++ suffix ≡⟨ cong (_++ suffix) (++-assoc s [ c ] e') ⟩
                           (s ++ [ c ] ++ e') ++ suffix   ≡⟨ ++-assoc s ([ c ] ++ e') suffix ⟩
                           s ++ ([ c ] ++ e') ++ suffix   ≡⟨ cong (λ x → s ++ x ++ suffix) (sym $ proj₂ (proj₂ e≡)) ⟩
                           s ++ e ++ suffix               ≡⟨ solve (++-monoid Char) ⟩
                           (s ++ e) ++ suffix             ≡⟨ cong (λ x → (x ++ e) ++ suffix) (sym (++-identityʳ s)) ⟩
                           ((s ++ []) ++ e) ++ suffix     ≡⟨ ps≡ ⟩
                           xs                             ∎))
                  ¬p
              (success ._ read read≡ (mkCertFinalLine{e = e} (mk64Str{s}{p = p} str strLen (pad1 (mk64P1{b₁}{b₂}{b₃} c₁@(mk64 ._ b₁∈ _ refl) c₂@(mk64 ._ b₂∈ _ refl) c₃@(mk64 ._ b₃∈ _ refl) pad refl)) refl) lineLen eol refl) suffix ps≡) →
                contradiction
                  (success
                    (s ++ b₁ ∷ b₂ ∷ b₃ ∷ [ '=' ]) _ refl
                    (mkParseWhile (s ++ b₁ ∷ b₂ ∷ [ b₃ ]) '=' (All.++⁺ (Base64.Char.iList2All str) (c₁ All.∷ c₂ All.∷ c₃ All.∷ All.[])) {!!} {!!})
                    (e ++ suffix)
                    {!!})
                  ¬p
              (success ._ read read≡ (mkCertFinalLine{e = e} (mk64Str{p = p} str strLen (pad2 x) refl) lineLen eol refl) suffix ps≡) → {!!}
                ))
          , tt
        (yes (success pre₁ r₁ r₁≡ (mkParseWhile prefix term allPrefix ¬term ps≡) suf₁ ps≡₁)) → {!!}

