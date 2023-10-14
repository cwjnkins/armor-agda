{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension
import      Aeres.Data.X509.Extension.TCB.OIDs as OIDs
open import Aeres.Data.X509.PublicKey
open import Aeres.Data.X509.Name
open import Aeres.Data.X509.SignAlg
open import Aeres.Data.X509.TBSCert.Properties
open import Aeres.Data.X509.TBSCert.TCB
open import Aeres.Data.X509.TBSCert.UID
open import Aeres.Data.X509.TBSCert.Version
open import Aeres.Data.X509.Validity
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Seq
open import Aeres.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.TBSCert.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Seq         UInt8

private
  here' = "X509: TBSCert"

parseTBSCertFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength TBSCertFields n)
parseTBSCertFields n =
  parseEquivalent (Iso.transEquivalent (Iso.symEquivalent Distribute.exactLength-&) (Parallel.equivalent₁ equivalentTBSCertFields))
    (parse&ᵈ{A = Length≤ (&ₚ (Option Version) Int) n}
      (Parallel.nosubstrings₁ (NonNesting.noconfusion-option&₁ TLV.nosubstrings TLV.nosubstrings (TLV.noconfusion λ ())))
      (Parallel.Length≤.unambiguous _
        (Unambiguous.unambiguous-option₁&₁
          (TLV.unambiguous
            Int.unambiguous)
          TLV.nosubstrings
          Int.unambiguous (TLV.noconfusion λ ())))
      (Option.parseOption₁&₁≤ parseVersion Int.parse TLV.nosubstrings TLV.nosubstrings (TLV.noconfusion (λ ())) overflow n)
      λ where
        (singleton r₁ r₁≡) _ →
          subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength Rep₇ (n - x)))
            r₁≡ (p₁ (n - r₁)))
  where
  overflow : Logging (Level.Lift _ ⊤)
  overflow = tell $ here' String.++ ": overflow"


  p₆ : ∀ n → Parser (Logging ∘ Dec) (ExactLength Rep₂ n)
  p₆ n =
      Option.parseOption₃{A = IssUID}{B = SubUID}{C = Extensions}
        TLV.nosubstrings TLV.nosubstrings TLV.nosubstrings
        (TLV.noconfusion λ ()) (TLV.noconfusion λ ()) (TLV.noconfusion λ ())
        parseIssUID parseSubUID parseExtensions
        (tell $ here' String.++ ": underflow (issUID, subUID, extensions)")
        _

  p₅ : ∀ n → Parser (Logging ∘ Dec) (ExactLength Rep₃ n)
  p₅ n =
    parseEquivalent (Iso.symEquivalent Distribute.exactLength-&)
      (parse&ᵈ {A = Length≤ (PublicKey ×ₚ Singleton) n}
        (Parallel.nosubstrings₁ (Parallel.nosubstrings₁ TLV.nosubstrings))
        (Parallel.Length≤.unambiguous _ (Parallel.unambiguous×ₚ PublicKey.unambiguous (λ where self self → refl)))
        (parse≤ _ (parse×Singleton PublicKey.parse)
        (Parallel.nosubstrings₁ TLV.nosubstrings) overflow)
        λ where
          (singleton r r≡) _ →
            subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength Rep₂ (n - x)))
              r≡ (p₆ (n - r)))

  p₄ : ∀ n → Parser (Logging ∘ Dec) (ExactLength Rep₄ n)
  p₄ n =
    parseEquivalent (Iso.symEquivalent Distribute.exactLength-&)
      (parse&ᵈ {A = Length≤ Name n}
        (Parallel.nosubstrings₁ TLV.nosubstrings)
        (Parallel.Length≤.unambiguous _ Name.unambiguous)
        (parse≤ _ Name.parse TLV.nosubstrings overflow)
        λ where
          (singleton r r≡) _ →
            subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength Rep₃ (n ∸ x)))
              r≡
              (p₅ (n - r)))

  p₃ : ∀ n → Parser (Logging ∘ Dec) (ExactLength Rep₅ n)
  p₃ n =
    parseEquivalent (Iso.symEquivalent Distribute.exactLength-&)
      (parse&ᵈ {A = Length≤ Validity n}
        (Parallel.nosubstrings₁ TLV.nosubstrings)
        (Parallel.Length≤.unambiguous _ Validity.unambiguous)
        (parse≤ _ parseValidity TLV.nosubstrings overflow)
        λ where
          (singleton r r≡) _ →
            subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength Rep₄ (n ∸ x)))
              r≡ (p₄ (n - r)))

  p₂ : ∀ n → Parser (Logging ∘ Dec) (ExactLength Rep₆ n)
  p₂ n  =
    parseEquivalent (Iso.symEquivalent Distribute.exactLength-&)
      (parse&ᵈ{A = Length≤ Name n}
        (Parallel.nosubstrings₁ TLV.nosubstrings)
        (Parallel.Length≤.unambiguous _ Name.unambiguous)
        (parse≤ _ Name.parse TLV.nosubstrings overflow)
        λ where
          (singleton r r≡) _ →
            subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength Rep₅ (n ∸ x)))
              r≡ (p₃ (n - r)))

  p₁ : ∀ n → Parser (Logging ∘ Dec) (ExactLength Rep₇ n)
  p₁ n =
    parseEquivalent (Iso.symEquivalent Distribute.exactLength-&)
      (parse&ᵈ{A = Length≤ SignAlg n}
        (Parallel.nosubstrings₁{A = SignAlg} SignAlg.nosubstrings)
        (Parallel.Length≤.unambiguous _ SignAlg.unambiguous)
        (parse≤ _ parseSignAlg SignAlg.nosubstrings overflow)
        λ where
          (singleton r r≡) _ →
            subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength Rep₆ (n - x)))
              r≡ (p₂ (n - r)))

parseTBSCert : Parser (Logging ∘ Dec) TBSCert
parseTBSCert = parseTLV _ here' _ parseTBSCertFields
