{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension
import      Aeres.Data.X509.Extension.TCB.OIDs as OIDs
open import Aeres.Data.X509.PublicKey
open import Aeres.Data.X509.RDN
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
open import Aeres.Data.X690-DER.Time.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
open import Aeres.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.TBSCert.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Properties  UInt8

private
  here' = "X509: TBSCert"

parseTBSCertFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength TBSCertFields n)
parseTBSCertFields n =
  parseEquivalent (transEquivalent (symEquivalent Distribute.exactLength-&) (equivalent×ₚ equivalent))
    (parse&ᵈ{A = WithinLength (&ₚ (Option Version) Int) n}
      (withinLength-nonnesting (NonNesting.noconfusion-option&₁ TLV.nonnesting TLV.nonnesting (TLV.noconfusion λ ())))
      (withinLength-unambiguous
        (Unambiguous.unambiguous-option₁&₁
          (TLV.unambiguous
            (TLV.unambiguous λ{xs} → Int.unambiguous{xs}))
          TLV.nonnesting
          (TLV.unambiguous λ{xs} → Int.unambiguous{xs}) (TLV.noconfusion λ ())))
      (parseOption₁&₁≤ parseVersion Int.parse TLV.nonnesting TLV.nonnesting (TLV.noconfusion (λ ())) overflow n)
      λ where
        (singleton r₁ r₁≡) _ →
          subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength Rep₇ (n - x)))
            r₁≡ (p₁ (n - r₁)))
  where
  overflow : Logging (Level.Lift _ ⊤)
  overflow = tell $ here' String.++ ": overflow"


  p₆ : ∀ n → Parser (Logging ∘ Dec) (ExactLength Rep₂ n)
  p₆ n =
      parseOption₃{A = IssUID}{B = SubUID}{C = Extensions}
        TLV.nonnesting TLV.nonnesting TLV.nonnesting
        (TLV.noconfusion λ ()) (TLV.noconfusion λ ()) (TLV.noconfusion λ ())
        parseIssUID parseSubUID parseExtensions
        (tell $ here' String.++ ": underflow (issUID, subUID, extensions)")
        _

  p₅ : ∀ n → Parser (Logging ∘ Dec) (ExactLength Rep₃ n)
  p₅ n =
    parseEquivalent (symEquivalent Distribute.exactLength-&)
      (parse&ᵈ {A = WithinLength (PublicKey ×ₚ Singleton) n}
        (withinLength-nonnesting (nonnestingΣₚ₁ TLV.nonnesting))
        (withinLength-unambiguous (unambiguous×ₚ PublicKey.unambiguous (λ where self self → refl)))
        (parse≤ _ (parse×Singleton parsePublicKey)
        (nonnesting×ₚ₁ TLV.nonnesting) overflow)
        λ where
          (singleton r r≡) _ →
            subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength Rep₂ (n - x)))
              r≡ (p₆ (n - r)))

  p₄ : ∀ n → Parser (Logging ∘ Dec) (ExactLength Rep₄ n)
  p₄ n =
    parseEquivalent (symEquivalent Distribute.exactLength-&)
      (parse&ᵈ {A = WithinLength RDNSeq n}
        (withinLength-nonnesting TLV.nonnesting)
        (withinLength-unambiguous RDN.Seq.unambiguous)
        (parse≤ _ parseRDNSeq TLV.nonnesting overflow)
        λ where
          (singleton r r≡) _ →
            subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength Rep₃ (n ∸ x)))
              r≡
              (p₅ (n - r)))

  p₃ : ∀ n → Parser (Logging ∘ Dec) (ExactLength Rep₅ n)
  p₃ n =
    parseEquivalent (symEquivalent Distribute.exactLength-&)
      (parse&ᵈ {A = WithinLength Validity n}
        (withinLength-nonnesting TLV.nonnesting)
        (withinLength-unambiguous (TLV.unambiguous Validity.unambiguous))
        (parse≤ _ parseValidity TLV.nonnesting overflow)
        λ where
          (singleton r r≡) _ →
            subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength Rep₄ (n ∸ x)))
              r≡ (p₄ (n - r)))

  p₂ : ∀ n → Parser (Logging ∘ Dec) (ExactLength Rep₆ n)
  p₂ n  =
    parseEquivalent (symEquivalent Distribute.exactLength-&)
      (parse&ᵈ{A = WithinLength RDNSeq n}
        (withinLength-nonnesting TLV.nonnesting)
        (withinLength-unambiguous RDN.Seq.unambiguous)
        (parse≤ _ parseRDNSeq TLV.nonnesting overflow)
        λ where
          (singleton r r≡) _ →
            subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength Rep₅ (n ∸ x)))
              r≡ (p₃ (n - r)))

  p₁ : ∀ n → Parser (Logging ∘ Dec) (ExactLength Rep₇ n)
  p₁ n =
    parseEquivalent (symEquivalent Distribute.exactLength-&)
      (parse&ᵈ{A = WithinLength SignAlg n}
        (withinLength-nonnesting{A = SignAlg} SignAlg.nonnesting)
        (withinLength-unambiguous SignAlg.unambiguous)
        (parse≤ _ parseSignAlg SignAlg.nonnesting overflow)
        λ where
          (singleton r r≡) _ →
            subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength Rep₆ (n - x)))
              r≡ (p₂ (n - r)))

parseTBSCert : Parser (Logging ∘ Dec) TBSCert
parseTBSCert = parseTLV _ here' _ parseTBSCertFields
