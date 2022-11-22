{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Extension
open import Aeres.Data.X509.Properties as Props
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Decidable.TBSCert where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Parser      UInt8

module parseTBSCert where
  here' = "X509: TBSCert"

  parseTBSCertFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength X509.TBSCertFields n)
  parseTBSCertFields n =
    parseEquivalent (transEquivalent (symEquivalent Distribute.exactLength-&) (equivalent×ₚ Props.TBSCertFields.equivalent))
      (parse&ᵈ{A = WithinLength (&ₚ (Option Version) Int) n}
        (withinLength-nonnesting (NonNesting.noconfusion-option&₁ TLV.nonnesting TLV.nonnesting (TLV.noconfusion λ ())))
        (withinLength-unambiguous
          (Unambiguous.unambiguous-option₁&₁
            (TLV.unambiguous
              (TLV.unambiguous λ{xs} → Int.unambiguous{xs}))
            TLV.nonnesting
            (TLV.unambiguous λ{xs} → Int.unambiguous{xs}) (TLV.noconfusion λ ())))
        (parseOption₁&₁≤ parseVersion parseInt TLV.nonnesting TLV.nonnesting (TLV.noconfusion (λ ())) overflow n)
        λ where
          (singleton r₁ r₁≡) _ →
            subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength TBSCertFields.Rep₇ (n - x)))
              r₁≡ (p₁ (n - r₁)))
    where
    overflow : Logging (Level.Lift _ ⊤)
    overflow = tell $ here' String.++ ": overflow"


    p₆ : ∀ n → Parser (Logging ∘ Dec) (ExactLength TBSCertFields.Rep₂ n)
    p₆ n =
        parseOption₃{A = IssUID}{B = SubUID}{C = X509.Extensions}
          TLV.nonnesting TLV.nonnesting TLV.nonnesting
          (TLV.noconfusion λ ()) (TLV.noconfusion λ ()) (TLV.noconfusion λ ())
          parseIssUID parseSubUID parseExtensions
          (tell $ here' String.++ ": underflow (issUID, subUID, extensions)")
          _

    p₅ : ∀ n → Parser (Logging ∘ Dec) (ExactLength TBSCertFields.Rep₃ n)
    p₅ n =
      parseEquivalent (symEquivalent Distribute.exactLength-&)
        (parse&ᵈ {A = WithinLength (PublicKey ×ₚ Singleton) n}
          (withinLength-nonnesting (nonnestingΣₚ₁ TLV.nonnesting))
          (withinLength-unambiguous (unambiguous×ₚ PublicKey.unambiguous (λ where self self → refl)))
          (parse≤ _ (parse×Singleton parsePublicKey)
          (nonnesting×ₚ₁ TLV.nonnesting) overflow)
          λ where
            (singleton r r≡) _ →
              subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength TBSCertFields.Rep₂ (n - x)))
                r≡ (p₆ (n - r)))

    p₄ : ∀ n → Parser (Logging ∘ Dec) (ExactLength TBSCertFields.Rep₄ n)
    p₄ n =
      parseEquivalent (symEquivalent Distribute.exactLength-&)
        (parse&ᵈ {A = WithinLength RDNSeq n}
          (withinLength-nonnesting TLV.nonnesting)
          (withinLength-unambiguous RDN.Seq.unambiguous)
          (parse≤ _ parseRDNSeq TLV.nonnesting overflow)
          λ where
            (singleton r r≡) _ →
              subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength TBSCertFields.Rep₃ (n ∸ x)))
                r≡
                (p₅ (n - r)))

    p₃ : ∀ n → Parser (Logging ∘ Dec) (ExactLength TBSCertFields.Rep₅ n)
    p₃ n =
      parseEquivalent (symEquivalent Distribute.exactLength-&)
        (parse&ᵈ {A = WithinLength Validity n}
          (withinLength-nonnesting TLV.nonnesting)
          (withinLength-unambiguous (TLV.unambiguous Validity.unambiguous))
          (parse≤ _ parseValidity TLV.nonnesting overflow)
          λ where
            (singleton r r≡) _ →
              subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength TBSCertFields.Rep₄ (n ∸ x)))
                r≡ (p₄ (n - r)))

    p₂ : ∀ n → Parser (Logging ∘ Dec) (ExactLength TBSCertFields.Rep₆ n)
    p₂ n  =
      parseEquivalent (symEquivalent Distribute.exactLength-&)
        (parse&ᵈ{A = WithinLength RDNSeq n}
          (withinLength-nonnesting TLV.nonnesting)
          (withinLength-unambiguous RDN.Seq.unambiguous)
          (parse≤ _ parseRDNSeq TLV.nonnesting overflow)
          λ where
            (singleton r r≡) _ →
              subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength TBSCertFields.Rep₅ (n ∸ x)))
                r≡ (p₃ (n - r)))

    p₁ : ∀ n → Parser (Logging ∘ Dec) (ExactLength TBSCertFields.Rep₇ n)
    p₁ n =
      parseEquivalent (symEquivalent Distribute.exactLength-&)
        (parse&ᵈ{A = WithinLength SignAlg n}
          (withinLength-nonnesting{A = SignAlg} SignAlg.nonnesting)
          (withinLength-unambiguous SignAlg.unambiguous)
          (parse≤ _ parseSignAlg SignAlg.nonnesting overflow)
          λ where
            (singleton r r≡) _ →
              subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength TBSCertFields.Rep₆ (n - x)))
                r≡ (p₂ (n - r)))

  parseTBSCert : Parser (Logging ∘ Dec) X509.TBSCert
  parseTBSCert = parseTLV _ "TBS cert." _ parseTBSCertFields

open parseTBSCert public using (parseTBSCert)
