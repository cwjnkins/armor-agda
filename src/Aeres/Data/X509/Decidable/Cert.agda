{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.TBSCert
open import Aeres.Data.X509.Properties as Props
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Decidable.Cert where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Properties  UInt8

module parseCert where

  here' = "X509: Cert"

  parseCertFields : ExactLengthParser (Logging ∘ Dec) X509.CertFields
  parseCertFields n =
    parseEquivalent
      (transEquivalent
        (symEquivalent Distribute.exactLength-&)
        (equivalent×ₚ Props.CertFields.equiv))
      (parse&ᵈ{A = WithinLength (X509.TBSCert ×ₚ Singleton) n}
        (withinLength-nonnesting (nonnesting×ₚ₁ TLV.nonnesting))
        (withinLength-unambiguous
          (unambiguous×ₚ
            (TLV.unambiguous Props.TBSCertFields.unambiguous)
            (λ where self self → refl)))
        (parse≤ _ (parse×Singleton parseTBSCert)
          (nonnesting×ₚ₁ TLV.nonnesting)
          (tell $ here' String.++ ": overflow (TBS cert)"))
        λ where
          (singleton r r≡) a →
            subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength (&ₚ SignAlg (BitString ×ₚ Singleton)) (n - x)))
              r≡ (p₁ (n - r)))
    where
    p₁ : ∀ n → Parser (Logging ∘ Dec) (ExactLength (&ₚ SignAlg (BitString ×ₚ Singleton)) n)
    p₁ n =
      parseExactLength
        (NonNesting&ₚ SignAlg.nonnesting (nonnesting×ₚ₁ TLV.nonnesting))
        (tell $ here' String.++ ": length mismatch (sign alg, signature)")
        (parse& SignAlg.nonnesting parseSignAlg
          (parse×Singleton parseBitstring)) _

  parseCert : Parser (Logging ∘ Dec) X509.Cert
  parseCert =
    parseTLV _ "cert" _ parseCertFields

open parseCert public using (parseCert)
