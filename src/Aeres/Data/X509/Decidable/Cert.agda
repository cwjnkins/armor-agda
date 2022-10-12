{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.SignAlg
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

  here' = "parseCert"

  parseCertFields : ExactLengthParser (Logging ∘ Dec) X509.CertFields
  parseCertFields n =
    parseEquivalent
      (transEquivalent
        (symEquivalent Distribute.exactLength-&)
        (equivalent×ₚ Props.CertFields.equiv))
      (parse&ᵈ (withinLength-nonnesting (nonnestingΣₚ₁ TLV.nonnesting))
        (withinLength-unambiguous
          (unambiguous×ₚ
            (TLV.unambiguous Props.TBSCertFields.unambiguous)
            (λ where self self → refl)))
        (parse≤ n (parse×Singleton parseTBSCert) (nonnestingΣₚ₁ TLV.nonnesting) (tell $ here' String.++ ": overflow"))
        λ where
          (singleton r₀ r₀≡) _ →
            subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength _ (n ∸ x))) r₀≡
              (parseExactLength
                (NonNesting&ₚ TLV.nonnesting TLV.nonnesting)
                (tell $ here' String.++ ": length mismatch")
                (parse& TLV.nonnesting parseSignAlg parseBitstring) (n - r₀)))

  parseCert : Parser (Logging ∘ Dec) X509.Cert
  parseCert =
    parseTLV _ "cert" _ parseCertFields

open parseCert public using (parseCert)
