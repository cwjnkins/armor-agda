{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Bitstring
open import Aeres.Data.X509.Decidable.SignAlg
open import Aeres.Data.X509.Decidable.TBSCert
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Decidable.Cert where

open Base256
open import Aeres.Grammar.Definitions UInt8
open import Aeres.Grammar.Properties  UInt8

module parseCert where

  here' = "parseCert"

  parseCertFields : ExactLengthParser _ (Logging ∘ Dec) X509.CertFields
  parseCertFields n =
    parseEquivalent _ (transEquivalent (symEquivalent Distribute.exactLength-&) (equivalent×ₚ Props.CertFields.equivalent))
      (parse&ᵈ _ (withinLength-nonnesting TLV.nonnesting) (withinLength-unambiguous (TLV.unambiguous Props.TBSCertFields.unambiguous))
        (parse≤ _ n parseTBSCert TLV.nonnesting (tell $ here' String.++ ": overflow"))
        λ where
          (singleton r₀ r₀≡) _ →
            subst₀ (λ x → Parser _ (Logging ∘ Dec) (ExactLength _ (n ∸ x))) r₀≡
              (parseExactLength _
                (NonNesting&ₚ TLV.nonnesting TLV.nonnesting)
                (tell $ here' String.++ ": length mismatch")
                (parse& _ TLV.nonnesting parseSignAlg parseBitstring) (n - r₀)))

  parseCert : Parser _ (Logging ∘ Dec) X509.Cert
  parseCert =
    parseTLV _ "cert" _ parseCertFields

open parseCert public using (parseCert)
