{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Bitstring
open import Aeres.Data.X509.Decidable.SignAlg
open import Aeres.Data.X509.Decidable.TBSCert
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Decidable.Cert where

open Base256
open import Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Properties  Dig

module parseCert where

  here' = "parseCert"

  parseCertFields : ExactLengthParser _ (Logging ∘ Dec) X509.CertFields
  parseCertFields n =
    parseEquivalent _ (transEquivalent (symEquivalent Distribute.exactLength-&) (equivalent×ₚ Props.CertFields.equivalent))
      (parse&ᵈ _ (withinLength-nonnesting Props.TLV.nonnesting) (withinLength-unambiguous (TLV.unambiguous Props.TBSCertFields.unambiguous))
        (parse≤ _ n parseTBSCert Props.TLV.nonnesting (tell $ here' String.++ ": overflow"))
        λ where
          (singleton r₀ r₀≡) _ →
            subst₀ (λ x → Parser _ (Logging ∘ Dec) (ExactLength _ (n ∸ x))) r₀≡
              (parseExactLength _
                (NonNesting&ₚ Props.TLV.nonnesting Props.TLV.nonnesting)
                (tell $ here' String.++ ": length mismatch")
                (parse& _ Props.TLV.nonnesting parseSignAlg parseBitstring) (n - r₀)))

  parseCert : Parser _ (Logging ∘ Dec) X509.Cert
  parseCert =
    parseTLV _ "cert" _ parseCertFields

open parseCert public using (parseCert)
