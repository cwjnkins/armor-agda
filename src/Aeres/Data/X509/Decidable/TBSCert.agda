{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Bitstring
open import Aeres.Data.X509.Decidable.Extension
open import Aeres.Data.X509.Decidable.Int
open import Aeres.Data.X509.Decidable.PublicKey
open import Aeres.Data.X509.Decidable.RDN
open import Aeres.Data.X509.Decidable.SignAlg
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Decidable.Validity
open import Aeres.Data.X509.Decidable.Version
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Decidable.TBSCert where

open Base256
open import Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Properties  Dig

module parseTBSCert where
  here' = "parseTBSCert"

  parseTBSCertFields : ExactLengthParser _ (Logging ∘ Dec) X509.TBSCertFields
  parseTBSCertFields n =
    parseEquivalent _ (transEquivalent (symEquivalent Distribute.exactLength-&) (equivalent×ₚ Props.TBSCertFields.equivalent))
      (parse&ᵈ _
        (withinLength-nonnesting (NonNesting.noconfusion-option&₁ Props.TLV.nonnesting Props.TLV.nonnesting (Props.TLV.noconfusion λ ())))
        (withinLength-unambiguous (Unambiguous.unambiguous-option₁&₁ (Props.TLV.unambiguous (TLV.unambiguous Props.Primitives.IntegerValue.unambiguous)) Props.TLV.nonnesting (Props.TLV.unambiguous Props.Primitives.IntegerValue.unambiguous) Props.TLV.nonnesting (Props.TLV.noconfusion λ ())))
        (parseOption₁&₁≤ _ parseVersion parseInt Props.TLV.nonnesting Props.TLV.nonnesting (TLV.noconfusion (λ ())) overflow n)
        λ where
          {bs} (singleton read read≡) _ →
            subst₀ (λ x → Parser _ (Logging ∘ Dec) (ExactLength _ (n - x))) read≡
              (parseEquivalent _ (symEquivalent Distribute.exactLength-&)
                (parse&ᵈ _ (withinLength-nonnesting Props.TLV.nonnesting) (withinLength-unambiguous (TLV.unambiguous Props.SignAlgFields.unambiguous))
                  (parse≤ _ (n - read) parseSignAlg Props.TLV.nonnesting overflow)
                    λ where
                      {bs₁} (singleton r₁ r₁≡) _ →
                        subst₀ (λ x → Parser _ (Logging ∘ Dec) (ExactLength _ (n - read - x))) r₁≡
                          (parseEquivalent _ (symEquivalent Distribute.exactLength-&)
                            (parse&ᵈ _ (withinLength-nonnesting Props.TLV.nonnesting) (withinLength-unambiguous (TLV.unambiguous (Seq.unambiguous (TLV.unambiguous (Seq.unambiguous (TLV.unambiguous Props.RDNATVFields.unambiguous))))))
                              (parse≤ _ (n - read - r₁) parseRDNSeq Props.TLV.nonnesting overflow)
                              λ {_} (singleton r₂ r₂≡) _ →
                                subst₀ (λ x → Parser _ (Logging ∘ Dec) (ExactLength _ (n - read - r₁ - x))) r₂≡
                                  (parseEquivalent _ (symEquivalent Distribute.exactLength-&)
                                    (parse&ᵈ _ (withinLength-nonnesting Props.TLV.nonnesting) (withinLength-unambiguous (TLV.unambiguous Props.ValidityFields.unambiguous))
                                      (parse≤ _ (n - read - r₁ - r₂) parseValidity Props.TLV.nonnesting overflow)
                                      λ where
                                        (singleton r₃ r₃≡) _ →
                                          subst₀ (λ x → Parser _ (Logging ∘ Dec) (ExactLength _ (n - read - r₁ - r₂ - x))) r₃≡
                                            (parseEquivalent _ (symEquivalent Distribute.exactLength-&)
                                              (parse&ᵈ _ (withinLength-nonnesting Props.TLV.nonnesting) (withinLength-unambiguous (TLV.unambiguous (Seq.unambiguous (TLV.unambiguous (Seq.unambiguous (TLV.unambiguous Props.RDNATVFields.unambiguous))))))
                                                (parse≤ _ (n - read - r₁ - r₂ - r₃) parseRDNSeq Props.TLV.nonnesting overflow)
                                                λ where
                                                  (singleton r₄ r₄≡) _ →
                                                    subst₀ (λ x → Parser _ (Logging ∘ Dec) (ExactLength _ (n - read - r₁ - r₂ - r₃ - x))) r₄≡
                                                      (parseEquivalent _ (symEquivalent Distribute.exactLength-&)
                                                        (parse&ᵈ _ (withinLength-nonnesting Props.TLV.nonnesting) (withinLength-unambiguous (TLV.unambiguous Props.PublicKeyFields.unambiguous))
                                                          (parse≤ _ (n - read - r₁ - r₂ - r₃ - r₄) parsePublicKey Props.TLV.nonnesting overflow)
                                                          λ where
                                                            (singleton r₅ r₅≡) _ →
                                                              subst₀ (λ x → Parser _ (Logging ∘ Dec) (ExactLength _ (n - read - r₁ - r₂ - r₃ - r₄ - x))) r₅≡
                                                                (parseOption₃ _ Props.TLV.nonnesting Props.TLV.nonnesting Props.TLV.nonnesting
                                                                  (TLV.noconfusion (λ ())) (Props.TLV.noconfusion λ ()) (Props.TLV.noconfusion λ ())
                                                                  parseIssUID parseSubUID parseExtensions (tell $ here' String.++ ": underflow") (n - read - r₁ - r₂ - r₃ - r₄ - r₅)) )))))))))))
    where
    overflow : Logging (Level.Lift _ ⊤)
    overflow = tell $ here' String.++ ": overflow"

  parseTBSCert : Parser _ (Logging ∘ Dec) X509.TBSCert
  parseTBSCert = parseTLV _ "TBS cert." _ parseTBSCertFields

open parseTBSCert public using (parseTBSCert)
