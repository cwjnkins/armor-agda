{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Cert.Properties
open import Aeres.Data.X509.Cert.TCB
open import Aeres.Data.X509.Extension.TCB
open import Aeres.Data.X509.RDN.TCB
open import Aeres.Data.X509.SignAlg
open import Aeres.Data.X509.TBSCert
import      Aeres.Data.X509.TBSCert.UID.TCB as TBSCert
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.Time.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
open import Aeres.Prelude

module Aeres.Data.X509.Cert.Parser where

open Aeres.Grammar.Definitions  UInt8
open Aeres.Grammar.IList        UInt8
open Aeres.Grammar.Option       UInt8
open Aeres.Grammar.Parser       UInt8
open Aeres.Grammar.Properties   UInt8

private
  here' = "X509: Cert"

parseCertFields : ExactLengthParser (Logging ∘ Dec) CertFields
parseCertFields n =
  parseEquivalent
    (transEquivalent
      (symEquivalent Distribute.exactLength-&)
      (equivalent×ₚ equiv))
    (parse&ᵈ{A = WithinLength (TBSCert ×ₚ Singleton) n}
      (withinLength-nonnesting (nonnesting×ₚ₁ TLV.nonnesting))
      (withinLength-unambiguous
        (unambiguous×ₚ
          (TLV.unambiguous TBSCert.unambiguous)
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

parseCert : Parser (Logging ∘ Dec) Cert
parseCert =
  parseTLV _ "Cert" _ parseCertFields

parseChain : Parser (Logging ∘ Dec) Chain
parseChain = LogDec.MaximalParser.parser (parseIListMax (mkLogged ["parseChain: underflow"] tt) _ TLV.nonempty TLV.nonnesting  parseCert)

  -- LogDec.MaximalParser.parser
  --   (parseIListMax.parseIListLowerBounded
  --     (mkLogged ["parseChain: underflow"] tt)
  --     _ TLV.nonempty TLV.nonnesting parseCert _)
