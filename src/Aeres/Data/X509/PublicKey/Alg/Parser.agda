{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg.EC
open import Aeres.Data.X509.PublicKey.Alg.RSA
open import Aeres.Data.X509.PublicKey.Alg.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum

module Aeres.Data.X509.PublicKey.Alg.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

parseUnsupported : Parser (Logging ∘ Dec) UnsupportedPublicKeyAlg
parseUnsupported =
  parseTLV _ "X509: PublicKey: Alg: unsupported" _
    λ n →
      parseEquivalent (symEquivalent Distribute.exactLength-&)
        (parse&ᵈ
          (withinLength-nonnesting (nonnestingΣₚ₁ TLV.nonnesting))
          (unambiguousΣₚ
            (unambiguousΣₚ OID.unambiguous (λ _ → T-unique))
            λ _ _ _ → erased-unique ≤-unique _ _ )
          (parse≤ _
            (parseSigma TLV.nonnesting OID.unambiguous parseOID
              (λ x → T-dec))
            (nonnestingΣₚ₁ TLV.nonnesting)
            (tell $ "X509: SignAlg: unsupported: OID overflow"))
          λ where
            (singleton r r≡) (mk×ₚ o o∉ refl) →
              subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength OctetStringValue (n - x)))
                (‼ r≡)
                (parseOctetStringValue (n - r)))

parseSignAlg : Parser (Logging ∘ Dec) PublicKeyAlg
parseSignAlg =
   parseSum parseRSA
  (parseSum parseEC
            parseUnsupported)
