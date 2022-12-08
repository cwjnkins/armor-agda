{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier
open import Aeres.Data.X509.SignAlg.ECDSA.TCB
import      Aeres.Data.X509.SignAlg.TCB.OIDs as OIDs
open import Aeres.Data.X690-DER.Null
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Sum
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.SignAlg.ECDSA.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Sum         UInt8

parseECDSA-Like : ∀ {@0 bs} → (o : OIDValue bs) → String → Parser (Logging ∘ Dec) (ECDSA-Like o)
parseECDSA-Like o s =
  parseAlgorithmIdentifier s
    λ n o' →
      parseExactLength
        (λ where xs₁++ys₁≡xs₂++ys₂ (mk×ₚ refl _ refl) (mk×ₚ refl _ refl) → refl)
        (tell $ s String.++ ": length mismatch")
        (parse×Dec (λ where _ refl refl → refl)
          (tell $ s String.++ ": mismatched OID")
            (parseLit silent silent [])
            (λ _ → _ ≋? _))
        _

parseSHA1   = parseECDSA-Like OIDs.ECDSA.SHA1   "X509: SignAlg: ECDSA: SHA1"
parseSHA224 = parseECDSA-Like OIDs.ECDSA.SHA224 "X509: SignAlg: ECDSA: SHA224"
parseSHA256 = parseECDSA-Like OIDs.ECDSA.SHA256 "X509: SignAlg: ECDSA: SHA256"
parseSHA384 = parseECDSA-Like OIDs.ECDSA.SHA384 "X509: SignAlg: ECDSA: SHA384"
parseSHA512 = parseECDSA-Like OIDs.ECDSA.SHA512 "X509: SignAlg: ECDSA: SHA512"

parseSupported : Parser (Logging ∘ Dec) Supported
parseSupported =
   parseSum parseSHA1
  (parseSum parseSHA224
  (parseSum parseSHA256
  (parseSum parseSHA384
            parseSHA512)))
