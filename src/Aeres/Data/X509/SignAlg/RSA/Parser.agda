{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X509.AlgorithmIdentifier
import      Aeres.Data.X509.HashAlg.Parser as HashAlg
open import Aeres.Data.X509.MaskGenAlg.Parser
open import Aeres.Data.X509.SignAlg.RSA.TCB
import      Aeres.Data.X509.SignAlg.RSA.Properties as RSA
import      Aeres.Data.X509.SignAlg.TCB.OIDs as OIDs
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.SignAlg.RSA.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8
open HashAlg
  using (parseSHA-Like)

parseMD2     = parseSHA-Like OIDs.RSA.MD2    "RSA (MD2)"
parseMD5     = parseSHA-Like OIDs.RSA.MD5    "RSA (MD5)"
parseSHA1    = parseSHA-Like OIDs.RSA.SHA1   "RSA (SHA1)"
parseSHA224  = parseSHA-Like OIDs.RSA.SHA224 "RSA (SHA224)"
parseSHA256  = parseSHA-Like OIDs.RSA.SHA256 "RSA (SHA256)"
parseSHA384  = parseSHA-Like OIDs.RSA.SHA384 "RSA (SHA384)"
parseSHA512  = parseSHA-Like OIDs.RSA.SHA512 "RSA (SHA512)"

parsePSS : Parser (Logging ∘ Dec) PSS
parsePSS =
  parseAlgorithmIdentifier "RSA (SSA-PSS)" help
  where
  help : ∀ n {@0 bs} → (o : OID bs) → Parser _ _
  help n o =
    parseEquivalent
      (symEquivalent (proj₁ Distribute.×ₚ-Σₚ-iso))
      (parse×Dec exactLength-nonnesting
        (tell $ "X509: SignAlg: RSA: PSS: mismatched OID")
        (parseEquivalent (equivalent×ₚ RSA.PSS.equiv)
          (parse&Option{M = Logging}
            (parseSum HashAlg.parseSHA1
              (parseSum HashAlg.parseSHA224
                (parseSum HashAlg.parseSHA256
                  (parseSum HashAlg.parseSHA384 HashAlg.parseSHA512))))
            (parse&Option{M = Logging}
              parseMGF1
              (parse&Option {M = Logging} parseInt
                (parseOption₁ExactLength (nonnestingΣₚ₁ TLV.nonnesting)
                  (tell "X509: SignAlg: RSA: trailerField: underflow")
                  (parseSigma TLV.nonnesting
                    (TLV.unambiguous Int.unambiguous) parseInt
                    (λ _ → _ ≟ _)))
                TLV.nonnesting)
              TLV.nonnesting)
            RSA.PSS.SupportedHashAlg.nonnesting _))
        λ x → _ ≋? _)
