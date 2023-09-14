{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.HashAlg
import      Aeres.Data.X509.MaskGenAlg.TCB.OIDs as OIDs
open import Aeres.Data.X509.MaskGenAlg.Properties
import      Aeres.Data.X509.MaskGenAlg.TCB as MaskGenAlg
open import Aeres.Data.X690-DER.Null.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.MaskGenAlg.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Sum         UInt8

parseMGF1 : Parser (Logging ∘ Dec) MaskGenAlg.MGF1.MaskGenAlg
parseMGF1 =
  DefinedByOID.parse "X509: MaskGenAlg: MGF1"
    help
  where
  open MaskGenAlg.MGF1

  help : ∀ n {@0 bs} → (o : OID bs) → Parser _ _
  help n o =
    parseExactLength
      (nonnesting×ₚ₁ MGF1.SupportedHashAlg.nonnesting)
      (tell $ "X509: MaskGenAlg: MGF1: length mismatch")
      (parse×Dec MGF1.SupportedHashAlg.nonnesting
        (tell $ "X509: MaskGenAlg: MGF1: mismatched maskgen OID")
        ( parseSum parseSHA1
         (parseSum parseSHA224
         (parseSum parseSHA256
         (parseSum parseSHA384
                   parseSHA512))))
        (λ _ → _ ≋? _))
      _
