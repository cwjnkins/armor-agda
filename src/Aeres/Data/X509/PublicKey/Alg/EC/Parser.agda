{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X509.PublicKey.Alg.TCB.OIDs as OIDs
open import Aeres.Data.X509.PublicKey.Alg.EC.Params
open import Aeres.Data.X509.PublicKey.Alg.EC.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.EC.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

parseECParams : ∀ n {@0 bs} → (o : OID bs) → Parser (Logging ∘ Dec) (ExactLength (Params o) n)
parseECParams n o =
  parseExactLength
    (nonnesting×ₚ₁ Params.nonnesting)
    (tell $ "X509: PublicKey: Alg: EC: Params: length mismatch")
    (parse×Dec Params.nonnesting
      (tell $ "X509: PublicKey: Alg: EC: mismatched OID")
      parseEcPkAlgParams
      (λ _ → _ ≋? _))
    _

parseEC : Parser (Logging ∘ Dec) EC
parseEC = DefinedByOID.parse "X509: PublicKey: Alg: EC" parseECParams
