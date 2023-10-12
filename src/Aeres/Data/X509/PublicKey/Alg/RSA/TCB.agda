{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.SignAlg.DSA.TCB
  using (DSA-Like ; RawDSALike)
import      Aeres.Data.X509.PublicKey.Alg.TCB.OIDs as OIDs
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.Sequence.DefinedByOID.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Grammar.Definitions.NonMalleable
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.RSA.TCB where

open Aeres.Grammar.Definitions.NonMalleable UInt8

RSA = DSA-Like OIDs.RSA

getOID : ∀ {@0 bs} → RSA bs → Exists─ _ OID
getOID x = -, DefinedByOIDFields.oid (TLV.val x)

RawRSA : Raw RSA
RawRSA = RawDSALike OIDs.RSA
