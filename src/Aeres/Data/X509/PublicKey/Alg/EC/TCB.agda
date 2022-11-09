{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier.TCB
open import Aeres.Data.X509.PublicKey.Alg.EC.Params.TCB
import      Aeres.Data.X509.PublicKey.Alg.TCB.OIDs as OIDs
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.EC.TCB where

open Aeres.Grammar.Definitions UInt8

Params : {@0 bs : List UInt8} → (OID bs) → @0 List UInt8 → Set
Params o =
     EcPkAlgParams
  ×ₚ const (_≋_{A = OIDValue} (TLV.val o) OIDs.EC)

EC : @0 List UInt8 → Set
EC = AlgorithmIdentifier Params
