{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X509.Extension.AIA.AccessDesc.TCB.OIDs as OIDs
open import Aeres.Data.X509.GeneralName.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.Extension.AIA.AccessDesc.TCB where

open Aeres.Grammar.Definitions UInt8

supportedAccessMethod : List (Exists─ _ OIDValue)
supportedAccessMethod = (-, OIDs.OSCP) ∷ [ -, OIDs.CAIssuers ]

AccessDescParam : {@0 bs : List UInt8} → OID bs → @0 List UInt8 → Set
AccessDescParam o =
     GeneralName
  ×ₚ const (True ((-, TLV.val o) ∈? supportedAccessMethod))

AccessDesc : @0 List UInt8 → Set
AccessDesc = DefinedByOID AccessDescParam
