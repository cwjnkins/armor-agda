{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier.TCB
import      Aeres.Data.X509.Extension.AIA.AccessDesc.AccessMethod.TCB.OIDs as OIDs
open import Aeres.Data.X509.GeneralName.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.Extension.AIA.AccessDesc.AccessMethod.TCB where

open Aeres.Grammar.Definitions UInt8

supportedAccessMethod : List (Exists─ _ OIDValue)
supportedAccessMethod = (-, OIDs.OSCP) ∷ [ -, OIDs.CAIssuers ]

AccessMethodParam : ∀ {@0 bs} → OID bs → @0 List UInt8 → Set
AccessMethodParam o =
     GeneralName
  ×ₚ const (True ((-, TLV.val o) ∈? supportedAccessMethod))

AccessMethod = AlgorithmIdentifier AccessMethodParam
