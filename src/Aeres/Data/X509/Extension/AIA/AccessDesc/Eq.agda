{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier
import      Aeres.Data.X509.Extension.AIA.AccessDesc.TCB.OIDs as OIDs
open import Aeres.Data.X509.Extension.AIA.AccessDesc.TCB
open import Aeres.Data.X509.GeneralName
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.Extension.AIA.AccessDesc.Eq where

open Aeres.Grammar.Definitions UInt8

instance
  eq≋ : Eq≋ (AlgorithmIdentifierFields AccessDescParam)
  eq≋ =
    AlgorithmIdentifier.eq≋ _
      λ o → eq≋Σₚ it λ _ →
        record
          { _≟_ = λ x y → yes (T-unique x y)
          }