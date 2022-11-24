{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier
import      Aeres.Data.X509.Extension.AIA.AccessDesc.AccessMethod.TCB.OIDs as OIDs
open import Aeres.Data.X509.Extension.AIA.AccessDesc.AccessMethod.TCB
open import Aeres.Data.X509.GeneralName
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.Extension.AIA.AccessDesc.AccessMethod.Eq where

open Aeres.Grammar.Definitions UInt8

instance
  eq≋ : Eq≋ (AlgorithmIdentifierFields AccessMethodParam)
  eq≋ =
    AlgorithmIdentifier.eq≋ AccessMethodParam
      λ o → eq≋Σₚ it λ _ →
        record
          { _≟_ = λ x y → yes (T-unique x y)
          }
