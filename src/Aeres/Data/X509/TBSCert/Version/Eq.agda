open import Aeres.Binary
open import Aeres.Data.X509.TBSCert.Version.TCB
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
open import Aeres.Prelude

module Aeres.Data.X509.TBSCert.Version.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8

instance
  eq≋ : Eq≋ Version
  eq≋ = Parallel.eq≋Σₚ
          it
          λ a → record { _≟_ = λ where
            a∈₁ a∈₂ → yes (erased-unique (∈-unique (toWitness{Q = unique? supportedVersions} tt)) a∈₁ a∈₂) }
