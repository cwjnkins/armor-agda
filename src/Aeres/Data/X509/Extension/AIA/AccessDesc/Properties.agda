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

module Aeres.Data.X509.Extension.AIA.AccessDesc.Properties where

open Aeres.Grammar.Definitions UInt8

@0 unambiguous : Unambiguous (AlgorithmIdentifierFields AccessDescParam)
unambiguous =
  AlgorithmIdentifier.unambiguous _
    (λ o → unambiguous×ₚ GeneralName.unambiguous (λ a₁ a₂ → T-unique a₁ a₂))
