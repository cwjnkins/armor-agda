{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X509.Extension.AIA.AccessDesc.TCB.OIDs as OIDs
open import Aeres.Data.X509.Extension.AIA.AccessDesc.TCB
open import Aeres.Data.X509.GeneralNames
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
open import Aeres.Data.X690-DER.TLV
open import Aeres.Prelude

module Aeres.Data.X509.Extension.AIA.AccessDesc.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8

@0 unambiguous : Unambiguous AccessDesc
unambiguous = TLV.unambiguous 
  (DefinedByOID.unambiguous _
    (λ o → Parallel.unambiguous×ₚ GeneralNames.GeneralName.unambiguous (λ a₁ a₂ → T-unique a₁ a₂)))

postulate
  @0 nonmalleable : NonMalleable RawAccessDesc
