{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg.EC.Params
open import Aeres.Data.X509.PublicKey.Alg.EC.TCB
open import Aeres.Data.X690-DER.OID
import      Aeres.Data.X690-DER.Sequence.DefinedByOID.Properties as DefinedByOID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.EC.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8

@0 unambiguous : Unambiguous EC
unambiguous =
  TLV.unambiguous
    (DefinedByOID.unambiguous Params
      (λ o → Parallel.unambiguous Params.unambiguous (λ where _ ≋-refl ≋-refl → refl)))

postulate
  @0 nonmalleable : NonMalleable RawEC
