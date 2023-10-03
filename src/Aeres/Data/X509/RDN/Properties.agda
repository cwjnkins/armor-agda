{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.RDN.ATV
open import Aeres.Data.X509.RDN.TCB
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
open import Aeres.Prelude
import      Data.Nat.Properties as Nat

module Aeres.Data.X509.RDN.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8

@0 unambiguousElems : Unambiguous RDNElems
unambiguousElems =
  Parallel.unambiguous
    (SequenceOf.unambiguous ATV.unambiguous TLV.nonempty TLV.nosubstrings)
    (λ _ _ _ → Nat.≤-irrelevant _ _)

@0 unambiguous : Unambiguous Name
unambiguous =
  TLV.unambiguous
    (SequenceOf.unambiguous (TLV.unambiguous unambiguousElems)
      TLV.nonempty
      TLV.nosubstrings)

instance
  RDNElemsEq≋ : Eq≋ RDNElems
  RDNElemsEq≋ = SequenceOf.BoundedSequenceOfEq≋

postulate --type checking is stuck
  @0 nonmalleable : NonMalleable RawName
  -- nonmalleable = TLV.nonmalleable (SequenceOf.nonmalleable TLV.nonempty TLV.nosubstrings
  --               (TLV.nonmalleable (SequenceOf.Bounded.nonmalleable TLV.nonempty TLV.nosubstrings ATV.nonmalleable))
