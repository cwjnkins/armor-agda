open import Aeres.Binary
open import Aeres.Data.X509.GeneralNames
open import Aeres.Data.X509.Extension.CRLDistPoint.DistPoint
open import Aeres.Data.X509.Extension.CRLDistPoint.TCB
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X690-DER.SequenceOf
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CRLDistPoint.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Seq         UInt8

@0 unambiguous : Unambiguous CRLDistFields
unambiguous = TLV.unambiguous (TLV.unambiguous (SequenceOf.Bounded.unambiguous
                DistPoint.unambiguous TLV.nonempty TLV.nosubstrings))


@0 nonmalleable : NonMalleable RawCRLDistFields
nonmalleable = TLV.nonmalleable (TLV.nonmalleable (SequenceOf.Bounded.nonmalleable
                 TLV.nonempty TLV.nosubstrings DistPoint.nonmalleable))
