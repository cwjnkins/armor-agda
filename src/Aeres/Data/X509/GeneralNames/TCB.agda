{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.RDN.TCB
open import Aeres.Data.X509.GeneralNames.GeneralName.TCB
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.Strings
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.SequenceOf.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel.TCB
import      Aeres.Grammar.Sum.TCB
open import Aeres.Prelude

module Aeres.Data.X509.GeneralNames.TCB where

open      Aeres.Grammar.Definitions              UInt8
open      Aeres.Grammar.Parallel.TCB             UInt8
open      Aeres.Grammar.Sum.TCB                  UInt8

GeneralNamesElems = NonEmptySequenceOf GeneralName
GeneralNames = TLV Tag.Sequence GeneralNamesElems

RawGeneralNamesElems : Raw GeneralNamesElems
RawGeneralNamesElems = RawBoundedSequenceOf RawGeneralName 1

RawGeneralNames : Raw GeneralNames
RawGeneralNames = RawTLV _ RawGeneralNamesElems
