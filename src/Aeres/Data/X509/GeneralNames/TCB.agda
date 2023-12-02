open import Aeres.Binary
open import Aeres.Data.X509.Name.TCB
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

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.6
--    GeneralNames ::= SEQUENCE SIZE (1..MAX) OF GeneralName

GeneralNamesElems = NonEmptySequenceOf GeneralName
GeneralNames = TLV Tag.Sequence GeneralNamesElems

RawGeneralNamesElems : Raw GeneralNamesElems
RawGeneralNamesElems = RawBoundedSequenceOf RawGeneralName 1

RawGeneralNames : Raw GeneralNames
RawGeneralNames = RawTLV _ RawGeneralNamesElems
