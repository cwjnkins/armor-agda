open import Aeres.Binary
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Data.X509.Name.RDN.Properties as RDN
open import Aeres.Data.X509.Name.RDN.TCB
open import Aeres.Data.X509.Name.TCB
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.Name.Properties where

open Aeres.Grammar.Definitions UInt8

@0 unambiguous : Unambiguous Name
unambiguous = TLV.unambiguous (SequenceOf.unambiguous RDN.unambiguous TLV.nonempty TLV.nosubstrings)

@0 nonmalleable : NonMalleable RawName
nonmalleable = TLV.nonmalleable {R = RawSequenceOf RawRDN} (SequenceOf.nonmalleable {R = RawRDN} TLV.nonempty TLV.nosubstrings RDN.nonmalleable)
