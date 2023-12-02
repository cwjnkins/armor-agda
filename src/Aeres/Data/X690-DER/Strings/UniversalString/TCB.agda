open import Aeres.Binary
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions.NonMalleable
open import Aeres.Data.Unicode.UTF32.TCB
open import Aeres.Prelude

module Aeres.Data.X690-DER.Strings.UniversalString.TCB where

open Aeres.Grammar.Definitions.NonMalleable UInt8

UniversalString : @0 List UInt8 → Set
UniversalString = TLV Tag.UniversalString UTF32

RawUniversalString : Raw UniversalString 
RawUniversalString = RawTLV _ RawUTF32
