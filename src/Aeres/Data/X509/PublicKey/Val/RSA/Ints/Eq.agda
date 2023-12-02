open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Val.RSA.Ints.Properties
open import Aeres.Data.X509.PublicKey.Val.RSA.Ints.TCB
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.RSA.Ints.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Seq         UInt8

instance
  eq≋ : Eq≋ RSAPkIntsFields
  eq≋ =
    Iso.isoEq≋ iso (Eq⇒Eq≋ (Seq.eq&ₚ it it))
