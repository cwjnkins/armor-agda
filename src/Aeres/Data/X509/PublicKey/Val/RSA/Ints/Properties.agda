open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Val.RSA.Ints.TCB
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.RSA.Ints.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Seq         UInt8

iso : Iso RSAPkIntsFieldsRep RSAPkIntsFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkRSAPkIntsFields nval eval bs≡) = refl

@0 nosubstrings : NoSubstrings RSAPkIntsFields
nosubstrings =
  Iso.nosubstrings equivalent
    (Seq.nosubstrings TLV.nosubstrings TLV.nosubstrings)

@0 unambiguousFields : Unambiguous RSAPkIntsFields
unambiguousFields =
  Iso.unambiguous iso
    (Seq.unambiguous Int.unambiguous TLV.nosubstrings Int.unambiguous)

@0 unambiguous : Unambiguous RSAPkInts
unambiguous = TLV.unambiguous unambiguousFields

@0 nonmalleableFields : NonMalleable RawRSAPkIntsFields
nonmalleableFields =
  Iso.nonmalleable iso RawRSAPkIntsFieldsRep
    (Seq.nonmalleable Int.nonmalleable Int.nonmalleable)

@0 nonmalleable : NonMalleable RawRSAPkInts
nonmalleable = TLV.nonmalleable nonmalleableFields
