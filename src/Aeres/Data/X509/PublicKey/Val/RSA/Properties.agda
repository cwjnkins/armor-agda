{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Val.RSA.TCB
open import Aeres.Data.X509.PublicKey.Val.RSA.Ints
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.RSA.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Seq         UInt8

iso : Iso RSABitStringFieldsRep RSABitStringFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ refl sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkRSABitStringFields self rsane bs≡) = refl

@0 nosubstrings : NoSubstrings RSABitStringFields
nosubstrings =
  Iso.nosubstrings equivalent
    (Seq.nosubstrings (λ where _ refl refl → refl) TLV.nosubstrings)

@0 unambiguousFields : Unambiguous RSABitStringFields
unambiguousFields =
  Iso.unambiguous iso
    (Seq.unambiguous
      ≡-unique (λ where _ refl refl → refl)
      Ints.unambiguous)

@0 unambiguous : Unambiguous RSABitString
unambiguous = TLV.unambiguous unambiguousFields

@0 nonmalleableFields : NonMalleable RawRSABitStringFields
nonmalleableFields =
  Iso.nonmalleable iso RawRSABitStringFieldsRep
    (Seq.nonmalleable
      (subsingleton⇒nonmalleable (λ where (─ _ , refl) (─ _ , refl) → refl))
      Ints.nonmalleable)

@0 nonmalleable : NonMalleable RawRSABitString
nonmalleable = TLV.nonmalleable nonmalleableFields
