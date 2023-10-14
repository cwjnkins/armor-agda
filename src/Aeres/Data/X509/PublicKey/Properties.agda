{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg
open import Aeres.Data.X509.PublicKey.Alg.TCB.OIDs
open import Aeres.Data.X509.PublicKey.Val
open import Aeres.Data.X509.PublicKey.TCB
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Seq         UInt8

iso   : Iso PublicKeyFieldsRep PublicKeyFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkPublicKeyFields alg key bs≡) = refl

@0 unambiguous : Unambiguous PublicKey
unambiguous =
  TLV.unambiguous
    (Iso.unambiguous iso
      (Seq.unambiguousᵈ Alg.unambiguous TLV.nosubstrings Val.unambiguous))

postulate
  @0 nonmalleable : NonMalleable RawPublicKey
