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

Rep : @0 List UInt8 → Set
Rep = &ₚᵈ PublicKeyAlg λ a → PublicKeyVal (proj₂ (Alg.getOID a))

equiv : Equivalent Rep PublicKeyFields
proj₁ equiv (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkPublicKeyFields fstₚ₁ sndₚ₁ bs≡
proj₂ equiv (mkPublicKeyFields alg key bs≡) = mk&ₚ alg key bs≡

iso   : Iso Rep PublicKeyFields
proj₁ iso = equiv
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkPublicKeyFields alg key bs≡) = refl

@0 unambiguous : Unambiguous PublicKey
unambiguous =
  TLV.unambiguous
    (Iso.unambiguous iso
      (Seq.unambiguousᵈ
        Alg.unambiguous
        Alg.nosubstrings
        λ a → Val.unambiguous (proj₂ (Alg.getOID a))))

postulate
  @0 nonmalleable : NonMalleable RawPublicKey
