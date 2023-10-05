{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.GeneralName
open import Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.Name
open import Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.TCB
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Seq         UInt8

Rep = &ₚ (Option DistPointName) (&ₚ (Option ReasonFlags) (Option CrlIssuer))

equivalent : Equivalent Rep DistPointFields
proj₁ equivalent (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ sndₚ₁ refl) refl) = mkDistPointFields fstₚ₁ fstₚ₂ sndₚ₁ refl
proj₂ equivalent (mkDistPointFields crldp crldprsn crlissr bs≡) = mk&ₚ crldp (mk&ₚ crldprsn crlissr refl) bs≡

iso : Iso Rep DistPointFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ sndₚ₁ refl) refl) = refl
proj₂ (proj₂ iso) (mkDistPointFields crldp crldprsn crlissr refl) = refl

@0 unambiguous : Unambiguous DistPoint
unambiguous =
  TLV.unambiguous (Iso.unambiguous iso
    (Unambiguous.option₃&₂
      (Name.unambiguous) TLV.nosubstrings TLV.nonempty
      (TLV.unambiguous BitString.unambiguous) TLV.nosubstrings TLV.nonempty
      (TLV.unambiguous GeneralName.GeneralNamesElems.unambiguous) TLV.nonempty
      (TLV.noconfusion (λ ())) (TLV.noconfusion λ ()) (TLV.noconfusion λ ())))

postulate
  @0 nonmalleable : NonMalleable RawDistPoint
-- nonmalleable = TLV.nonmalleable {!!}
