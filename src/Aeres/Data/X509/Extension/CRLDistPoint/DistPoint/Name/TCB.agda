{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.GeneralName.TCB
open import Aeres.Data.X509.RDN.TCB
open import Aeres.Data.X690-DER.BitString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.Name.TCB where

FullName : @0 List UInt8 → Set
FullName xs = TLV Tag.AA0 GeneralNamesElems xs

NameRTCrlIssuer : @0 List UInt8 → Set
NameRTCrlIssuer xs = TLV Tag.AA1 RDNElems xs

data DistPointNameChoice : @0 List UInt8 → Set where
  fullname : ∀ {@0 bs} → FullName bs → DistPointNameChoice bs
  nameRTCrlissr : ∀ {@0 bs} → NameRTCrlIssuer bs → DistPointNameChoice bs

DistPointName : @0 List UInt8 → Set
DistPointName xs = TLV Tag.AA0 DistPointNameChoice xs
