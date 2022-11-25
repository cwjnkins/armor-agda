{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.AIA.AccessDesc.AccessMethod.TCB
open import Aeres.Data.X509.GeneralName.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Prelude

module Aeres.Data.X509.Extension.AIA.AccessDesc.TCB where

record AccessDescFields (@0 bs : List UInt8) : Set where
  constructor mkAccessDescFields
  field
    @0 {acm acl} : List UInt8
    acmethod : AccessMethod acm
    aclocation : GeneralName acl
    @0 bs≡  : bs ≡ acm ++ acl

AccessDesc : @0 List UInt8 → Set
AccessDesc xs = TLV Tag.Sequence  AccessDescFields xs
