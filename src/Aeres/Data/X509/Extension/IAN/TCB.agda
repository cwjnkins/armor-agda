{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.GeneralName.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Prelude

module Aeres.Data.X509.Extension.IAN.TCB where

IANFields : @0 List UInt8 → Set
IANFields xs = TLV Tag.OctetString GeneralNames xs
