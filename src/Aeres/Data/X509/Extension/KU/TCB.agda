{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.BitString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Prelude

module Aeres.Data.X509.Extension.KU.TCB where

KUFields : @0 List UInt8 → Set
KUFields xs = TLV Tag.OctetString BitString xs
