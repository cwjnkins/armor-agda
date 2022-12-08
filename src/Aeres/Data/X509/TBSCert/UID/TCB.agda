{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.BitString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Prelude

module Aeres.Data.X509.TBSCert.UID.TCB where

IssUID : (@0 _ : List UInt8) → Set
IssUID xs = TLV Tag.A81 BitStringValue xs

SubUID : (@0 _ : List UInt8) → Set
SubUID xs = TLV Tag.A82 BitStringValue xs
