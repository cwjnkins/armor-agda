{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER
open import Aeres.Prelude

module Aeres.Data.X509.IA5String.TCB where

record IA5StringValue (@0 bs : List UInt8) : Set where
  constructor mkIA5StringValue
  field
    str : OctetStringValue bs
    @0 all<128 : True (All.all? (Fin._<? (# 128)) (↑ str))

IA5String : (@0 _ : List UInt8) → Set
IA5String xs = TLV Tag.IA5String  IA5StringValue xs

PrintableString : (@0 _ : List UInt8) → Set
PrintableString xs = TLV Tag.PrintableString  IA5StringValue xs
