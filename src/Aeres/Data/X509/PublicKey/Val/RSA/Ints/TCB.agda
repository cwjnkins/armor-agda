{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.RSA.Ints.TCB where

record RSAPkIntsFields (@0 bs : List UInt8) : Set where
  constructor mkRSAPkIntsFields
  field
    @0 {n e} : List UInt8
    nval : Int n 
    eval : Int e
    @0 bs≡ : bs ≡ n ++ e

RSAPkInts : (@0 _ : List UInt8) → Set
RSAPkInts xs = TLV Tag.Sequence RSAPkIntsFields xs
