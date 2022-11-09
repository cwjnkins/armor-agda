{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Val.RSA.Ints.TCB
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.RSA.TCB where

record RSABitStringFields (@0 bs : List UInt8) : Set where
  constructor mkRSABitStringFields
  field
    @0 {neseq} : List UInt8
    z : Singleton ([ # 0 ]) 
    rsane : RSAPkInts neseq
    @0 bs≡ : bs ≡ (Singleton.x z) ++ neseq

RSABitString : @0 List UInt8 → Set
RSABitString xs = TLV Tag.BitString RSABitStringFields xs
