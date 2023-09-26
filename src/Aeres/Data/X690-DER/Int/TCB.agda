{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Grammar.Definitions.NonMalleable
open import Aeres.Prelude
open import Relation.Nullary.Implication

module Aeres.Data.X690-DER.Int.TCB where

open Aeres.Grammar.Definitions.NonMalleable UInt8

{- T-REC-X.690-202102-I!!PDF-E.pdf
8.3 Encoding of an integer value

8.3.1 The encoding of an integer value shall be primitive. The contents octets
      shall consist of one or more octets.

8.3.2 If the contents octets of an integer value encoding consist of more than
      one octet, then the bits of the first octet and bit 8 of the second octet:
      a) shall not all be ones; and
      b) shall not all be zero.
      NOTE – These rules ensure that an integer value is always encoded in the
      smallest possible number of octets.

8.3.3 The contents octets shall be a two's complement binary number equal to the
      integer value, and consisting of bits 8 to 1 of the first octet, followed
      by bits 8 to 1 of the second octet, followed by bits 8 to 1 of each octet
      in turn up to and including the last octet of the contents octets.
-}

record IntegerValue (@0 bs : List UInt8) : Set where
  constructor mkIntVal
  field
    @0 bₕ : UInt8
    @0 bₜ : List UInt8
    @0 minRep : True (Base256.twosComplementMinRep? bₕ bₜ)
    val : Singleton (Base256.twosComplement (bₕ ∷ bₜ))
    @0 bs≡ : bs ≡ bₕ ∷ bₜ

Int : @0 List UInt8 → Set
Int = TLV Tag.Integer IntegerValue

getVal : ∀ {@0 bs} → Int bs → ℤ
getVal = Singleton.x ∘ IntegerValue.val ∘ TLV.val

RawIntegerValue : Raw IntegerValue
Raw.D RawIntegerValue = ℤ
Raw.to RawIntegerValue = uncurry─ (Singleton.x ∘ IntegerValue.val)

RawInt : Raw Int
RawInt = RawTLV RawIntegerValue
