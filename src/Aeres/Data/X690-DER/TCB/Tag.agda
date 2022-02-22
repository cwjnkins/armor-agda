{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Prelude

module Aeres.Data.X690-DER.TCB.Tag where

open Base256

Boolean : UInt8
Boolean = # 1

Integer : UInt8
Integer = # 2

Bitstring : UInt8
Bitstring = # 3

OctetString : UInt8
OctetString = # 4

Null : UInt8
Null = # 5

ObjectIdentifier : UInt8
ObjectIdentifier = # 6

UTCTime : UInt8
UTCTime = # 23

GeneralizedTime : UInt8
GeneralizedTime = # 24

Sequence : UInt8
Sequence = # 48

Sett : UInt8
Sett = # 49
