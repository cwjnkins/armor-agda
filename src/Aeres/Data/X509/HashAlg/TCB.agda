{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X509.HashAlg.TCB.OIDs as OIDs
open import Aeres.Data.X690-DER.Null.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.Sequence.DefinedByOID.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Grammar.Definitions.Eq
import      Aeres.Grammar.Definitions.NonMalleable
import      Aeres.Grammar.Option.TCB
import      Aeres.Grammar.Parallel.TCB
open import Aeres.Prelude

module Aeres.Data.X509.HashAlg.TCB where

open Aeres.Grammar.Definitions.Eq           UInt8
open Aeres.Grammar.Definitions.NonMalleable UInt8
open Aeres.Grammar.Option.TCB               UInt8
open Aeres.Grammar.Parallel.TCB             UInt8

SHA-Like-Param : ∀ {@0 bs} → (o : OIDValue bs) → ∀ {@0 bs'} → (o' : OID bs') → @0 List UInt8 → Set
SHA-Like-Param o o' =
      Option Null
  ×ₚ const (_≋_{A = OIDValue} (TLV.val o') o)

RawSHALikeParam : ∀ {@0 bs} (o : OIDValue bs) → Raw₁ RawOID (SHA-Like-Param o)
Raw₁.D (RawSHALikeParam o) x = Raw.D (RawOption RawNull)
Raw₁.to (RawSHALikeParam o) o' p = Raw.to (RawOption RawNull) (fstₚ p)

SHA-Like : {@0 bs : List UInt8} → OIDValue bs → @0 List UInt8 → Set
SHA-Like o = DefinedByOID (SHA-Like-Param o)

RawSHALike : ∀ {@0 bs} (o : OIDValue bs) → Raw (SHA-Like o)
RawSHALike o = RawDefinedByOID (RawSHALikeParam o)

SHA1   = SHA-Like OIDs.SHA1
SHA224 = SHA-Like OIDs.SHA224
SHA256 = SHA-Like OIDs.SHA256
SHA384 = SHA-Like OIDs.SHA384
SHA512 = SHA-Like OIDs.SHA512
