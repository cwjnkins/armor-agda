{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.DirectoryString.TCB
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.SequenceOf.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Prelude

module Aeres.Data.X509.RDN.TCB where

record RDNATVFields (@0 bs : List UInt8) : Set where
  constructor mkRDNATVFields
  field
    @0 {o v} : List UInt8
    oid : OID o
    val : DirectoryString v
    @0 bs≡  : bs ≡ o ++ v

RDNATV : @0 List UInt8 → Set
RDNATV xs = TLV Tag.Sequence RDNATVFields xs

RDNElems : @0 List UInt8 → Set
RDNElems = NonEmptySequenceOf RDNATV

RDN : @0 List UInt8 → Set
RDN = TLV Tag.Sett RDNElems

RDNSeq : @0 List UInt8 → Set
RDNSeq = Seq RDN

getSeqLen : ∀ {@0 bs} → RDNSeq bs → ℕ
getSeqLen (mkTLV len val len≡ bs≡) = lengthSequence val
