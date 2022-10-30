{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X509.PkOID       as PkOID
open import Aeres.Data.X690-DER.Null
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag     as Tag
open import Aeres.Prelude

module Aeres.Data.X509.RSAPkAlg.TCB where

record RSAPkAlgFields (@0 bs : List UInt8) : Set where
  constructor mkRSAPkAlgFields
  field
    @0 {n} : List UInt8
    oid : Singleton PkOID.RsaEncPk
    param : Null n
    @0 bs≡  : bs ≡ Singleton.x oid ++ n

RSAPkAlg : @0 List UInt8 → Set
RSAPkAlg xs = TLV Tag.Sequence RSAPkAlgFields xs


