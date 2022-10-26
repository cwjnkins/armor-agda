{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
open import Aeres.Prelude

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8

module Aeres.Data.X509.SignAlg.TCB where

record SignAlgFields (@0 bs : List UInt8) : Set where
  constructor mkSignAlgFields
  field
    @0 {o p} : List UInt8
    signOID : OID o
    param : Option (NotEmpty OctetStringValue) p
    @0 bs≡  : bs ≡ o ++ p

SignAlg : (@0 _ : List UInt8) → Set
SignAlg xs = TLV Tag.Sequence SignAlgFields xs

getSignAlgOIDbs : ∀ {@0 bs} → SignAlg bs → List UInt8
getSignAlgOIDbs = Singleton.x ∘ OID.serialize ∘ SignAlgFields.signOID ∘ TLV.val
