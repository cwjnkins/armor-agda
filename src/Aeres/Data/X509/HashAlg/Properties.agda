{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier.TCB
import      Aeres.Data.X509.HashAlg.TCB.OIDs as OIDs
open import Aeres.Data.X690-DER.Null.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
open import Aeres.Prelude

module Aeres.Data.X509.HashAlg.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8

module SHA-Like where
  Rep : @0 List UInt8 → Set
  Rep = {!!}
