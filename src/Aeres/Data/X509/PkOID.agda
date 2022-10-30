{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.OID
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Prelude

module Aeres.Data.X509.PkOID where

RsaEncPk : List UInt8
RsaEncPk = Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 1 ]

EcPk : List UInt8
EcPk = Tag.ObjectIdentifier ∷ # 7 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 206 ∷ # 61 ∷ # 2 ∷ [ # 1 ]

Supported : List (List UInt8)
Supported = RsaEncPk ∷ [ EcPk ]

module Properties where
  open import Aeres.Grammar.Parser UInt8

  supportedOIDs : All OID Supported
  supportedOIDs =
      Success.value (toWitness{Q = Logging.val (runParser parseOID RsaEncPk)} tt)
    ∷ Success.value (toWitness{Q = Logging.val (runParser parseOID EcPk)} tt)
    ∷ []
