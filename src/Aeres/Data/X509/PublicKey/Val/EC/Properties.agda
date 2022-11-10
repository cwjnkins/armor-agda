{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Val.EC.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.EC.Properties where

open Aeres.Grammar.Definitions UInt8

@0 nonnesting : NonNesting ECBitString
nonnesting = nonnesting×ₚ₁ TLV.nonnesting
