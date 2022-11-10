{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier.TCB
open import Aeres.Data.X509.PublicKey.Alg.RSA.TCB
import     Aeres.Data.X509.SignAlg.DSA.Properties as DSA
import      Aeres.Data.X509.PublicKey.Alg.TCB.OIDs as OIDs
open import Aeres.Data.X690-DER.Length
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.RSA.Properties where

open Aeres.Grammar.Definitions UInt8

@0 unambiguous : Unambiguous RSA
unambiguous = DSA.unambiguous (mkTLV (Length.shortₛ (# (length OIDs.RSALit))) OIDs.RSA refl refl)
