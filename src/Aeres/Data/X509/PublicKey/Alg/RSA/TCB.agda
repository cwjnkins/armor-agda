{-# OPTIONS --subtyping #-}

open import Aeres.Data.X509.AlgorithmIdentifier.TCB
open import Aeres.Data.X509.SignAlg.DSA.TCB
  using (DSA-Like)
import      Aeres.Data.X509.PublicKey.Alg.TCB.OIDs as OIDs
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.TLV.TCB
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.RSA.TCB where

RSA = DSA-Like OIDs.RSA

getOID : ∀ {@0 bs} → RSA bs → Exists─ _ OID
getOID x = -, AlgorithmIdentifierFields.algOID (TLV.val x)
