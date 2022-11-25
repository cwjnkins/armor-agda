{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.SignAlg.DSA.TCB
  using (DSA-Like)
import      Aeres.Data.X509.SignAlg.DSA.Properties as DSA
import      Aeres.Data.X509.SignAlg.TCB.OIDs as OIDs
open import Aeres.Data.X509.SignAlg.ECDSA.TCB
open import Aeres.Data.X690-DER.OID.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.SignAlg.ECDSA.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

@0 unambiguous : Unambiguous Supported
unambiguous =
  unambiguousSum (DSA.DSA-Like.unambiguous _)
    (unambiguousSum (DSA.DSA-Like.unambiguous _)
      (unambiguousSum (DSA.DSA-Like.unambiguous _)
        (unambiguousSum (DSA.DSA-Like.unambiguous _)
          (DSA.DSA-Like.unambiguous _)
          (DSA.DSA-Like.noConfusion _ _))
        (NoConfusion.sumₚ {A = SHA256}
          (DSA.DSA-Like.noConfusion _ _)
          (DSA.DSA-Like.noConfusion _ _)))
      (NoConfusion.sumₚ{A = SHA224}
        (DSA.DSA-Like.noConfusion _ _)
          (NoConfusion.sumₚ {A = SHA224} (DSA.DSA-Like.noConfusion _ _)
            (DSA.DSA-Like.noConfusion _ _))))
    (NoConfusion.sumₚ {A = SHA1} (DSA.DSA-Like.noConfusion _ _)
      (NoConfusion.sumₚ {A = SHA1} (DSA.DSA-Like.noConfusion _ _)
        (NoConfusion.sumₚ {A = SHA1} (DSA.DSA-Like.noConfusion _ _) (DSA.DSA-Like.noConfusion _ _))))
