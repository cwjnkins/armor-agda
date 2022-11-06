{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier.TCB
import Aeres.Data.X509.HashAlg.TCB              as HashAlg
open import Aeres.Data.X509.HashAlg.TCB.OIDs    as OIDs
import      Aeres.Data.X509.MaskGenAlg.TCB.OIDs as OIDs
import      Aeres.Data.X509.MaskGenAlg.TCB      as MaskGenAlg
open import Aeres.Data.X690-DER.Null.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Sum
-- import      Aeres.Grammar.Option
open import Aeres.Prelude

module Aeres.Data.X509.MaskGenAlg.Properties where

open Aeres.Grammar.Definitions UInt8

module MGF1 where
  open MaskGenAlg.MGF1

  postulate
    nonnestingSupported : NonNesting SupportedHashAlg
