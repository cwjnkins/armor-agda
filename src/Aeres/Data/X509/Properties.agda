{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

import Aeres.Data.X509.Properties.AccessMethod
import Aeres.Data.X509.Properties.AccessDescFields
import Aeres.Data.X509.Properties.BCFieldsSeqFields
import Aeres.Data.X509.Properties.CertFields
import Aeres.Data.X509.Properties.DistPointFields
import Aeres.Data.X509.Properties.DistPointNameChoice
import Aeres.Data.X509.Properties.Extension
import Aeres.Data.X509.Properties.GeneralSubtreeFields
import Aeres.Data.X509.Properties.NCFieldsSeqFields
import Aeres.Data.X509.Properties.PCFieldsSeqFields
import Aeres.Data.X509.Properties.PolicyMapFields
import Aeres.Data.X509.Properties.TBSCertFields

module Aeres.Data.X509.Properties where

-- Dumping ground for unfinished lemmas (place these proofs of these in the
-- appropriate file under Properties/)

module NonEmpty where
  open import Aeres.Binary
  open Base256
  open import Aeres.Grammar.Definitions UInt8
  open import Aeres.Data.X509

module NonNesting where
  open import Aeres.Binary
  open Base256
  open import Aeres.Grammar.Definitions UInt8
  open import Aeres.Data.X509

-- Finished lemmas
module AccessMethod              = Aeres.Data.X509.Properties.AccessMethod
module AccessDescFields          = Aeres.Data.X509.Properties.AccessDescFields
module BCFieldsSeqFields         = Aeres.Data.X509.Properties.BCFieldsSeqFields
module CertFields                = Aeres.Data.X509.Properties.CertFields
module DistPointFields           = Aeres.Data.X509.Properties.DistPointFields
module DistPointNameChoice       = Aeres.Data.X509.Properties.DistPointNameChoice
module Extension                 = Aeres.Data.X509.Properties.Extension
module GeneralSubtreeFields      = Aeres.Data.X509.Properties.GeneralSubtreeFields
module NCFieldsSeqFields         = Aeres.Data.X509.Properties.NCFieldsSeqFields
module PCFieldsSeqFields         = Aeres.Data.X509.Properties.PCFieldsSeqFields
module PolicyMapFields           = Aeres.Data.X509.Properties.PolicyMapFields
module TBSCertFields             = Aeres.Data.X509.Properties.TBSCertFields
