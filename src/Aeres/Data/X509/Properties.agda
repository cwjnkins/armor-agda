{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

import Aeres.Data.X509.Properties.AKIFieldsSeqFields
import Aeres.Data.X509.Properties.AccessMethod
import Aeres.Data.X509.Properties.AccessDescFields
import Aeres.Data.X509.Properties.BCFieldsSeqFields
import Aeres.Data.X509.Properties.DisplayText
import Aeres.Data.X509.Properties.DistPointFields
import Aeres.Data.X509.Properties.DistPointNameChoice
import Aeres.Data.X509.Properties.DirectoryString
import Aeres.Data.X509.Properties.Extension
import Aeres.Data.X509.Properties.GeneralName
import Aeres.Data.X509.Properties.Length
import Aeres.Data.X509.Properties.MonthDayHourMinSecFields
import Aeres.Data.X509.Properties.OIDSub
import Aeres.Data.X509.Properties.Primitives
import Aeres.Data.X509.Properties.PolicyQualifierInfoFields
import Aeres.Data.X509.Properties.PublicKeyFields
import Aeres.Data.X509.Properties.TLV
import Aeres.Data.X509.Properties.Time
import Aeres.Data.X509.Properties.UserNoticeFields
import Aeres.Data.X509.Properties.ValidityFields

module Aeres.Data.X509.Properties where

-- Dumping ground for unfinished lemmas (place these proofs of these in the
-- appropriate file under Properties/)

module NonEmpty where
  open import Aeres.Binary
  open Base256
  open import Aeres.Grammar.Definitions Dig
  open import Aeres.Data.X509

module NonNesting where
  open import Aeres.Binary
  open Base256
  open import Aeres.Grammar.Definitions Dig
  open import Aeres.Data.X509

-- Unfinished lemmas
module PolicyQualifierInfoFields = Aeres.Data.X509.Properties.PolicyQualifierInfoFields

-- Finished lemmas
module AKIFieldsSeqFields        = Aeres.Data.X509.Properties.AKIFieldsSeqFields
module AccessMethod              = Aeres.Data.X509.Properties.AccessMethod
module AccessDescFields          = Aeres.Data.X509.Properties.AccessDescFields
module BCFieldsSeqFields         = Aeres.Data.X509.Properties.BCFieldsSeqFields
module DisplayText               = Aeres.Data.X509.Properties.DisplayText
module DistPointFields           = Aeres.Data.X509.Properties.DistPointFields
module DistPointNameChoice       = Aeres.Data.X509.Properties.DistPointNameChoice
module DirectoryString           = Aeres.Data.X509.Properties.DirectoryString
module Extension                 = Aeres.Data.X509.Properties.Extension
module GeneralName               = Aeres.Data.X509.Properties.GeneralName
module Length                    = Aeres.Data.X509.Properties.Length
module MonthDayHourMinSecFields  = Aeres.Data.X509.Properties.MonthDayHourMinSecFields
module OIDSub                    = Aeres.Data.X509.Properties.OIDSub
module Primitives                = Aeres.Data.X509.Properties.Primitives
module PublicKeyFields           = Aeres.Data.X509.Properties.PublicKeyFields
module TLV                       = Aeres.Data.X509.Properties.TLV
module Time                      = Aeres.Data.X509.Properties.Time
module UserNoticeFields          = Aeres.Data.X509.Properties.UserNoticeFields
module ValidityFields            = Aeres.Data.X509.Properties.ValidityFields
