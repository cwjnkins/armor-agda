{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

import Aeres.Data.X509.Properties.AKIFieldsSeqFields
import Aeres.Data.X509.Properties.AccessMethod
import Aeres.Data.X509.Properties.AccessDescFields
import Aeres.Data.X509.Properties.BCFieldsSeqFields
import Aeres.Data.X509.Properties.CertFields
import Aeres.Data.X509.Properties.CurveFields
import Aeres.Data.X509.Properties.DisplayText
import Aeres.Data.X509.Properties.DistPointFields
import Aeres.Data.X509.Properties.DistPointNameChoice
import Aeres.Data.X509.Properties.DirectoryString
import Aeres.Data.X509.Properties.EcParamsFields
import Aeres.Data.X509.Properties.EcPkAlgFields
import Aeres.Data.X509.Properties.Extension
import Aeres.Data.X509.Properties.GeneralName
import Aeres.Data.X509.Properties.GeneralSubtreeFields
import Aeres.Data.X509.Properties.NCFieldsSeqFields
import Aeres.Data.X509.Properties.NoticeReferenceFields
import Aeres.Data.X509.Properties.PCFieldsSeqFields
import Aeres.Data.X509.Properties.PkAlg
import Aeres.Data.X509.Properties.PkVal
import Aeres.Data.X509.Properties.PolicyMapFields
import Aeres.Data.X509.Properties.PolicyQualifierInfoFields
import Aeres.Data.X509.Properties.PublicKeyFields
import Aeres.Data.X509.Properties.RDNATVFields
import Aeres.Data.X509.Properties.RDNSeq
import Aeres.Data.X509.Properties.RSAPkAlgFields
import Aeres.Data.X509.Properties.RSAPkIntsFields
import Aeres.Data.X509.Properties.RSABitStringFields
import Aeres.Data.X509.Properties.TBSCertFields
import Aeres.Data.X509.Properties.UserNoticeFields

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

-- Finished lemmas
module AKIFieldsSeqFields        = Aeres.Data.X509.Properties.AKIFieldsSeqFields
module AccessMethod              = Aeres.Data.X509.Properties.AccessMethod
module AccessDescFields          = Aeres.Data.X509.Properties.AccessDescFields
module BCFieldsSeqFields         = Aeres.Data.X509.Properties.BCFieldsSeqFields
module CertFields                = Aeres.Data.X509.Properties.CertFields
module CurveFields               = Aeres.Data.X509.Properties.CurveFields
module DistPointFields           = Aeres.Data.X509.Properties.DistPointFields
module DistPointNameChoice       = Aeres.Data.X509.Properties.DistPointNameChoice
module DirectoryString           = Aeres.Data.X509.Properties.DirectoryString
module DisplayText               = Aeres.Data.X509.Properties.DisplayText
module Extension                 = Aeres.Data.X509.Properties.Extension
module EcParamsFields            = Aeres.Data.X509.Properties.EcParamsFields
module EcPkAlgFields             = Aeres.Data.X509.Properties.EcPkAlgFields
module GeneralName               = Aeres.Data.X509.Properties.GeneralName
module GeneralSubtreeFields      = Aeres.Data.X509.Properties.GeneralSubtreeFields
module NCFieldsSeqFields         = Aeres.Data.X509.Properties.NCFieldsSeqFields
module NoticeReferenceFields     = Aeres.Data.X509.Properties.NoticeReferenceFields
module PCFieldsSeqFields         = Aeres.Data.X509.Properties.PCFieldsSeqFields
module PkAlg                     = Aeres.Data.X509.Properties.PkAlg
module PkVal                     = Aeres.Data.X509.Properties.PkVal
module PolicyMapFields           = Aeres.Data.X509.Properties.PolicyMapFields
module PolicyQualifierInfoFields = Aeres.Data.X509.Properties.PolicyQualifierInfoFields
module PublicKeyFields           = Aeres.Data.X509.Properties.PublicKeyFields
module RDNATVFields              = Aeres.Data.X509.Properties.RDNATVFields
module RDNSeq                    = Aeres.Data.X509.Properties.RDNSeq
module RSAPkAlgFields            = Aeres.Data.X509.Properties.RSAPkAlgFields
module RSAPkIntsFields           = Aeres.Data.X509.Properties.RSAPkIntsFields
module RSABitStringFields        = Aeres.Data.X509.Properties.RSABitStringFields
module TBSCertFields             = Aeres.Data.X509.Properties.TBSCertFields
module UserNoticeFields          = Aeres.Data.X509.Properties.UserNoticeFields
