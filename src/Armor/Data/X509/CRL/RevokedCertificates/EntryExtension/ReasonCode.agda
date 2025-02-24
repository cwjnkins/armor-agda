{-# OPTIONS --erasure #-}
import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.ReasonCode.Parser
import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.ReasonCode.TCB
import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.ReasonCode.Properties

module Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.ReasonCode where

open Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.ReasonCode.Parser public
open Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.ReasonCode.TCB    public

module ReasonCode where
  open Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.ReasonCode.Properties public
