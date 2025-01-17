import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.CertIssuer
import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.InvalidityDate
import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.ReasonCode
import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.Parser
import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.Properties
import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.TCB


module Armor.Data.X509.CRL.RevokedCertificates.EntryExtension where

open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.Parser public
open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.TCB    public
  hiding (module EntryExtension)

module EntryExtension where
  open Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.CertIssuer      public
  open Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.InvalidityDate           public
  open Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.ReasonCode
  open Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.Properties    public
  open Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.TCB           public
