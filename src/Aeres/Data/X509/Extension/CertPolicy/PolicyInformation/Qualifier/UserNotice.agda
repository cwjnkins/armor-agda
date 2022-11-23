{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.Eq
import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.NoticeReference
import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.Parser
import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.Properties
import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.TCB

module Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice where

module UserNotice where
  open Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.Eq              public
  open Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.NoticeReference public
  open Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.Properties      public

open Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.Parser public
open Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.TCB    public
