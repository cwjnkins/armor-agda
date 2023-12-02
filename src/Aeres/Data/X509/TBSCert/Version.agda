import Aeres.Data.X509.TBSCert.Version.Eq
import Aeres.Data.X509.TBSCert.Version.Parser
import Aeres.Data.X509.TBSCert.Version.Properties
import Aeres.Data.X509.TBSCert.Version.TCB

module Aeres.Data.X509.TBSCert.Version where

open Aeres.Data.X509.TBSCert.Version.TCB    public
  using (Version ; [0]ExplicitVersion ; v1[0]ExplicitVersion ; Raw[0]ExplicitVersion ; v1 ; v2 ; v3)

module Version where
  open Aeres.Data.X509.TBSCert.Version.Eq         public
  open Aeres.Data.X509.TBSCert.Version.Parser     public
  open Aeres.Data.X509.TBSCert.Version.Properties public
