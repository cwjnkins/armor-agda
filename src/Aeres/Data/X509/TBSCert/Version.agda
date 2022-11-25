{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.TBSCert.Version.Parser
import Aeres.Data.X509.TBSCert.Version.TCB

module Aeres.Data.X509.TBSCert.Version where

open Aeres.Data.X509.TBSCert.Version.Parser public
open Aeres.Data.X509.TBSCert.Version.TCB    public
  using (Version)

module Version where
  open Aeres.Data.X509.TBSCert.Version.TCB public
    using (getVal)
