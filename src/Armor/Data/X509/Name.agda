{-# OPTIONS --erasure #-}
import Armor.Data.X509.Name.Parser
import Armor.Data.X509.Name.Properties
import Armor.Data.X509.Name.RDN
import Armor.Data.X509.Name.TCB

module Armor.Data.X509.Name where

open Armor.Data.X509.Name.TCB public
  hiding (getRDNs)

module Name where
  open Armor.Data.X509.Name.Parser     public
  open Armor.Data.X509.Name.Properties public
  open Armor.Data.X509.Name.RDN        public
  open Armor.Data.X509.Name.TCB public
    using (getRDNs)

