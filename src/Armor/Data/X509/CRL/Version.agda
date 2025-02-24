{-# OPTIONS --erasure #-}
import Armor.Data.X509.CRL.Version.Eq
import Armor.Data.X509.CRL.Version.Parser
import Armor.Data.X509.CRL.Version.Properties
import Armor.Data.X509.CRL.Version.TCB

module Armor.Data.X509.CRL.Version where

open Armor.Data.X509.CRL.Version.TCB    public
open Armor.Data.X509.CRL.Version.Parser    public

module Version where
  open Armor.Data.X509.CRL.Version.Eq         public
  open Armor.Data.X509.CRL.Version.TCB     public
  open Armor.Data.X509.CRL.Version.Properties public
