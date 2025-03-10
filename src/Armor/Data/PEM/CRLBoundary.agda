{-# OPTIONS --erasure #-}
import Armor.Data.PEM.CRLBoundary.Parser
import Armor.Data.PEM.CRLBoundary.Properties
import Armor.Data.PEM.CRLBoundary.TCB

module Armor.Data.PEM.CRLBoundary where

open Armor.Data.PEM.CRLBoundary.Parser public
open Armor.Data.PEM.CRLBoundary.TCB public
  hiding (module CRLBoundary)

module CRLBoundary where
  open Armor.Data.PEM.CRLBoundary.Properties public
