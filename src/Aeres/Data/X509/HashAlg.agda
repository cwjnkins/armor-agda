{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.HashAlg.Parser
import Aeres.Data.X509.HashAlg.TCB

module Aeres.Data.X509.HashAlg where

open Aeres.Data.X509.HashAlg.Parser public

module HashAlg where
  open Aeres.Data.X509.HashAlg.TCB   public
