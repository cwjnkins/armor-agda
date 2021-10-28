{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

import Aeres.Data.X509.Properties.DirectoryString
import Aeres.Data.X509.Properties.GeneralName
import Aeres.Data.X509.Properties.Length
import Aeres.Data.X509.Properties.MonthDayHourMinSecFields
import Aeres.Data.X509.Properties.OIDSub
import Aeres.Data.X509.Properties.Primitives
import Aeres.Data.X509.Properties.PublicKeyFields
import Aeres.Data.X509.Properties.TLV
import Aeres.Data.X509.Properties.Time
import Aeres.Data.X509.Properties.ValidityFields

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

module OIDSub            = Aeres.Data.X509.Properties.OIDSub
module PublicKeyFields   = Aeres.Data.X509.Properties.PublicKeyFields
module GeneralName       = Aeres.Data.X509.Properties.GeneralName
module DirectoryString   = Aeres.Data.X509.Properties.DirectoryString
module MonthDayHourMinSecFields = Aeres.Data.X509.Properties.MonthDayHourMinSecFields

-- Finished lemmas
module Length     = Aeres.Data.X509.Properties.Length
module Primitives = Aeres.Data.X509.Properties.Primitives
module TLV        = Aeres.Data.X509.Properties.TLV
module Time       = Aeres.Data.X509.Properties.Time
