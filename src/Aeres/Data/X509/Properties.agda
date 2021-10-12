{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

import Aeres.Data.X509.Properties.Length
import Aeres.Data.X509.Properties.OIDSub
import Aeres.Data.X509.Properties.Primitives
import Aeres.Data.X509.Properties.TLV
import Aeres.Data.X509.Properties.Time

module Aeres.Data.X509.Properties where

-- Dumping ground for unfinished lemmas (place these proofs of these in the
-- appropriate file under Properties/)

module NonEmpty where
  open import Aeres.Binary
  open Base256
  open import Aeres.Grammar.Definitions Dig
  open import Aeres.Data.X509

  postulate
    GeneralName : NonEmpty X509.GeneralName

module NonNesting where
  open import Aeres.Binary
  open Base256
  open import Aeres.Grammar.Definitions Dig
  open import Aeres.Data.X509

  postulate
    MonthDayHourMinSecFields : NonNesting Generic.MonthDayHourMinSecFields
    UtcTimeFields : NonNesting Generic.UtcTimeFields
    GenTimeFields : NonNesting Generic.GenTimeFields
    Time          : NonNesting Generic.Time

    DirectoryString : NonNesting X509.DirectoryString
    ValidityFields  : NonNesting X509.ValidityFields
    GeneralName     : NonNesting X509.GeneralName


-- Finished lemmas
module Length     = Aeres.Data.X509.Properties.Length
module OIDSub     = Aeres.Data.X509.Properties.OIDSub
module Primitives = Aeres.Data.X509.Properties.Primitives
module TLV        = Aeres.Data.X509.Properties.TLV
module Time        = Aeres.Data.X509.Properties.Time
