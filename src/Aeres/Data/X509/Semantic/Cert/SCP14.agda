open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Extension.TCB.OIDs as OIDs
open import Aeres.Data.X509.Semantic.Cert.Utils
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
open import Aeres.Grammar.IList as IList
open import Aeres.Prelude

module Aeres.Data.X509.Semantic.Cert.SCP14 where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2
-- A certificate MUST NOT include more than one instance of a particular Extension.

SCP14 : ∀ {@0 bs} → Cert bs → Set
SCP14 c = List.Unique _≟_ (getExtensionsOIDList (Cert.getExtensionsList c))

scp14 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP14 c)
scp14 c = List.unique? _≟_ (getExtensionsOIDList (Cert.getExtensionsList c))
