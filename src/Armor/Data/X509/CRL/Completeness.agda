open import Armor.Binary
open import Armor.Data.X509.CRL.CertList
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parser
  hiding (module Generic)
open import Armor.Prelude

module Armor.Data.X509.CRL.Completeness where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parser      UInt8

private 
  module Generic where
    open import Armor.Grammar.Parser.Completeness UInt8 public
    open Proofs (Logging ∘ Dec) Logging.val public

open Generic.Definitions (Logging ∘ Dec) Logging.val

@0 soundness : Sound parseCertList
soundness = Generic.soundness parseCertList

@0 weakCompleteness : WeaklyComplete parseCertList
weakCompleteness = Generic.weakCompleteness parseCertList

@0 strongCompleteness : StronglyComplete parseCertList
strongCompleteness = Generic.strongCompleteness parseCertList
                       CertList.unambiguous TLV.nosubstrings
