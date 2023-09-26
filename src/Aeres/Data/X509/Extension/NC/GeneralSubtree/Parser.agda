{-# OPTIONS --subtyping --allow-unsolved-metas #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.NC.GeneralSubtree.Properties
open import Aeres.Data.X509.Extension.NC.GeneralSubtree.TCB
open import Aeres.Data.X509.GeneralName
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.SequenceOf
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parser
import      Aeres.Grammar.IList
import      Aeres.Grammar.Properties
open import Aeres.Prelude

module Aeres.Data.X509.Extension.NC.GeneralSubtree.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.IList      UInt8
open Aeres.Grammar.Properties  UInt8

private
  here' = "X509: Extension: NC: GeneralSubtree"

parseExactLengthGeneralSubtrees : (n : ℕ) → Parser (Logging ∘ Dec) (ExactLength (GeneralSubtrees) n)
parseExactLengthGeneralSubtrees n =
  parseIListNonEmpty (tell $ here' String.++ ": underflow")
    _ TLV.nonempty TLV.nonnesting
      (parseTLV _ "GeneralSubtree" _ helper) n
  where
  helper : (n : ℕ) → Parser (Logging ∘ Dec) (ExactLength (GeneralSubtreeFields) n)
  helper n =
    parseEquivalent
      (Iso.transEquivalent
        (Iso.symEquivalent Distribute.exactLength-&)
        (equivalent×ₚ equivalent))
      (parse&ᵈ (withinLength-nonnesting GeneralName.nonnesting)
        (withinLength-unambiguous GeneralName.unambiguous)
        (parse≤ n parseGeneralName GeneralName.nonnesting (tell $ here' String.++ ": underflow"))
        λ where
          {bs} (singleton read read≡) _ →
            subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength _ (n - x))) read≡
            (parseOption₂ TLV.nonnesting TLV.nonnesting (TLV.noconfusion λ ())
              (parseTLV _ "MinBaseDistance" _ Int.parseValue)
              (parseTLV _ "MaxBaseDistance" _ Int.parseValue)
              (tell $ here' String.++ ": underflow")
              (n - read)))

