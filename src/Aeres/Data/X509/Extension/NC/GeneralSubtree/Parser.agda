{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.NC.GeneralSubtree.Properties
open import Aeres.Data.X509.Extension.NC.GeneralSubtree.TCB
open import Aeres.Data.X509.GeneralNames.GeneralName
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.SequenceOf
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.Extension.NC.GeneralSubtree.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.IList       UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Seq         UInt8

private
  here' = "X509: Extension: NC: GeneralSubtree"

parseExactLengthGeneralSubtrees : (n : ℕ) → Parser (Logging ∘ Dec) (ExactLength (GeneralSubtrees) n)
parseExactLengthGeneralSubtrees n =
  parseIListNonEmpty (tell $ here' String.++ ": underflow")
    _ TLV.nonempty TLV.nosubstrings
      (parseTLV _ "GeneralSubtree" _ helper) n
  where
  helper : (n : ℕ) → Parser (Logging ∘ Dec) (ExactLength (GeneralSubtreeFields) n)
  helper n =
    parseEquivalent
      (Iso.transEquivalent
        (Iso.symEquivalent Distribute.exactLength-&)
        (Parallel.equivalent₁ equivalentGeneralSubtreeFields))
      (parse&ᵈ (Parallel.nosubstrings₁ GeneralName.nosubstrings)
        (Parallel.Length≤.unambiguous _ GeneralName.unambiguous)
        (parse≤ n parseGeneralName GeneralName.nosubstrings (tell $ here' String.++ ": underflow"))
        λ where
          {bs} (singleton read read≡) _ →
            subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength _ (n - x))) read≡
            (Option.parseOption₂ TLV.nosubstrings TLV.nosubstrings (TLV.noconfusion λ ())
              (parseTLV _ "MinBaseDistance" _ Int.parseValue)
              (parseTLV _ "MaxBaseDistance" _ Int.parseValue)
              (tell $ here' String.++ ": underflow")
              (n - read)))

