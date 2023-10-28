{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.NC.GeneralSubtree.Properties
open import Aeres.Data.X509.Extension.NC.GeneralSubtree.TCB
open import Aeres.Data.X509.GeneralNames.GeneralName
open import Aeres.Data.X690-DER.Default
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.Sequence
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
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
      (parseTLV _ here' _ helper) n
  where
  B = &ₚ (Default MinBaseDistance defaultMinBaseDistance) (Option MaxBaseDistance)
  equiv
    : ∀ n
      → Equivalent
          (&ₚᵈ (Length≤ GeneralName n) (λ {bs} _ → ExactLength B (n - length bs)))
           (ExactLength GeneralSubtreeFields n)
  equiv n =
    (Iso.transEquivalent
      (Iso.symEquivalent Distribute.exactLength-&)
      (Parallel.equivalent₁ equivalentGeneralSubtreeFields))

  p₂ : {@0 bs : List UInt8} → Singleton (length bs) → ∀ n → Parser (Logging ∘ Dec) (ExactLength B (n - length bs))
  p₂ (singleton r r≡) n =
    subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength B (n - x)))
      r≡
      (Sequence.parseDefaultOption _ here'
        Int.[ _ ]unambiguous TLV.nosubstrings
        TLV.nosubstrings (TLV.noconfusion λ ())
        (Int.[_]parse (here' String.++ ": MinBaseDistance") _)
        (Int.[_]parse (here' String.++ ": MaxBaseDistnace") _)
        (n - r))

  helper : (n : ℕ) → Parser (Logging ∘ Dec) (ExactLength (GeneralSubtreeFields) n)
  helper n =
    parseEquivalent (equiv n)
      (parse&ᵈ
        (Parallel.nosubstrings₁ GeneralName.nosubstrings)
        (Parallel.Length≤.unambiguous _ GeneralName.unambiguous)
        (parse≤ n parseGeneralName GeneralName.nosubstrings (tell $ here' String.++ ": underflow"))
        λ {bs} s a → p₂{bs} s n)
