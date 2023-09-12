{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.Unicode
open import Aeres.Data.X509.DisplayText.TCB
open import Aeres.Data.X690-DER.Strings
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.DSum
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Aeres.Prelude
import      Data.Nat.Properties as Nat

module Aeres.Data.X509.DisplayText.Parser where

open Aeres.Data.X509.DisplayText.TCB.DisplayText
open Aeres.Grammar.DSum          UInt8
open Aeres.Grammar.Definitions   UInt8
open Aeres.Grammar.Parser        UInt8

private
  here' = "X509: DisplayText: "

parseDisplayText : Parser (Logging ∘ Dec) DisplayText
parseDisplayText =
  DSum.parse underflow notFound parseFail
    (λ x → Vec.head x ∈? _)
    (λ x → ∈-unique (toWitness{Q = unique? _} tt))
    len (λ {x} → p {x})
  where
  underflow = tell $ here' String.++ "underflow reading tag"
  notFound  = tell $ here' String.++ "invalid tag"
  parseFail = tell $ here' String.++ "read tag, but failed to read TLV"

  @0 len : ∀ {xs bs} → (d : DisplayTextChoice xs) → DisplayTextValue{xs} d bs → 1 ≤ length bs
  len {bs = bs} (here px) x = Nat.n≢0⇒n>0 (contraposition (Lemmas.length-0-≡-[] bs) (nonemptyΣₚ₁ TLV.nonempty x))
  len {bs = bs} (there (here px)) x = Nat.n≢0⇒n>0 (contraposition (Lemmas.length-0-≡-[] bs) (nonemptyΣₚ₁ TLV.nonempty x))
  len {bs = bs} (there (there (here px))) x = Nat.n≢0⇒n>0 (contraposition (Lemmas.length-0-≡-[] bs) (nonemptyΣₚ₁ TLV.nonempty x))
  len {bs = bs} (there (there (there (here px)))) x = Nat.n≢0⇒n>0 (contraposition (Lemmas.length-0-≡-[] bs) (nonemptyΣₚ₁ TLV.nonempty x))

  p : {@0 xs : Vec UInt8 1} → (d : DisplayTextChoice xs) → Parser (Logging ∘ Dec) (DisplayTextValue{xs} d)
  p (here px) = parseTLVSizeBound IA5StringValue.size IA5String.sizeUnique 1 200 (here' String.++ ": IA5String") parseIA5String
  p (there (here px)) = parseTLVSizeBound VisibleStringValue.size VisibleString.sizeUnique 1 200 (here' String.++ ": VisibleString") parseVisibleString
  p (there (there (here px))) = parseTLVSizeBound UTF16.size UTF16.sizeUnique 1 200 (here' String.++ ": BMPString") parseBMPString
  p (there (there (there (here px)))) = parseTLVSizeBound UTF8.size UTF8.sizeUnique 1 200 (here' String.++ ": UTF8String") parseUTF8String
