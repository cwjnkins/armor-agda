{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.GeneralName
open import Aeres.Data.X509.Decidable.Octetstring
open import Aeres.Data.X509.Decidable.Seq
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.AIAFields where

open Base256

module parseAIAFields where
  here' = "parseAIAFields"

  open ≡-Reasoning


  parseAccessMethod : Parser Dig (Logging ∘ Dec) X509.AccessMethod
  runParser parseAccessMethod xs = do
    no ¬parse₁ ← runParser (parseLit _ (tell $ here' String.++ ": underflow") (tell $ here' String.++ ": mismatched CA Issuer ID") X509.ACMOID.CAISSUERS) xs  
      where yes x → return (yes (mapSuccess _ (λ {xs} eq → X509.caissid {xs} eq) x) )
    no ¬parse₂ ← runParser (parseLit _ (tell $ here' String.++ ": underflow") (tell $ here' String.++ ": mismatched OCSP ID") X509.ACMOID.OCSP) xs 
      where yes x → return (yes (mapSuccess _ (λ {xs} eq → X509.ocspid {xs} eq) x))
    return ∘ no $ λ where
      (success prefix read read≡ (X509.caissid x) suffix ps≡) → contradiction (success _ _ read≡ x _ ps≡) ¬parse₁
      (success prefix read read≡ (X509.ocspid x) suffix ps≡) → contradiction (success _ _ read≡ x _ ps≡) ¬parse₂

  parseAccessDescFields : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength _ X509.AccessDescFields n)
  parseAccessDescFields n = parseExactLength _  Props.AccessDescFields.nonnesting (tell $ here' String.++ ": underflow")
    (parseEquivalent _ Props.AccessDescFields.equivalent (parse& _ Props.AccessMethod.nonnesting parseAccessMethod parseGeneralName)) n

  parseAccessDesc :  Parser Dig (Logging ∘ Dec) X509.AccessDesc
  parseAccessDesc = parseTLV _ "Access Description" _ parseAccessDescFields

  parseAIAFields : Parser Dig (Logging ∘ Dec) X509.AIAFields
  parseAIAFields = parseTLV _ "AIA Fields" _ (parseExactLength _ Props.TLV.nonnesting (tell $ here' String.++ ": underflow")
                     (parseSeq "AIA Fields Elems" _ Props.TLV.nonempty Props.TLV.nonnesting parseAccessDesc) )

open parseAIAFields public using (parseAIAFields)
