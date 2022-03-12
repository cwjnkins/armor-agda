{-# OPTIONS --subtyping --sized-types #-}

import      Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Properties
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList as IList
import      Aeres.Grammar.Sum
open import Aeres.Prelude

open import Aeres.Data.UTF8.Parser
open import Aeres.Data.UTF8.Serializer
open import Aeres.Data.UTF8.TCB
open import Aeres.Data.UTF8.Trie
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.Combine
open import Data.These.Base

module Aeres.Data.X509.Semantic.StringPrep.Exec where

open Aeres.Binary
open Base256
open Aeres.Grammar.Definitions Dig

appendUTF8 : Exists─ (List UInt8) UTF8 → Exists─ (List UInt8) UTF8 → Exists─ (List UInt8) UTF8
appendUTF8 (fst , snd) (fst₁ , snd₁) = _ , appendIList snd snd₁

lookupB2Map : ∀ {@0 bs} → UTF8Char bs → Exists─ (List UInt8) UTF8
lookupB2Map x 
  with lookupUTF8Trie (serializeUTF8Char' x) B2Map
... | nothing = _ , (cons (mkIListCons x nil refl))
... | just x₁
  with x₁
... | this x₂ = x₂
... | that x₃ = _ , (cons (mkIListCons x nil refl))
... | these x₂ x₃ = x₂


Transcode : ∀ {@0 bs} → X509.DirectoryString bs → String ⊎ Exists─ (List UInt8) UTF8
Transcode (X509.teletexString x) = inj₁ "error in stringprep : teletexstring not supported" 
Transcode (X509.printableString (Aeres.Grammar.Definitions.mk×ₚ (mkTLV len (X509.mkIA5StringValue (singleton x refl) all<128) len≡ bs≡₁) sndₚ₁ bs≡)) = inj₂ (helper x all<128)
  where
  helper : (ss : List UInt8) → @0 All (Fin._< # 128) ss → Exists─ (List UInt8) UTF8
  helper [] All.[] = _ , nil
  helper (x ∷ xs) (px All.∷ x₁) = _ , (cons (mkIListCons (utf81 (mkUTF8Char1 x px refl)) (proj₂ (helper xs x₁)) refl))
Transcode (X509.universalString (Aeres.Grammar.Definitions.mk×ₚ (mkTLV {v = v} len val len≡ refl) sndₚ₁ refl)) = inj₂ (_ , val)
Transcode (X509.utf8String (Aeres.Grammar.Definitions.mk×ₚ (mkTLV {v = v} len val len≡ refl) sndₚ₁ refl)) = inj₂ (_ , val)
Transcode (X509.bmpString (Aeres.Grammar.Definitions.mk×ₚ (mkTLV {v = v} len val len≡ refl) sndₚ₁ refl)) = inj₂ (_ , val)

postulate
  InitialMapping : ∀ {@0 bs} → UTF8 bs → Exists─ (List UInt8) UTF8

CaseFoldingNFKC : ∀ {@0 bs} → UTF8 bs → Exists─ (List UInt8) UTF8
CaseFoldingNFKC nil = _ , nil
CaseFoldingNFKC (cons (mkIListCons head₁ tail₁ bs≡)) = appendUTF8 (lookupB2Map head₁) (CaseFoldingNFKC tail₁)

postulate
  Prohibit : ∀ {@0 bs} → UTF8 bs → Bool
  InsigCharHandling : ∀ {@0 bs} → UTF8 bs → Exists─ (List UInt8) UTF8

ProcessString : ∀ {@0 bs} → X509.DirectoryString bs → String ⊎ Exists─ (List UInt8) UTF8
ProcessString str
  with Transcode str
... | inj₁ err = inj₁ err
... | inj₂ ts
  with InitialMapping (proj₂ ts)
... | ims
  with CaseFoldingNFKC (proj₂ ims)
... | ms
  with Prohibit (proj₂ ms)
... | true = inj₁ "error in stringprep : prohibitted unicode character present"
... | false = inj₂ (InsigCharHandling (proj₂ ms))

Compare : ∀ {@0 bs₁ bs₂} → X509.DirectoryString bs₁ → X509.DirectoryString bs₂ → Set
Compare x x₁
  with ProcessString x
... | inj₁ err = ⊥
... | inj₂ a
  with ProcessString x₁
... | inj₁ err = ⊥
... | inj₂ b = _≋_ {A = UTF8} (proj₂ a) (proj₂ b)
