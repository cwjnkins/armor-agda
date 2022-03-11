{-# OPTIONS --subtyping --sized-types --allow-unsolved-metas #-}

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

MergeTwoUTF8 : Exists─ (List UInt8) UTF8 → Exists─ (List UInt8) UTF8 → Exists─ (List UInt8) UTF8
MergeTwoUTF8 = {!!}

lookupB2Map : ∀ {@0 bs} → UTF8Char bs → Exists─ (List UInt8) UTF8
lookupB2Map x 
  with lookupUTF8Trie (serializeUTF8Char' x) B2Map
... | nothing = _ , nil
... | just x₁
  with x₁
... | this x₂ = x₂
... | that x₃ = ?
... | these x₂ x₃ = x₂


Transcode : ∀ {@0 bs} → X509.DirectoryString bs → Exists─ (List UInt8) UTF8
Transcode (X509.teletexString x) = _ , nil
Transcode (X509.printableString (Aeres.Grammar.Definitions.mk×ₚ (mkTLV len (X509.mkIA5StringValue (singleton x refl) all<128) len≡ bs≡₁) sndₚ₁ bs≡)) = helper x all<128
  where
  helper : (ss : List UInt8) → @0 All (Fin._< # 128) ss → Exists─ (List UInt8) UTF8
  helper [] All.[] = _ , nil
  helper (x ∷ xs) (px All.∷ x₁) = _ , (cons (IList.mkIListCons (utf81 (mkUTF8Char1 x px refl)) (proj₂ (helper xs x₁)) refl))
Transcode (X509.universalString (Aeres.Grammar.Definitions.mk×ₚ (mkTLV {v = v} len val len≡ refl) sndₚ₁ refl)) = _ , val
Transcode (X509.utf8String (Aeres.Grammar.Definitions.mk×ₚ (mkTLV {v = v} len val len≡ refl) sndₚ₁ refl)) = _ , val
Transcode (X509.bmpString (Aeres.Grammar.Definitions.mk×ₚ (mkTLV {v = v} len val len≡ refl) sndₚ₁ refl)) = _ , val


InitialMapping : ∀ {@0 bs} → UTF8 bs → Exists─ (List UInt8) UTF8
InitialMapping = {!!}


CaseFoldingNFKC : ∀ {@0 bs} → UTF8 bs → Exists─ (List UInt8) UTF8
CaseFoldingNFKC nil = _ , nil
CaseFoldingNFKC (cons (mkIListCons head₁ tail₁ bs≡)) = MergeTwoUTF8 (lookupB2Map head₁) (CaseFoldingNFKC tail₁)


Prohibit : ∀ {@0 bs} → UTF8 bs → Bool
Prohibit = {!!}


InsigCharHandling : ∀ {@0 bs} → UTF8 bs → Exists─ (List UInt8) UTF8
InsigCharHandling = {!!}


ProcessString : ∀ {@0 bs} → X509.DirectoryString bs → Exists─ (List UInt8) UTF8
ProcessString x
  with Transcode x
... | _ , nil = _ , nil
... | _ , cons x₂
  with InitialMapping (cons x₂)
... | _ , nil = _ , nil
... | _ , cons x₃
  with CaseFoldingNFKC (cons x₃)
... | _ , nil = _ , nil
... | _ , cons x₄
  with Prohibit (cons x₄)
... | true = _ , nil
... | false = InsigCharHandling (cons x₄)


Compare : ∀ {@0 bs₁ bs₂} → X509.DirectoryString bs₁ → X509.DirectoryString bs₂ → Set
Compare x x₁
  with ProcessString x
... | _ , nil = ⊥
... | _ , cons x₃
  with ProcessString x₁
... | _ , nil = ⊥
... | _ , cons x₄ =  _≋_ {A = UTF8} (cons x₃) (cons x₄)



-- CheckIfOnlySpaces : ∀ {@0 bs} → UTF8 bs → Bool
-- CheckIfOnlySpaces nil = false
-- CheckIfOnlySpaces (cons (mkIListCons head₁ tail₁ bs≡)) = helper head₁ tail₁
--   where
--   helper : ∀ {bs ps} → UTF8Char bs → UTF8 ps → Bool
--   helper (utf81 (mkUTF8Char1 b₁ b₁range bs≡)) nil
--     with b₁ ≟ # 32
--   ... | z = {!!}
--   helper (utf81 (mkUTF8Char1 b₁ b₁range bs≡)) (cons x) = {!!}
--   helper (utf82 x) x₁ = false
--   helper (utf83 x) x₁ = false
--   helper (utf84 x) x₁ = false




  --   with b₁ ≟ # 32
  -- ... | no ¬p = false
  -- ... | yes p = true ∧ helper {!!}


