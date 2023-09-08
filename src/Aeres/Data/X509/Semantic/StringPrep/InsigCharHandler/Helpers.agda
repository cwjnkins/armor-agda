{-# OPTIONS --subtyping --sized-types #-}

open import Data.Nat.DivMod
import      Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Grammar.Definitions
open import Aeres.Grammar.IList
import      Aeres.Grammar.Sum
open import Aeres.Prelude

open import Aeres.Data.Unicode.UTF8
open import Aeres.Data.Unicode.UTF8.Serializer
open import Aeres.Data.Unicode.UTF8.Trie
import      Data.Nat.Properties as Nat
open import Data.These.Base

module Aeres.Data.X509.Semantic.StringPrep.InsigCharHandler.Helpers where

open Aeres.Binary
open Base256
open Aeres.Grammar.Definitions Dig


spaceUTF8 : Exists─ (List UInt8) UTF8
spaceUTF8 = _ , cons (mkIListCons (utf81 (mkUTF8Char1 (# 32) (toWitness {Q = 32 <? 128 } tt) refl)) nil refl)

checkOnlySpaces : ∀ {@0 bs} → UTF8 bs → Bool
checkOnlySpaces nil = true
checkOnlySpaces (cons (mkIListCons (utf81 (mkUTF8Char1 b₁ b₁range bs≡₁)) tail₁ bs≡))
  with toℕ b₁ ≟ 32
... | no ¬p = false
... | yes p = checkOnlySpaces tail₁
checkOnlySpaces (cons (mkIListCons (utf82 x) tail₁ bs≡)) = false
checkOnlySpaces (cons (mkIListCons (utf83 x) tail₁ bs≡)) = false
checkOnlySpaces (cons (mkIListCons (utf84 x) tail₁ bs≡)) = false

lstripUTF8 : ∀ {@0 bs} → (bsname : UTF8 bs) → Exists─ (List UInt8) (Σₚ UTF8 (λ xs a → lengthIList _ a ≤ lengthIList _ bsname))
lstripUTF8 nil = _ , (Aeres.Grammar.Definitions.mk×ₚ nil z≤n refl)
lstripUTF8 a@(cons (mkIListCons (utf81 (mkUTF8Char1 b₁ b₁range bs≡₁)) tail₁ bs≡))
  with toℕ b₁ ≟ 32
... | no ¬p = _ , (Aeres.Grammar.Definitions.mk×ₚ a (s≤s Nat.≤-refl) refl)
... | yes p
  with lstripUTF8 tail₁
... | fst , Aeres.Grammar.Definitions.mk×ₚ fstₚ₁ sndₚ₁ refl = fst , (Aeres.Grammar.Definitions.mk×ₚ fstₚ₁ (Nat.≤-step sndₚ₁) refl)
lstripUTF8 a@(cons (mkIListCons (utf82 x) tail₁ bs≡)) = _ , (Aeres.Grammar.Definitions.mk×ₚ a (s≤s Nat.≤-refl) refl)
lstripUTF8 a@(cons (mkIListCons (utf83 x) tail₁ bs≡)) = _ , (Aeres.Grammar.Definitions.mk×ₚ a (s≤s Nat.≤-refl) refl)
lstripUTF8 a@(cons (mkIListCons (utf84 x) tail₁ bs≡)) = _ , (Aeres.Grammar.Definitions.mk×ₚ a (s≤s Nat.≤-refl) refl)

lstripUTF8' : ∀ {@0 bs} → (bsname : UTF8 bs) → Exists─ (List UInt8) UTF8
lstripUTF8' bsname
  with lstripUTF8 bsname
... | fst , snd = _ , fstₚ snd

rstripUTF8 : ∀ {@0 bs} → UTF8 bs → Exists─ (List UInt8) UTF8
rstripUTF8 x = reverseIList _ (proj₂ (lstripUTF8' (proj₂ (reverseIList _ x))))

stripUTF8 :  ∀ {@0 bs} → UTF8 bs → Exists─ (List UInt8) UTF8
stripUTF8 x = rstripUTF8 (proj₂ (lstripUTF8' x))

addSpacesStartEnd :  ∀ {@0 bs} → UTF8 bs → Exists─ (List UInt8) UTF8
addSpacesStartEnd x = _ , (appendIList _ (appendIList _ (proj₂ spaceUTF8) x) (proj₂ spaceUTF8))

innerSeqSpaceHelperWF : ∀ {@0 bs ss} → (bsname : UTF8 bs) → Acc _<_ (lengthIList _ bsname) → UTF8 ss → Exists─ (List UInt8) UTF8
innerSeqSpaceHelperWF IList.nil ac x₁ = _ , x₁
innerSeqSpaceHelperWF (cons (mkIListCons (utf81 x@(mkUTF8Char1 b₁ b₁range bs≡₁)) tail₁ bs≡)) (WellFounded.acc rs) x₁
  with toℕ b₁ ≟ 32
... | no ¬p = innerSeqSpaceHelperWF tail₁ (rs (lengthIList _ tail₁) Nat.≤-refl) (appendIList _ x₁ (cons (mkIListCons (utf81 x) nil refl)))
... | yes p
  with lstripUTF8 tail₁
... | fst , Aeres.Grammar.Definitions.mk×ₚ fstₚ₁ sndₚ₁ bs≡₂ = innerSeqSpaceHelperWF fstₚ₁ (rs (lengthIList _ fstₚ₁) (s≤s sndₚ₁)) (((appendIList _ x₁ (appendIList _ (proj₂ spaceUTF8) (proj₂ spaceUTF8)))))
innerSeqSpaceHelperWF (cons (mkIListCons (utf82 x) tail₁ bs≡)) (WellFounded.acc rs) x₁ =
  innerSeqSpaceHelperWF tail₁ (rs (lengthIList _ tail₁) Nat.≤-refl) (appendIList _ x₁ (cons (mkIListCons (utf82 x) nil refl)))
innerSeqSpaceHelperWF (cons (mkIListCons (utf83 x) tail₁ bs≡)) (WellFounded.acc rs) x₁ =
  innerSeqSpaceHelperWF tail₁ (rs (lengthIList _ tail₁) Nat.≤-refl) (appendIList _ x₁ (cons (mkIListCons (utf83 x) nil refl)))
innerSeqSpaceHelperWF (cons (mkIListCons (utf84 x) tail₁ bs≡)) (WellFounded.acc rs) x₁ =
  innerSeqSpaceHelperWF tail₁ (rs (lengthIList _ tail₁) Nat.≤-refl) (appendIList _ x₁ (cons (mkIListCons (utf84 x) nil refl)))

innerSeqSpaceHelper : ∀ {@0 bs ss} → (bsname : UTF8 bs) → UTF8 ss → Exists─ (List UInt8) UTF8
innerSeqSpaceHelper bsname = innerSeqSpaceHelperWF bsname (<-wellFounded _)
  where open import Data.Nat.Induction
