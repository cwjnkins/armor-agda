{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.Unicode.UTF8.TCB
import Aeres.Data.Unicode.UTF16.TCB as BMP
  using (size)
open BMP hiding (size)
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.Strings.BMPString.TCB
open import Aeres.Data.X690-DER.Strings.IA5String.TCB
open import Aeres.Data.X690-DER.Strings.UTF8String.TCB
open import Aeres.Data.X690-DER.Strings.VisibleString.TCB
import      Aeres.Grammar.DSum
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.DisplayText.TCB where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.DSum        UInt8

DisplayTextChoice : Vec UInt8 1 → Set
DisplayTextChoice t = Vec.head t ∈ Tag.IA5String ∷ Tag.VisibleString ∷ Tag.BMPString ∷ [ Tag.UTF8String ]

DisplayTextValue : ∀ {xs} → DisplayTextChoice xs → @0 List UInt8 → Set
DisplayTextValue (here px)                  = Σₚ IA5String (TLVSizeBounded IA5StringValue.size 1 200)
DisplayTextValue (there (here px))          = Σₚ VisibleString (TLVSizeBounded VisibleStringValue.size 1 200)
DisplayTextValue (there (there (here px)))  = Σₚ BMPString (TLVSizeBounded BMP.size 1 200)
DisplayTextValue (there (there (there c)))  = Σₚ UTF8String (TLVSizeBounded UTF8.size 1 200)

DisplayText : @0 List UInt8 → Set
DisplayText = DSum DisplayTextChoice λ {xs} → DisplayTextValue{xs}

module DisplayText where
  mkIA5String : ∀ {@0 bs} → Σₚ IA5String (TLVSizeBounded IA5StringValue.size 1 200) bs → DisplayText bs
  mkIA5String s@(mk×ₚ (mkTLV len val len≡ refl) b refl) = mkDSum{look = Vec.[ Tag.IA5String ]} (here refl) s refl

  pattern ia5String     v b l≡ = mkDSum{look = _ ∷ []} (here refl)                         (mk×ₚ v b refl) l≡
  pattern visibleString v b l≡ = mkDSum{look = _ ∷ []} (there (here refl))                 (mk×ₚ v b refl) l≡
  pattern bmpString     v b l≡ = mkDSum{look = _ ∷ []} (there (there (here refl)))         (mk×ₚ v b refl) l≡
  pattern utf8String    v b l≡ = mkDSum{look = _ ∷ []} (there (there (there (here refl)))) (mk×ₚ v b refl) l≡
