{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.AIA.TCB
open import Aeres.Data.X509.Extension.AKI.TCB
open import Aeres.Data.X509.Extension.BC.TCB
open import Aeres.Data.X509.Extension.CRLDistPoint.TCB
open import Aeres.Data.X509.Extension.CertPolicy.TCB
open import Aeres.Data.X509.Extension.EKU.TCB
open import Aeres.Data.X509.Extension.IAN.TCB
open import Aeres.Data.X509.Extension.INAP.TCB
open import Aeres.Data.X509.Extension.KU.TCB
open import Aeres.Data.X509.Extension.NC.TCB
open import Aeres.Data.X509.Extension.PC.TCB
open import Aeres.Data.X509.Extension.PM.TCB
open import Aeres.Data.X509.Extension.SAN.TCB
open import Aeres.Data.X509.Extension.SKI.TCB
import      Aeres.Data.X509.Extension.TCB.OIDs as OIDs
open import Aeres.Data.X690-DER.Boool.TCB
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
open import Aeres.Data.X690-DER.SequenceOf.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList.TCB
import      Aeres.Grammar.Option
open import Aeres.Prelude

module Aeres.Data.X509.Extension.TCB where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.IList.TCB   UInt8
open Aeres.Grammar.Option      UInt8

supportedExtensions : List (List UInt8)
supportedExtensions =
    OIDs.AKILit ∷ OIDs.SKILit ∷ OIDs.KULit ∷ OIDs.EKULit ∷ OIDs.BCLit ∷ OIDs.IANLit ∷ OIDs.SANLit
  ∷ OIDs.CPOLLit ∷ OIDs.CRLDISTLit ∷ OIDs.NCLit ∷ OIDs.PCLit ∷ OIDs.PMLit ∷ OIDs.INAPLit ∷ [ OIDs.AIALit ]

record ExtensionFields (@0 P : List UInt8 → Set) (A : @0 List UInt8 → Set) (@0 bs : List UInt8) : Set where
  constructor mkExtensionFields
  field
    @0 {oex cex ocex} : List UInt8
    extnId : OID oex
    @0 extnId≡ : P oex -- oex ≡ lit
    crit : Option Boool cex
    extension : A ocex
    @0 bs≡ : bs ≡ oex ++ cex ++ ocex

ExtensionFieldBC      = ExtensionFields (_≡ OIDs.BCLit  )    BCFields
ExtensionFieldKU      = ExtensionFields (_≡ OIDs.KULit  )    KUFields
ExtensionFieldSAN     = ExtensionFields (_≡ OIDs.SANLit )    SANFields
ExtensionFieldCRLDist = ExtensionFields (_≡ OIDs.CRLDISTLit) CRLDistFields
ExtensionFieldCPOL    = ExtensionFields (_≡ OIDs.CPOLLit)    CertPolFields

data SelectExtn : @0 List UInt8 → Set where
  akiextn  : ∀ {@0 bs} → ExtensionFields (_≡ OIDs.AKILit )    AKIFields     bs → SelectExtn bs 
  skiextn  : ∀ {@0 bs} → ExtensionFields (_≡ OIDs.SKILit )    SKIFields     bs → SelectExtn bs 
  kuextn   : ∀ {@0 bs} → ExtensionFieldKU bs                                   → SelectExtn bs 
  ekuextn  : ∀ {@0 bs} → ExtensionFields (_≡ OIDs.EKULit )    EKUFields     bs → SelectExtn bs 
  bcextn   : ∀ {@0 bs} → ExtensionFieldBC bs                                   → SelectExtn bs 
  ianextn  : ∀ {@0 bs} → ExtensionFields (_≡ OIDs.IANLit )    IANFields     bs → SelectExtn bs 
  sanextn  : ∀ {@0 bs} → ExtensionFieldSAN bs                                  → SelectExtn bs 
  cpextn   : ∀ {@0 bs} → ExtensionFieldCPOL bs                                 → SelectExtn bs 
  crlextn  : ∀ {@0 bs} → ExtensionFieldCRLDist bs                              → SelectExtn bs 
  ncextn   : ∀ {@0 bs} → ExtensionFields (_≡ OIDs.NCLit  )    NCFields      bs → SelectExtn bs 
  pcextn   : ∀ {@0 bs} → ExtensionFields (_≡ OIDs.PCLit  )    PCFields      bs → SelectExtn bs 
  pmextn   : ∀ {@0 bs} → ExtensionFields (_≡ OIDs.PMLit  )    PMFields      bs → SelectExtn bs 
  inapextn : ∀ {@0 bs} → ExtensionFields (_≡ OIDs.INAPLit)    INAPFields    bs → SelectExtn bs 
  aiaextn  : ∀ {@0 bs} → ExtensionFields (_≡ OIDs.AIALit )    AIAFields     bs → SelectExtn bs
  other    : ∀ {@0 bs} → ExtensionFields (False ∘ (_∈? supportedExtensions)) OctetString bs → SelectExtn bs

Extension : @0 List UInt8 → Set
Extension xs = TLV Tag.Sequence SelectExtn xs

ExtensionsSeq : @0 List UInt8 → Set
ExtensionsSeq xs = TLV Tag.Sequence (NonEmptySequenceOf Extension) xs

Extensions : @0 List UInt8 → Set
Extensions xs = TLV Tag.AA3  ExtensionsSeq xs

module Extension where
  getBC : ∀ {@0 bs} → Extension bs → Exists─ (List UInt8) (Option ExtensionFieldBC)
  getBC (mkTLV len (bcextn x) len≡ bs≡) = _ , (some x)
  getBC (mkTLV len _ len≡ bs≡) = _ , none

  getKU : ∀ {@0 bs} → Extension bs → Exists─ (List UInt8) (Option ExtensionFieldKU)
  getKU (mkTLV len (kuextn x) len≡ bs≡) = _ , (some x)
  getKU (mkTLV len _ len≡ bs≡) = _ , none

  getSAN : ∀ {@0 bs} → Extension bs → Exists─ (List UInt8) (Option ExtensionFieldSAN)
  getSAN (mkTLV len (sanextn x) len≡ bs≡) = _ , (some x)
  getSAN (mkTLV len _ len≡ bs≡) = _ , none

  getCRLDIST : ∀ {@0 bs} → Extension bs → Exists─ (List UInt8) (Option ExtensionFieldCRLDist)
  getCRLDIST (mkTLV len (crlextn x) len≡ bs≡) = _ , (some x)
  getCRLDIST (mkTLV len _ len≡ bs≡) = _ , none

  getCPOL : ∀ {@0 bs} → Extension bs → Exists─ (List UInt8) (Option ExtensionFieldCPOL)
  getCPOL (mkTLV len (cpextn x) len≡ bs≡) = _ , (some x)
  getCPOL (mkTLV len _ len≡ bs≡) = _ , none

module ExtensionsSeq where
  getBC : ∀ {@0 bs} → ExtensionsSeq bs → Exists─ (List UInt8) (Option ExtensionFieldBC)
  getBC (mkTLV len (mk×ₚ x sndₚ₁ bs≡₁) len≡ bs≡) = helper x
    where
    helper : ∀ {@0 bs} → SequenceOf Extension bs → Exists─ (List UInt8) (Option ExtensionFieldBC)
    helper nil = _ , none
    helper (consIList h t bs≡) = case (Extension.getBC h) of λ where
      (─ .[] , none) → helper t
      y@(fst , some x) → y

  getKU : ∀ {@0 bs} → ExtensionsSeq bs → Exists─ (List UInt8) (Option ExtensionFieldKU)
  getKU (mkTLV len (mk×ₚ x sndₚ₁ bs≡₁) len≡ bs≡) = helper x
    where
    helper : ∀ {@0 bs} → SequenceOf Extension bs → Exists─ (List UInt8) (Option _)
    helper nil = _ , none
    helper (consIList h t bs≡) = case (Extension.getKU h) of λ where
      (─ .[] , none) → helper t
      y@(fst , some x) → y

  getSAN : ∀ {@0 bs} → ExtensionsSeq bs → Exists─ (List UInt8) (Option ExtensionFieldSAN)
  getSAN (mkTLV len (mk×ₚ x sndₚ₁ bs≡₁) len≡ bs≡) = helper x
    where
    helper : ∀ {@0 bs} → SequenceOf Extension bs → Exists─ (List UInt8) (Option _)
    helper nil = _ , none
    helper (consIList h t bs≡) = case (Extension.getSAN h) of λ where
      (─ .[] , none) → helper t
      y@(fst , some x) → y

  getCRLDIST : ∀ {@0 bs} → ExtensionsSeq bs → Exists─ (List UInt8) (Option ExtensionFieldCRLDist)
  getCRLDIST (mkTLV len (mk×ₚ x sndₚ₁ bs≡₁) len≡ bs≡) = helper x
    where
    helper : ∀ {@0 bs} → SequenceOf Extension bs → Exists─ (List UInt8) (Option _)
    helper nil = _ , none
    helper (consIList h t bs≡) = case (Extension.getCRLDIST h) of λ where
      (─ .[] , none) → helper t
      y@(fst , some x) → y

  getCPOL : ∀ {@0 bs} → ExtensionsSeq bs → Exists─ (List UInt8) (Option ExtensionFieldCPOL)
  getCPOL (mkTLV len (mk×ₚ x sndₚ₁ bs≡₁) len≡ bs≡) = helper x
    where
    helper : ∀ {@0 bs} → SequenceOf Extension bs → Exists─ (List UInt8) (Option _)
    helper nil = _ , none
    helper (consIList h t bs≡) = case (Extension.getCPOL h) of λ where
      (─ .[] , none) → helper t
      y@(fst , some x) → y

  getExtensionsList : ∀ {@0 bs} → ExtensionsSeq bs → List (Exists─ (List UInt8) Extension)
  getExtensionsList (mkTLV len (mk×ₚ fstₚ₁ sndₚ₁ bs≡₁) len≡ bs≡) = helper fstₚ₁
    where
    helper : ∀ {@0 bs} → SequenceOf Extension bs → List (Exists─ (List UInt8) Extension)
    helper nil = []
    helper (consIList h t bs≡) = (_ , h) ∷ helper t

module Extensions where
  getBC : ∀ {@0 bs} → Extensions bs → Exists─ (List UInt8) (Option ExtensionFieldBC)
  getBC (mkTLV len val len≡ bs≡) = ExtensionsSeq.getBC val

  getKU : ∀ {@0 bs} → Extensions bs → Exists─ (List UInt8) (Option ExtensionFieldKU)
  getKU (mkTLV len val len≡ bs≡) = ExtensionsSeq.getKU val

  getSAN : ∀ {@0 bs} → Extensions bs → Exists─ (List UInt8) (Option ExtensionFieldSAN)
  getSAN (mkTLV len val len≡ bs≡) = ExtensionsSeq.getSAN val

  getCRLDIST : ∀ {@0 bs} → Extensions bs → Exists─ (List UInt8) (Option ExtensionFieldCRLDist)
  getCRLDIST (mkTLV len val len≡ bs≡) = ExtensionsSeq.getCRLDIST val

  getCPOL : ∀ {@0 bs} → Extensions bs → Exists─ (List UInt8) (Option ExtensionFieldCPOL)
  getCPOL (mkTLV len val len≡ bs≡) = ExtensionsSeq.getCPOL val

  getExtensionsList : ∀ {@0 bs} → Extensions bs → List (Exists─ (List UInt8) Extension)
  getExtensionsList (mkTLV len val len≡ bs≡) = ExtensionsSeq.getExtensionsList val
