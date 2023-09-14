{-# OPTIONS --subtyping --sized-types #-}

import      Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Semantic.StringPrep.ExecDS
open import Aeres.Data.X509.Semantic.StringPrep.ExecPS
open import Aeres.Data.X509.Semantic.StringPrep.ExecIS
open import Aeres.Data.X509.Semantic.Cert
open import Aeres.Data.X509.Semantic.Cert.Utils
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
open import Aeres.Grammar.IList as IList
open import Aeres.Prelude

open import  Aeres.Data.X509.RDN.ATV.OIDs

module Aeres.Data.X509.Semantic.Chain where

open Aeres.Binary
open Base256
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Definitions Dig


------- helper functions ------

chainToList : ∀ {@0 bs} → Chain bs  → List (Exists─ (List UInt8) Cert)
chainToList nil = []
chainToList (cons (mkIListCons h t bs≡)) = (_ , h) ∷ helper t
  where
  helper : ∀ {@0 bs} → IList UInt8 Cert bs → List (Exists─ (List UInt8) Cert)
  helper nil = []
  helper (cons (mkIListCons h t bs≡)) = (_ , h) ∷ helper t

CCP2Seq : ∀ {@0 bs} → SequenceOf Cert bs → Set  
CCP2Seq nil = ⊤
CCP2Seq (cons (mkSequenceOf h nil bs≡)) = ⊤
CCP2Seq (cons (mkSequenceOf h (cons x) bs≡)) = Cert.getVersion h ≡ ℤ.+ 2 × CCP2Seq (cons x)

MatchRDNATV : ∀ {@0 bs₁ bs₂} → RDN.ATV bs₁ → RDN.ATV bs₂ → Set
MatchRDNATV (mkTLV len (Sequence.mkOIDDefinedFields oid param bs≡₂) len≡ bs≡) (mkTLV len₁ (Sequence.mkOIDDefinedFields oid₁ param₁ bs≡₃) len≡₁ bs≡₁) = helper oid ((-, TLV.val oid) ∈? Supported) oid₁ ((-, TLV.val oid₁) ∈? Supported)
  where
  helper : ∀ {@0 bs₁ bs₂} → (o₁ : OID bs₁) → (d : Dec ((-, TLV.val o₁) ∈ Supported)) → (o₂ : OID bs₂) → (d : Dec ((-, TLV.val o₂) ∈ Supported)) → Set
  helper o₁ (no ¬p) o₂ (no ¬p₁) = (_≋_ {A = OID} o₁ o₂) × CompareDS {!!} {!!}
  helper o₁ (no ¬p) o₂ (yes p) = ⊥
  helper o₁ (yes p) o₂ (no ¬p) = ⊥
  helper o₁ (yes (here px)) o₂ (yes (here px₁)) = (_≋_ {A = OID} o₁ o₂) × ComparePS {!!} {!!}
  helper o₁ (yes (here px)) o₂ (yes (there p₁)) = ⊥
  helper o₁ (yes (there p)) o₂ (yes (here px)) = ⊥
  helper o₁ (yes (there (here px))) o₂ (yes (there (here px₁))) = (_≋_ {A = OID} o₁ o₂) × ComparePS {!!} {!!}
  helper o₁ (yes (there (here px))) o₂ (yes (there (there p₁))) = ⊥
  helper o₁ (yes (there (there p))) o₂ (yes (there (here px))) = ⊥
  helper o₁ (yes (there (there (here px)))) o₂ (yes (there (there (here px₁)))) = (_≋_ {A = OID} o₁ o₂) × ComparePS {!!} {!!}
  helper o₁ (yes (there (there (here px)))) o₂ (yes (there (there (there p₁)))) = ⊥
  helper o₁ (yes (there (there (there p)))) o₂ (yes (there (there (here px)))) = ⊥
  helper o₁ (yes (there (there (there (here px))))) o₂ (yes (there (there (there (here px₁))))) = (_≋_ {A = OID} o₁ o₂) × CompareIS {!!} {!!}


data InSeq {@0 bs} (a : RDN.ATV bs) : (@0 b : List Dig) → SequenceOf RDN.ATV b → Set where
  here  : ∀ {@0 bs₁ bs₂ bs₃} {x : RDN.ATV bs₁} {xs : SequenceOf RDN.ATV bs₂} (px : MatchRDNATV a x) (@0 bs≡ : bs₃ ≡ bs₁ ++ bs₂) → InSeq a (bs₃) (cons (mkSequenceOf x xs bs≡))
  there : ∀ {@0 bs₁ bs₂ bs₃} {x : RDN.ATV bs₁} {xs : SequenceOf RDN.ATV bs₂} (pxs : InSeq a bs₂ xs) (@0 bs≡ : bs₃ ≡ bs₁ ++ bs₂) → InSeq a (bs₃) (cons (mkSequenceOf x xs bs≡))

data AllInSeq {@0 bs} (xs : SequenceOf RDN.ATV bs) : (@0 b : List Dig) → SequenceOf RDN.ATV b → Set where
  []  : AllInSeq xs [] nil
  cons : ∀ {@0 bs₁ bs₂ bs₃} {x : RDN.ATV bs₁} {xs' : SequenceOf RDN.ATV bs₂} (px : InSeq x _ xs) (pxs : AllInSeq xs _ xs') (@0 bs≡ : bs₃ ≡ bs₁ ++ bs₂) → AllInSeq xs bs₃ (cons (mkSequenceOf x xs' bs≡))

MatchRDNElemsLen : ∀ {@0 bs₁ bs₂} → RDNElems bs₁ → RDNElems bs₂ → Set
MatchRDNElemsLen (Aeres.Grammar.Definitions.mk×ₚ fstₚ₁ sndₚ₁ bs≡) (Aeres.Grammar.Definitions.mk×ₚ fstₚ₂ sndₚ₂ bs≡₁) = (lengthSequence fstₚ₁) ≡ (lengthSequence fstₚ₂)

MatchRDN : ∀ {@0 bs₁ bs₂} → RDN bs₁ → RDN bs₂ → Set
MatchRDN (mkTLV len x@(Aeres.Grammar.Definitions.mk×ₚ fstₚ₁ sndₚ₁ bs≡) len≡ refl) (mkTLV len₁ x'@(Aeres.Grammar.Definitions.mk×ₚ {bs = bs₂'} fstₚ₂ sndₚ₂ bs≡₁) len≡₁ refl) = (MatchRDNElemsLen x x') × AllInSeq fstₚ₁ bs₂' fstₚ₂

MatchRDNSeqHelper : ∀ {@0 bs₁ bs₂} → SequenceOfFields RDN bs₁ → SequenceOfFields RDN bs₂ → Set
MatchRDNSeqHelper (mkSequenceOf h nil bs≡) (mkSequenceOf h₁ nil bs≡₁) = MatchRDN h h₁
MatchRDNSeqHelper (mkSequenceOf h nil bs≡) (mkSequenceOf h₁ (cons x) bs≡₁) = MatchRDN h h₁
MatchRDNSeqHelper (mkSequenceOf h (cons x) bs≡) (mkSequenceOf h₁ nil bs≡₁) = MatchRDN h h₁
MatchRDNSeqHelper (mkSequenceOf h (cons x) bs≡) (mkSequenceOf h₁ (cons x₁) bs≡₁) = MatchRDN h h₁ × MatchRDNSeqHelper x x₁

MatchRDNSeq : ∀ {@0 bs₁ bs₂} → Name bs₁ → Name bs₂ → Set
MatchRDNSeq (mkTLV len nil len≡ bs≡) (mkTLV len₁ nil len≡₁ bs≡₁) = ⊤
MatchRDNSeq (mkTLV len nil len≡ bs≡) (mkTLV len₁ (cons x) len≡₁ bs≡₁) = ⊥
MatchRDNSeq (mkTLV len (cons x) len≡ bs≡) (mkTLV len₁ nil len≡₁ bs≡₁) = ⊥
MatchRDNSeq (mkTLV len (cons x) len≡ bs≡) (mkTLV len₁ (cons x₁) len≡₁ bs≡₁) = MatchRDNSeqHelper x x₁

CCP6Seq : List (Exists─ (List Dig) Cert) → Set
CCP6Seq [] = ⊥
CCP6Seq ((fst , snd) ∷ []) = ⊤
CCP6Seq ((fst , snd) ∷ (fst₁ , snd₁) ∷ x₂) = MatchRDNSeq (proj₂ (Cert.getIssuer snd)) (proj₂ (Cert.getSubject snd₁)) × CCP6Seq ((fst₁ , snd₁) ∷ x₂)

CCP10Seq : List (Exists─ (List UInt8) Cert) → Set
CCP10Seq [] = ⊤
CCP10Seq ((fst , snd) ∷ []) = T (isCA (Cert.getBC snd))
CCP10Seq ((fst , snd) ∷ (fst₁ , snd₁) ∷ x₁) = T (isCA (Cert.getBC snd₁)) × CCP10Seq x₁

helperCCP4₁-h : ∀ {@0 h t} → Extension.CRLDistPoint.DistPoint h → IList UInt8 Extension.CRLDistPoint.DistPoint t  → Set
helperCCP4₁-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields crldp crldprsn none bs≡₁) len≡ bs≡) x₁ = ⊥
helperCCP4₁-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields crldp crldprsn (some x) bs≡₁) len≡ bs≡) nil = ⊤ 
helperCCP4₁-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields crldp crldprsn (some x) bs≡₁) len≡ bs≡) (cons (mkIListCons head₁ tail₁ bs≡₂)) = helperCCP4₁-h head₁ tail₁
  
helperCCP4₁ : Exists─ (List UInt8) (Option ExtensionFieldCRLDist) → Set
helperCCP4₁ (─ .[] , none) = ⊤
helperCCP4₁ (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ (cons (mkIListCons head₁ tail₁ bs≡₄)) snd₁ bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = helperCCP4₁-h head₁ tail₁

helperCCP4₂-h : ∀ {@0 h t} → Extension.CRLDistPoint.DistPoint h → IList UInt8 Extension.CRLDistPoint.DistPoint t  → Set
helperCCP4₂-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields none crldprsn none bs≡₁) len≡ bs≡) x₁ = ⊥
helperCCP4₂-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields none crldprsn (some x) bs≡₁) len≡ bs≡) x₁ = ⊥
helperCCP4₂-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields (some x) crldprsn none bs≡₁) len≡ bs≡) nil = ⊤
helperCCP4₂-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields (some x) crldprsn none bs≡₁) len≡ bs≡) (cons (mkIListCons head₁ tail₁ bs≡₂)) = helperCCP4₂-h head₁ tail₁
helperCCP4₂-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields (some x) crldprsn (some y) bs≡₁) len≡ bs≡) x₁ = ⊥

helperCCP4₂ : Exists─ (List UInt8) (Option ExtensionFieldCRLDist) → Set
helperCCP4₂ (─ .[] , none) = ⊤
helperCCP4₂ (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ (cons (mkIListCons head₁ tail₁ bs≡₄)) snd₁ bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = helperCCP4₂-h head₁ tail₁

helperCCP4 : (c : List (Exists─ (List Dig) Cert)) → Set
helperCCP4 [] = ⊤
helperCCP4 ((fst , snd) ∷ [])
  with isCRLSignPresent (Cert.getKU snd)
... | false = (MatchRDNSeq (proj₂ (Cert.getIssuer snd)) (proj₂ (Cert.getSubject snd))) × helperCCP4₁ (Cert.getCRLDIST snd)
... | true = (MatchRDNSeq (proj₂ (Cert.getIssuer snd)) (proj₂ (Cert.getSubject snd))) × helperCCP4₂ (Cert.getCRLDIST snd)
helperCCP4 ((fst , snd) ∷ (fst₁ , snd₁) ∷ t)
  with isCRLSignPresent (Cert.getKU snd₁)
... | false = (MatchRDNSeq (proj₂ (Cert.getIssuer snd)) (proj₂ (Cert.getSubject snd₁))) × helperCCP4₁ (Cert.getCRLDIST snd)
... | true = (MatchRDNSeq (proj₂ (Cert.getIssuer snd)) (proj₂ (Cert.getSubject snd₁))) × helperCCP4₂ (Cert.getCRLDIST snd)

----------------- helper decidables -------------------------

MatchRDNATV-dec : ∀ {@0 bs₁ bs₂} → (n : RDN.ATV bs₁) → (m : RDN.ATV bs₂) → Dec (MatchRDNATV n m)
MatchRDNATV-dec (mkTLV len (RDN.mkATVFields oid val bs≡₂) len≡ bs≡) (mkTLV len₁ (RDN.mkATVFields oid₁ val₁ bs≡₃) len≡₁ bs≡₁) = {!!} --_≋?_ {A = OID} oid oid₁ -- ×-dec Compare-dec {!!} {!!}

InSeq-dec : ∀ {@0 bs} (a : RDN.ATV bs) → (@0 b : List Dig) → (c : SequenceOf RDN.ATV b) → Dec (InSeq a b c)
InSeq-dec a .[] nil = no (λ ())
InSeq-dec a b (cons (mkIListCons {bs₂ = g} head₁ tail₁ bs≡)) = case MatchRDNATV-dec a head₁ of λ where
  (no ¬p) → case (InSeq-dec a g tail₁) ret (const _) of λ where
    (no ¬q) → no λ where
      (here px .bs≡) → contradiction px ¬p
      (there x .bs≡) → contradiction x ¬q
    (yes p) → yes (there p bs≡)
  (yes p) → yes (here p bs≡)

AllInSeq-dec : ∀ {@0 bs} (xs : SequenceOf RDN.ATV bs) → (@0 b : List Dig) → (c : SequenceOf RDN.ATV b) → Dec (AllInSeq xs b c)
AllInSeq-dec xs .[] nil = yes AllInSeq.[]
AllInSeq-dec xs b (cons (mkIListCons head₁ tail₁ bs≡)) = case (InSeq-dec head₁ _ xs) of λ where
  (no ¬p) → no λ where
    (cons px z bs≡) → contradiction px ¬p
  (yes p) → case AllInSeq-dec xs _ tail₁ of λ where
    (no ¬p) → no λ where
      (cons px z bs≡) → contradiction z ¬p
    (yes q) → yes (cons p q bs≡)

MatchRDNElemsLen-dec : ∀ {@0 bs₁ bs₂} → (n : RDNElems bs₁) → (m : RDNElems bs₂) → Dec (MatchRDNElemsLen n m)
MatchRDNElemsLen-dec (Aeres.Grammar.Definitions.mk×ₚ fstₚ₁ sndₚ₁ bs≡) (Aeres.Grammar.Definitions.mk×ₚ fstₚ₂ sndₚ₂ bs≡₁) = (lengthSequence fstₚ₁) ≟ (lengthSequence fstₚ₂)

MatchRDN-dec : ∀ {@0 bs₁ bs₂} → (n : RDN bs₁) → (m : RDN bs₂) → Dec (MatchRDN n m)
MatchRDN-dec (mkTLV len x@(Aeres.Grammar.Definitions.mk×ₚ fstₚ₁ sndₚ₁ bs≡) len≡ refl) (mkTLV len₁ x'@(Aeres.Grammar.Definitions.mk×ₚ {bs = bs₂'} fstₚ₂ sndₚ₂ bs≡₁) len≡₁ refl) = (MatchRDNElemsLen-dec x x') ×-dec AllInSeq-dec fstₚ₁ bs₂' fstₚ₂

MatchRDNSeq-dec : ∀ {@0 bs₁ bs₂} → (a : Name bs₁) → (b : Name bs₂) → Dec (MatchRDNSeq a b)
MatchRDNSeq-dec (mkTLV len nil len≡ bs≡) (mkTLV len₁ nil len≡₁ bs≡₁) = yes tt
MatchRDNSeq-dec (mkTLV len nil len≡ bs≡) (mkTLV len₁ (cons x) len≡₁ bs≡₁) = no (λ ())
MatchRDNSeq-dec (mkTLV len (cons x) len≡ bs≡) (mkTLV len₁ nil len≡₁ bs≡₁) = no (λ ())
MatchRDNSeq-dec (mkTLV len (cons x) len≡ bs≡) (mkTLV len₁ (cons x₁) len≡₁ bs≡₁) = helper x x₁
  where
  helper : ∀ {@0 bs₁ bs₂} → (a : SequenceOfFields RDN bs₁) → (b : SequenceOfFields RDN bs₂) → Dec (MatchRDNSeqHelper a b)
  helper (mkSequenceOf h nil bs≡) (mkSequenceOf h₁ nil bs≡₁) = MatchRDN-dec h h₁
  helper (mkSequenceOf h nil bs≡) (mkSequenceOf h₁ (cons x) bs≡₁) = MatchRDN-dec h h₁
  helper (mkSequenceOf h (cons x) bs≡) (mkSequenceOf h₁ nil bs≡₁) = MatchRDN-dec h h₁
  helper (mkSequenceOf h (cons x) bs≡) (mkSequenceOf h₁ (cons x₁) bs≡₁) = MatchRDN-dec h h₁ ×-dec helper x x₁

helperCCP4₂-h-dec : ∀ {@0 h t} → (a : Extension.CRLDistPoint.DistPoint h) → (b : IList UInt8 Extension.CRLDistPoint.DistPoint t)  → Dec (helperCCP4₂-h a b)
helperCCP4₂-h-dec (mkTLV len (Extension.CRLDistPoint.mkDistPointFields none crldprsn none bs≡₁) len≡ bs≡) x₁ = no (λ())
helperCCP4₂-h-dec (mkTLV len (Extension.CRLDistPoint.mkDistPointFields none crldprsn (some x) bs≡₁) len≡ bs≡) x₁ = no (λ())
helperCCP4₂-h-dec (mkTLV len (Extension.CRLDistPoint.mkDistPointFields (some x) crldprsn none bs≡₁) len≡ bs≡) nil = yes tt
helperCCP4₂-h-dec (mkTLV len (Extension.CRLDistPoint.mkDistPointFields (some x) crldprsn none bs≡₁) len≡ bs≡) (cons (mkIListCons head₁ tail₁ bs≡₂)) = helperCCP4₂-h-dec head₁ tail₁
helperCCP4₂-h-dec (mkTLV len (Extension.CRLDistPoint.mkDistPointFields (some x) crldprsn (some y) bs≡₁) len≡ bs≡) x₁ = no (λ())

helperCCP4₂-dec : (c : Exists─ (List UInt8) (Option ExtensionFieldCRLDist)) → Dec (helperCCP4₂ c)
helperCCP4₂-dec (─ .[] , none) = yes tt
helperCCP4₂-dec (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ (cons (mkIListCons head₁ tail₁ bs≡₄)) snd₁ bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = helperCCP4₂-h-dec head₁ tail₁

helperCCP4₁-h-dec : ∀ {@0 h t} → (a : Extension.CRLDistPoint.DistPoint h) → (b : IList UInt8 Extension.CRLDistPoint.DistPoint t)  → Dec (helperCCP4₁-h a b)
helperCCP4₁-h-dec (mkTLV len (Extension.CRLDistPoint.mkDistPointFields crldp crldprsn none bs≡₁) len≡ bs≡) x₁ = no (λ())
helperCCP4₁-h-dec (mkTLV len (Extension.CRLDistPoint.mkDistPointFields crldp crldprsn (some x) bs≡₁) len≡ bs≡) nil = yes tt 
helperCCP4₁-h-dec (mkTLV len (Extension.CRLDistPoint.mkDistPointFields crldp crldprsn (some x) bs≡₁) len≡ bs≡) (cons (mkIListCons head₁ tail₁ bs≡₂)) = helperCCP4₁-h-dec head₁ tail₁

helperCCP4₁-dec : (c : Exists─ (List UInt8) (Option ExtensionFieldCRLDist)) → Dec (helperCCP4₁ c)
helperCCP4₁-dec (─ .[] , none) = yes tt
helperCCP4₁-dec (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ (cons (mkIListCons head₁ tail₁ bs≡₄)) snd₁ bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = helperCCP4₁-h-dec head₁ tail₁

helperCCP4-dec : (c : List (Exists─ (List Dig) Cert)) → Dec (helperCCP4 c)
helperCCP4-dec [] = yes tt
helperCCP4-dec ((fst , snd) ∷ [])
  with isCRLSignPresent (Cert.getKU snd)
... | false = (MatchRDNSeq-dec (proj₂ (Cert.getIssuer snd)) (proj₂ (Cert.getSubject snd))) ×-dec helperCCP4₁-dec (Cert.getCRLDIST snd)
... | true = (MatchRDNSeq-dec (proj₂ (Cert.getIssuer snd)) (proj₂ (Cert.getSubject snd))) ×-dec helperCCP4₂-dec (Cert.getCRLDIST snd)
helperCCP4-dec ((fst , snd) ∷ (fst₁ , snd₁) ∷ t)
  with isCRLSignPresent (Cert.getKU snd₁)
... | false = (MatchRDNSeq-dec (proj₂ (Cert.getIssuer snd)) (proj₂ (Cert.getSubject snd₁))) ×-dec helperCCP4₁-dec (Cert.getCRLDIST snd)
... | true = (MatchRDNSeq-dec (proj₂ (Cert.getIssuer snd)) (proj₂ (Cert.getSubject snd₁))) ×-dec helperCCP4₂-dec (Cert.getCRLDIST snd)

------------------------------------------------------------------------

countNextIntCACerts : List (Exists─ (List UInt8) Cert) → ℤ → ℤ
countNextIntCACerts [] n = n
countNextIntCACerts ((fst , snd) ∷ x₁) n
  with isCA (Cert.getBC snd)
... | false = countNextIntCACerts x₁ n
... | true
  with MatchRDNSeq-dec (proj₂ (Cert.getIssuer snd)) (proj₂ (Cert.getSubject snd))
... | no ¬p =  countNextIntCACerts x₁ (n ℤ.+ ℤ.+ 1) 
... | yes p =  countNextIntCACerts x₁ n

helperCCP3 : Exists─ (List UInt8) Cert → List (Exists─ (List UInt8) Cert) → Set
helperCCP3 (fst , snd) x₁
  with isCA (Cert.getBC snd) ∧ isKeyCertSignPresent (Cert.getKU snd)
... | false = ⊤
... | true
  with (getBCPathLen (Cert.getBC snd))
... | (─ .[] , none) = ⊤
... | (fst , some x) = countNextIntCACerts x₁ (ℤ.+ 0) ℤ.≤ Int.getVal x

CCP3Seq : List (Exists─ (List UInt8) Cert) → Set
CCP3Seq [] = ⊤
CCP3Seq (x ∷ x₁) =  helperCCP3 x x₁ × CCP3Seq x₁

helperCCP3-dec : (c : Exists─ (List UInt8) Cert) → (t : List (Exists─ (List UInt8) Cert)) → Dec (helperCCP3 c t)
helperCCP3-dec (fst , snd) x₁
  with isCA (Cert.getBC snd) ∧ isKeyCertSignPresent (Cert.getKU snd)
... | false = yes tt
... | true
  with (getBCPathLen (Cert.getBC snd))
... | (─ .[] , none) = yes tt
... | (fst , some x) = countNextIntCACerts x₁ (ℤ.+ 0) ℤ.≤? Int.getVal x

-------------------------- CCP rules ---------------------------------------

-- Conforming implementations may choose to reject all Version 1 and Version 2 intermediate CA certificates
CCP2 : ∀ {@0 bs} → Chain bs → Set
CCP2 nil = ⊤
CCP2 (cons (mkIListCons h t bs≡)) = CCP2Seq t

ccp2 : ∀ {@0 bs} (c : Chain bs) → Dec (CCP2 c)
ccp2 nil = yes tt
ccp2 (cons (mkIListCons h t bs≡)) = helper t
  where
  helper : ∀ {@0 bs} → (c : IList UInt8 Cert bs) → Dec (CCP2Seq c)  
  helper nil = yes tt
  helper (cons (mkSequenceOf h nil bs≡)) = yes tt
  helper (cons (mkSequenceOf h (cons x) bs≡)) = (Cert.getVersion h ≟ ℤ.+ 2) ×-dec helper (cons x)


--- The PathLenConstraint field is meaningful only if the CA boolean
--- is asserted and the Key Usage extension, if present, asserts the KeyCertSign bit. In this case, it gives
--- the maximum number of non-self-issued intermediate certificates that may follow this certificate in a valid certification path.
CCP3 : ∀ {@0 bs} → Chain bs → Set
CCP3 c = CCP3Seq (reverse (chainToList c))

ccp3 : ∀ {@0 bs} (c : Chain bs) → Dec (CCP3 c)
ccp3 c = CCP3Seq-dec (reverse (chainToList c))
  where
  CCP3Seq-dec : (c : List (Exists─ (List Dig) Cert)) → Dec (CCP3Seq c)
  CCP3Seq-dec [] = yes tt
  CCP3Seq-dec (x ∷ x₁) = helperCCP3-dec x x₁ ×-dec CCP3Seq-dec x₁


-- For DistributionPoint field, if the certificate issuer is not the CRL issuer,
-- then the CRLIssuer field MUST be present and contain the Name of the CRL issuer. If the
-- certificate issuer is also the CRL issuer, then conforming CAs MUST omit the CRLIssuer
-- field and MUST include the distributionPoint field.
CCP4 : ∀ {@0 bs} → Chain bs → Set
CCP4 c = helperCCP4 (chainToList c)

ccp4 : ∀ {@0 bs} (c : Chain bs) → Dec (CCP4 c)
ccp4 c = helperCCP4-dec (chainToList c)


-- A certificate MUST NOT appear more than once in a prospective certification path.
CCP5 : ∀ {@0 bs} → Chain bs → Set
CCP5 c = List.Unique _≟_ (chainToList c)

ccp5 : ∀ {@0 bs} (c : Chain bs) → Dec (CCP5 c)
ccp5 c = List.unique? _≟_ (chainToList c)


-- Certificate users MUST be prepared to process the Issuer distinguished name
-- and Subject distinguished name fields to perform name chaining for certification path validation.
CCP6 : ∀ {@0 bs} → Chain bs → Set
CCP6 c = CCP6Seq (chainToList c)

ccp6 : ∀ {@0 bs} (c : Chain bs) → Dec (CCP6 c)
ccp6 c = helper (chainToList c)
  where
  helper : (c : List (Exists─ (List Dig) Cert)) → Dec (CCP6Seq c)
  helper [] = no (λ ())
  helper ((fst , snd) ∷ []) = yes tt
  helper ((fst , snd) ∷ (fst₁ , snd₁) ∷ x₂) = (MatchRDNSeq-dec (proj₂ (Cert.getIssuer snd)) (proj₂ (Cert.getSubject snd₁))) ×-dec helper ((fst₁ , snd₁) ∷ x₂)


--- every issuer certificate in a chain must be CA certificate
CCP10 : ∀ {@0 bs} → Chain bs → Set
CCP10 c = CCP10Seq (chainToList c)

ccp10 : ∀ {@0 bs} (c : Chain bs) → Dec (CCP10 c)
ccp10 c = helper (chainToList c)
  where
  helper : (c : List (Exists─ (List Dig) Cert)) → Dec (CCP10Seq c)
  helper [] = yes tt
  helper ((fst , snd) ∷ [])
    with isCA (Cert.getBC snd)
  ... | false = no (λ ())
  ... | true = yes tt
  helper ((fst , snd) ∷ (fst₁ , snd₁) ∷ t)
    with isCA (Cert.getBC snd₁)
  ... | false = no (λ ())
  ... | true = yes tt ×-dec helper t
