{-# OPTIONS --sized-types #-}

import      Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Semantic.StringPrep.ExecDS
open import Aeres.Data.X509.Semantic.StringPrep.ExecPS
open import Aeres.Data.X509.Semantic.StringPrep.ExecIS
open import Aeres.Data.X509.Semantic.Cert
open import Aeres.Data.X509.Semantic.Cert.Utils
import      Aeres.Grammar.Definitions
open import Aeres.Grammar.IList as IList
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parallel
open import Aeres.Prelude

open import  Aeres.Data.X509.Name.RDN.ATV.OIDs

module Aeres.Data.X509.Semantic.Chain where

open Aeres.Binary
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parallel    UInt8


------- helper functions ------

chainToList : ∀ {@0 bs} → CertList bs  → List (Exists─ (List UInt8) Cert)
chainToList nil = []
chainToList (cons (mkIListCons h t bs≡)) = (_ , h) ∷ helper t
  where
  helper : ∀ {@0 bs} → IList UInt8 Cert bs → List (Exists─ (List UInt8) Cert)
  helper nil = []
  helper (cons (mkIListCons h t bs≡)) = (_ , h) ∷ helper t

CCP2Seq : ∀ {@0 bs} → SequenceOf Cert bs → Set  
CCP2Seq nil = ⊤
CCP2Seq (cons (mkSequenceOf h nil bs≡)) = ⊤
CCP2Seq (cons (mkSequenceOf h (cons x) bs≡)) = Cert.getVersion h ≡ TBSCert.v3 × CCP2Seq (cons x)

helperMatchRDNATV : ∀ {@0 bs₁ bs₂ bs₃} → (o : OID bs₁) → (d : Dec ((-, TLV.val o) ∈ Supported)) → Name.RDN.ATVParam o d bs₂ → Name.RDN.ATVParam o d bs₃ → Set
helperMatchRDNATV o (no ¬p) x x₁ = CompareDS x x₁
helperMatchRDNATV o (yes (here px)) x x₁ = ComparePS x x₁
helperMatchRDNATV o (yes (there (here px))) (mk×ₚ fstₚ₁ sndₚ₁) (mk×ₚ fstₚ₂ sndₚ₂) = ComparePS fstₚ₁ fstₚ₂
helperMatchRDNATV o (yes (there (there (here px)))) x x₁ = ComparePS x x₁
helperMatchRDNATV o (yes (there (there (there (here px))))) x x₁ = CompareIS x x₁
helperMatchRDNATV o (yes (there (there (there (there (here px)))))) x x₁ = CompareIS x x₁
  
MatchRDNATV : ∀ {@0 bs₁ bs₂} → Name.RDN.ATV bs₁ → Name.RDN.ATV bs₂ → Set
MatchRDNATV (mkTLV len (Sequence.mkOIDDefinedFields oid param bs≡₂) len≡ bs≡) (mkTLV len₁ (Sequence.mkOIDDefinedFields oid₁ param₁ bs≡₃) len≡₁ bs≡₁)
  = Σ (_≋_ {A = OID} oid oid₁) (λ where ≋-refl → helperMatchRDNATV oid ((-, TLV.val oid) ∈? Supported) param param₁)

data InSeq {@0 bs} (a : Name.RDN.ATV bs) : (@0 b : List UInt8) → SequenceOf Name.RDN.ATV b → Set where
  here  : ∀ {@0 bs₁ bs₂ bs₃} {x : Name.RDN.ATV bs₁} {xs : SequenceOf Name.RDN.ATV bs₂} (px : MatchRDNATV a x) (@0 bs≡ : bs₃ ≡ bs₁ ++ bs₂) → InSeq a (bs₃) (cons (mkSequenceOf x xs bs≡))
  there : ∀ {@0 bs₁ bs₂ bs₃} {x : Name.RDN.ATV bs₁} {xs : SequenceOf Name.RDN.ATV bs₂} (pxs : InSeq a bs₂ xs) (@0 bs≡ : bs₃ ≡ bs₁ ++ bs₂) → InSeq a (bs₃) (cons (mkSequenceOf x xs bs≡))

data AllInSeq {@0 bs} (xs : SequenceOf Name.RDN.ATV bs) : (@0 b : List UInt8) → SequenceOf Name.RDN.ATV b → Set where
  []  : AllInSeq xs [] nil
  cons : ∀ {@0 bs₁ bs₂ bs₃} {x : Name.RDN.ATV bs₁} {xs' : SequenceOf Name.RDN.ATV bs₂} (px : InSeq x _ xs) (pxs : AllInSeq xs _ xs') (@0 bs≡ : bs₃ ≡ bs₁ ++ bs₂) → AllInSeq xs bs₃ (cons (mkSequenceOf x xs' bs≡))

MatchRDNElemsLen : ∀ {@0 bs₁ bs₂} → SetOfFields Name.RDN.ATV bs₁ → SetOfFields Name.RDN.ATV bs₂ → Set
MatchRDNElemsLen (mkSetOfFields (mk×ₚ fstₚ₁ sndₚ₁≡) _) (mkSetOfFields (mk×ₚ fstₚ₂ sndₚ₂) _) = (lengthSequence fstₚ₁) ≡ (lengthSequence fstₚ₂)

MatchRDN : ∀ {@0 bs₁ bs₂} → Name.RDN bs₁ → Name.RDN bs₂ → Set
MatchRDN (mkTLV len x@(mkSetOfFields (mk×ₚ fstₚ₁ sndₚ₁) _) len≡ refl) (mkTLV len₁ x'@(mkSetOfFields (mk×ₚ fstₚ₂ sndₚ₂) _) len≡₁ refl) = (MatchRDNElemsLen x x') × AllInSeq fstₚ₁ _ fstₚ₂

MatchRDNSeqHelper : ∀ {@0 bs₁ bs₂} → SequenceOfFields Name.RDN bs₁ → SequenceOfFields Name.RDN bs₂ → Set
MatchRDNSeqHelper (mkSequenceOf h nil bs≡) (mkSequenceOf h₁ nil bs≡₁) = MatchRDN h h₁
MatchRDNSeqHelper (mkSequenceOf h nil bs≡) (mkSequenceOf h₁ (cons x) bs≡₁) = MatchRDN h h₁
MatchRDNSeqHelper (mkSequenceOf h (cons x) bs≡) (mkSequenceOf h₁ nil bs≡₁) = MatchRDN h h₁
MatchRDNSeqHelper (mkSequenceOf h (cons x) bs≡) (mkSequenceOf h₁ (cons x₁) bs≡₁) = MatchRDN h h₁ × MatchRDNSeqHelper x x₁

MatchRDNSeq : ∀ {@0 bs₁ bs₂} → Name bs₁ → Name bs₂ → Set
MatchRDNSeq (mkTLV len nil len≡ bs≡) (mkTLV len₁ nil len≡₁ bs≡₁) = ⊤
MatchRDNSeq (mkTLV len nil len≡ bs≡) (mkTLV len₁ (cons x) len≡₁ bs≡₁) = ⊥
MatchRDNSeq (mkTLV len (cons x) len≡ bs≡) (mkTLV len₁ nil len≡₁ bs≡₁) = ⊥
MatchRDNSeq (mkTLV len (cons x) len≡ bs≡) (mkTLV len₁ (cons x₁) len≡₁ bs≡₁) = MatchRDNSeqHelper x x₁

CCP6Seq : List (Exists─ (List UInt8) Cert) → Set
CCP6Seq [] = ⊥
CCP6Seq ((fst , snd) ∷ []) = ⊤
CCP6Seq ((fst , snd) ∷ (fst₁ , snd₁) ∷ x₂) = MatchRDNSeq (Cert.getIssuer snd) (Cert.getSubject snd₁) × CCP6Seq ((fst₁ , snd₁) ∷ x₂)

CCP10Seq : List (Exists─ (List UInt8) Cert) → Set
CCP10Seq [] = ⊥
CCP10Seq ((fst , snd) ∷ []) = ⊤
CCP10Seq ((fst , snd) ∷ (fst₁ , snd₁) ∷ x₁) = T(isCA (Cert.getBC snd₁)) × CCP10Seq ((fst₁ , snd₁) ∷ x₁)

helperCCP4₁-h : ∀ {@0 h t} → Extension.CRLDistPoint.DistPoint h → IList UInt8 Extension.CRLDistPoint.DistPoint t  → Set
helperCCP4₁-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields crldp crldprsn none bs≡₁) len≡ bs≡) x₁ = ⊥
helperCCP4₁-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields crldp crldprsn (some x) bs≡₁) len≡ bs≡) nil = ⊤ 
helperCCP4₁-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields crldp crldprsn (some x) bs≡₁) len≡ bs≡) (cons (mkIListCons head₁ tail₁ bs≡₂)) = helperCCP4₁-h head₁ tail₁
  
helperCCP4₁ : Exists─ (List UInt8) (Option ExtensionFieldCRLDist) → Set
helperCCP4₁ (─ .[] , none) = ⊤
helperCCP4₁ (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ (cons (mkIListCons head₁ tail₁ bs≡₄)) snd₁) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = helperCCP4₁-h head₁ tail₁

helperCCP4₂-h : ∀ {@0 h t} → Extension.CRLDistPoint.DistPoint h → IList UInt8 Extension.CRLDistPoint.DistPoint t  → Set
helperCCP4₂-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields none crldprsn none bs≡₁) len≡ bs≡) x₁ = ⊥
helperCCP4₂-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields none crldprsn (some x) bs≡₁) len≡ bs≡) x₁ = ⊥
helperCCP4₂-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields (some x) crldprsn none bs≡₁) len≡ bs≡) nil = ⊤
helperCCP4₂-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields (some x) crldprsn none bs≡₁) len≡ bs≡) (cons (mkIListCons head₁ tail₁ bs≡₂)) = helperCCP4₂-h head₁ tail₁
helperCCP4₂-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields (some x) crldprsn (some y) bs≡₁) len≡ bs≡) x₁ = ⊥

helperCCP4₂ : Exists─ (List UInt8) (Option ExtensionFieldCRLDist) → Set
helperCCP4₂ (─ .[] , none) = ⊤
helperCCP4₂ (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ (cons (mkIListCons head₁ tail₁ bs≡₄)) snd₁) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = helperCCP4₂-h head₁ tail₁

helperCCP4 : (c : List (Exists─ (List UInt8) Cert)) → Set
helperCCP4 [] = ⊥
helperCCP4 (x₁ ∷ []) = ⊤
helperCCP4 (x₁ ∷ x₂ ∷ t) with helperCCP4 (x₂ ∷ t) | isCRLSignPresent (Cert.getKU (proj₂ x₂))
... | rec | true =  helperCCP4₂ (Cert.getCRLDIST (proj₂ x₁)) × rec
... | rec | false = helperCCP4₁ (Cert.getCRLDIST (proj₂ x₁)) × rec

certInList : Exists─ (List UInt8) Cert →  List (Exists─ (List UInt8) Cert) → Bool
certInList c [] = false
certInList (fst , snd) ((fst₁ , snd₁) ∷ l) = case (snd ≋? snd₁) of λ where
  (no ¬p) → certInList (fst , snd) l
  (yes p) → true
    
helperCCP7 : List (Exists─ (List UInt8) Cert) → List (Exists─ (List UInt8) Cert) → Set
helperCCP7 r [] = ⊥
helperCCP7 r (x ∷ t)
  with certInList x r
... | false = helperCCP7 r t
... | true = ⊤

----------------- helper decidables -------------------------

helperMatchRDNATV-dec : ∀ {@0 bs₁ bs₂ bs₃} → (o : OID bs₁) → (d : Dec ((-, TLV.val o) ∈ Supported)) → (p₁ : Name.RDN.ATVParam o d bs₂) → (p₂ : Name.RDN.ATVParam o d bs₃) →
  Dec (helperMatchRDNATV o d p₁ p₂)
helperMatchRDNATV-dec o (no ¬p) x x₁ = CompareDS-dec x x₁
helperMatchRDNATV-dec o (yes (here px)) x x₁ = ComparePS-dec x x₁
helperMatchRDNATV-dec o (yes (there (here px))) (mk×ₚ fstₚ₁ sndₚ₁) (mk×ₚ fstₚ₂ sndₚ₂) = ComparePS-dec fstₚ₁ fstₚ₂
helperMatchRDNATV-dec o (yes (there (there (here px)))) x x₁ = ComparePS-dec x x₁
helperMatchRDNATV-dec o (yes (there (there (there (here px))))) x x₁ = CompareIS-dec x x₁
helperMatchRDNATV-dec o (yes (there (there (there (there (here px)))))) x x₁ = CompareIS-dec x x₁

MatchRDNATV-dec : ∀ {@0 bs₁ bs₂} → (n : Name.RDN.ATV bs₁) → (m : Name.RDN.ATV bs₂) → Dec (MatchRDNATV n m)
MatchRDNATV-dec (mkTLV len (Sequence.mkOIDDefinedFields oid param bs≡₂) len≡ bs≡) (mkTLV len₁ (Sequence.mkOIDDefinedFields oid₁ param₁ bs≡₃) len≡₁ bs≡₁)
  = case (_≋?_ {A = OID} oid oid₁) of λ where
      (no ¬p) → no λ { (fst , snd) → contradiction fst ¬p}
      (yes ≋-refl) →
        case helperMatchRDNATV-dec oid ((-, TLV.val oid) ∈? Supported) param param₁ of λ where
          (no ¬p) → no λ where (≋-refl , snd) → contradiction snd ¬p
          (yes p) → yes (≋-refl , p)

InSeq-dec : ∀ {@0 bs} (a : Name.RDN.ATV bs) → (@0 b : List UInt8) → (c : SequenceOf Name.RDN.ATV b) → Dec (InSeq a b c)
InSeq-dec a .[] nil = no (λ ())
InSeq-dec a b (cons (mkIListCons {bs₂ = g} head₁ tail₁ bs≡)) = case MatchRDNATV-dec a head₁ of λ where
  (no ¬p) → case (InSeq-dec a g tail₁) ret (const _) of λ where
    (no ¬q) → no λ where
      (here px .bs≡) → contradiction px ¬p
      (there x .bs≡) → contradiction x ¬q
    (yes p) → yes (there p bs≡)
  (yes p) → yes (here p bs≡)

AllInSeq-dec : ∀ {@0 bs} (xs : SequenceOf Name.RDN.ATV bs) → (@0 b : List UInt8) → (c : SequenceOf Name.RDN.ATV b) → Dec (AllInSeq xs b c)
AllInSeq-dec xs .[] nil = yes AllInSeq.[]
AllInSeq-dec xs b (cons (mkIListCons head₁ tail₁ bs≡)) = case (InSeq-dec head₁ _ xs) of λ where
  (no ¬p) → no λ where
    (cons px z bs≡) → contradiction px ¬p
  (yes p) → case AllInSeq-dec xs _ tail₁ of λ where
    (no ¬p) → no λ where
      (cons px z bs≡) → contradiction z ¬p
    (yes q) → yes (cons p q bs≡)

MatchRDNElemsLen-dec : ∀ {@0 bs₁ bs₂} → (n : SetOfFields Name.RDN.ATV bs₁) → (m : SetOfFields Name.RDN.ATV bs₂) → Dec (MatchRDNElemsLen n m)
MatchRDNElemsLen-dec (mkSetOfFields (mk×ₚ fstₚ₁ sndₚ₁) _) (mkSetOfFields (mk×ₚ fstₚ₂ sndₚ₂) _) = (lengthSequence fstₚ₁) ≟ (lengthSequence fstₚ₂)

MatchRDN-dec : ∀ {@0 bs₁ bs₂} → (n : Name.RDN bs₁) → (m : Name.RDN bs₂) → Dec (MatchRDN n m)
MatchRDN-dec (mkTLV len x@(mkSetOfFields (mk×ₚ fstₚ₁ sndₚ₁) _) len≡ refl) (mkTLV len₁ x'@(mkSetOfFields (mk×ₚ fstₚ₂ sndₚ₂) _) len≡₁ refl) = (MatchRDNElemsLen-dec x x') ×-dec AllInSeq-dec fstₚ₁ _ fstₚ₂

MatchRDNSeq-dec : ∀ {@0 bs₁ bs₂} → (a : Name bs₁) → (b : Name bs₂) → Dec (MatchRDNSeq a b)
MatchRDNSeq-dec (mkTLV len nil len≡ bs≡) (mkTLV len₁ nil len≡₁ bs≡₁) = yes tt
MatchRDNSeq-dec (mkTLV len nil len≡ bs≡) (mkTLV len₁ (cons x) len≡₁ bs≡₁) = no (λ ())
MatchRDNSeq-dec (mkTLV len (cons x) len≡ bs≡) (mkTLV len₁ nil len≡₁ bs≡₁) = no (λ ())
MatchRDNSeq-dec (mkTLV len (cons x) len≡ bs≡) (mkTLV len₁ (cons x₁) len≡₁ bs≡₁) = helper x x₁
  where
  helper : ∀ {@0 bs₁ bs₂} → (a : SequenceOfFields Name.RDN bs₁) → (b : SequenceOfFields Name.RDN bs₂) → Dec (MatchRDNSeqHelper a b)
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
helperCCP4₂-dec (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ (cons (mkIListCons head₁ tail₁ bs≡₄)) snd₁) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = helperCCP4₂-h-dec head₁ tail₁

helperCCP4₁-h-dec : ∀ {@0 h t} → (a : Extension.CRLDistPoint.DistPoint h) → (b : IList UInt8 Extension.CRLDistPoint.DistPoint t)  → Dec (helperCCP4₁-h a b)
helperCCP4₁-h-dec (mkTLV len (Extension.CRLDistPoint.mkDistPointFields crldp crldprsn none bs≡₁) len≡ bs≡) x₁ = no (λ())
helperCCP4₁-h-dec (mkTLV len (Extension.CRLDistPoint.mkDistPointFields crldp crldprsn (some x) bs≡₁) len≡ bs≡) nil = yes tt 
helperCCP4₁-h-dec (mkTLV len (Extension.CRLDistPoint.mkDistPointFields crldp crldprsn (some x) bs≡₁) len≡ bs≡) (cons (mkIListCons head₁ tail₁ bs≡₂)) = helperCCP4₁-h-dec head₁ tail₁

helperCCP4₁-dec : (c : Exists─ (List UInt8) (Option ExtensionFieldCRLDist)) → Dec (helperCCP4₁ c)
helperCCP4₁-dec (─ .[] , none) = yes tt
helperCCP4₁-dec (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ (cons (mkIListCons head₁ tail₁ bs≡₄)) snd₁) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = helperCCP4₁-h-dec head₁ tail₁

helperCCP4-dec : (c : List (Exists─ (List UInt8) Cert)) → Dec (helperCCP4 c)
helperCCP4-dec [] = no λ()
helperCCP4-dec (x₁ ∷ []) = yes tt
helperCCP4-dec (x₁ ∷ x₂ ∷ t) with helperCCP4-dec (x₂ ∷ t) | isCRLSignPresent (Cert.getKU (proj₂ x₂))
... | rec | true = helperCCP4₂-dec (Cert.getCRLDIST (proj₂ x₁)) ×-dec rec
... | rec | false = helperCCP4₁-dec (Cert.getCRLDIST (proj₂ x₁)) ×-dec rec

helperCCP7-dec : (r : List (Exists─ (List UInt8) Cert)) → (c : List (Exists─ (List UInt8) Cert)) → Dec (helperCCP7 r c)
helperCCP7-dec r [] = no λ()
helperCCP7-dec r (x ∷ t)
  with certInList x r
... | false = helperCCP7-dec r t
... | true = yes tt
------------------------------------------------------------------------

countNextIntCACerts : List (Exists─ (List UInt8) Cert) → ℤ → ℤ
countNextIntCACerts [] n = n
countNextIntCACerts ((fst , snd) ∷ x₁) n
  with isCA (Cert.getBC snd)
... | false = countNextIntCACerts x₁ n
... | true
  with MatchRDNSeq-dec (Cert.getIssuer snd) (Cert.getSubject snd)
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

-- https://datatracker.ietf.org/doc/html/rfc5280#section-6.1.4 (k)
-- Conforming implementations may choose to reject all Version 1 and Version 2 intermediate CA certificates

CCP2 : ∀ {@0 bs} → CertList bs → Set
CCP2 nil = ⊤
CCP2 (cons (mkIListCons h t bs≡)) = CCP2Seq t

ccp2 : ∀ {@0 bs} (c : CertList bs) → Dec (CCP2 c)
ccp2 nil = yes tt
ccp2 (cons (mkIListCons h t bs≡)) = helper t
  where
  helper : ∀ {@0 bs} → (c : IList UInt8 Cert bs) → Dec (CCP2Seq c)  
  helper nil = yes tt
  helper (cons (mkSequenceOf h nil bs≡)) = yes tt
  helper (cons (mkSequenceOf h (cons x) bs≡)) = (Cert.getVersion h ≟ TBSCert.v3) ×-dec helper (cons x)

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.9
--- The PathLenConstraint field is meaningful only if the CA boolean
--- is asserted and the Key Usage extension, if present, asserts the KeyCertSign bit. In this case, it gives
--- the maximum number of non-self-issued intermediate certificates that may follow this certificate in a valid certification path.

CCP3 : ∀ {@0 bs} → CertList bs → Set
CCP3 c = CCP3Seq (reverse (chainToList c))

ccp3 : ∀ {@0 bs} (c : CertList bs) → Dec (CCP3 c)
ccp3 c = CCP3Seq-dec (reverse (chainToList c))
  where
  CCP3Seq-dec : (c : List (Exists─ (List UInt8) Cert)) → Dec (CCP3Seq c)
  CCP3Seq-dec [] = yes tt
  CCP3Seq-dec (x ∷ x₁) = helperCCP3-dec x x₁ ×-dec CCP3Seq-dec x₁

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.13
-- For DistributionPoint field, if the certificate issuer is not the CRL issuer,
-- then the CRLIssuer field MUST be present and contain the Name of the CRL issuer. If the
-- certificate issuer is also the CRL issuer, then conforming CAs MUST omit the CRLIssuer
-- field and MUST include the distributionPoint field.

CCP4 : ∀ {@0 bs} → CertList bs → Set
CCP4 c = helperCCP4 (chainToList c)

ccp4 : ∀ {@0 bs} (c : CertList bs) → Dec (CCP4 c)
ccp4 c = helperCCP4-dec (chainToList c)

-- https://datatracker.ietf.org/doc/html/rfc5280#section-6.1
-- A certificate MUST NOT appear more than once in a prospective certification path.

CCP5 : ∀ {@0 bs} → CertList bs → Set
CCP5 c = List.Unique _≟_ (chainToList c)

ccp5 : ∀ {@0 bs} (c : CertList bs) → Dec (CCP5 c)
ccp5 c = List.unique? _≟_ (chainToList c)

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1.2.4
-- Certificate users MUST be prepared to process the Issuer distinguished name
-- and Subject distinguished name fields to perform name chaining for certification path validation.

CCP6 : ∀ {@0 bs} → CertList bs → Set
CCP6 c = CCP6Seq (chainToList c)

ccp6 : ∀ {@0 bs} (c : CertList bs) → Dec (CCP6 c)
ccp6 c = helper (chainToList c)
  where
  helper : (c : List (Exists─ (List UInt8) Cert)) → Dec (CCP6Seq c)
  helper [] = no (λ ())
  helper ((fst , snd) ∷ []) = yes tt
  helper ((fst , snd) ∷ (fst₁ , snd₁) ∷ x₂) = (MatchRDNSeq-dec (Cert.getIssuer snd) (Cert.getSubject snd₁)) ×-dec helper ((fst₁ , snd₁) ∷ x₂)

-- https://datatracker.ietf.org/doc/html/rfc5280#section-6
--- check whether any of the certificate in given chain is trusted by the system's trust anchor

CCP7 : ∀ {@0 as bs} (r : CertList as) → (c : CertList bs) → Set
CCP7 r c = helperCCP7 (chainToList r) (chainToList c)

ccp7 : ∀ {@0 as bs} (r : CertList as) → (c : CertList bs) → Dec (CCP7 r c)
ccp7 r c = helperCCP7-dec (chainToList r) (chainToList c)

-- https://datatracker.ietf.org/doc/html/rfc5280#section-6
--- every issuer certificate in a chain must be CA certificate

CCP10 : ∀ {@0 bs} → CertList bs → Set
CCP10 c = CCP10Seq (chainToList c)

ccp10 : ∀ {@0 bs} (c : CertList bs) → Dec (CCP10 c)
ccp10 c = helper (chainToList c)
  where
  helper : (c : List (Exists─ (List UInt8) Cert)) → Dec (CCP10Seq c)
  helper [] = no λ()
  helper ((fst , snd) ∷ []) = yes tt
  helper ((fst , snd) ∷ (fst₁ , snd₁) ∷ t) = T-dec ×-dec helper ((fst₁ , snd₁) ∷ t)
