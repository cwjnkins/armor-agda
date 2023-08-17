{-# OPTIONS --subtyping --sized-types #-}

import      Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Semantic.StringPrep.Exec
open import Aeres.Data.X509.Semantic.Cert
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
open import Aeres.Grammar.IList as IList
open import Aeres.Prelude

module Aeres.Data.X509.Semantic.Chain where

open Aeres.Binary
open Base256
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Definitions Dig


------- helper functions ------

ChainToList : ∀ {@0 bs} → Chain bs  → List (Exists─ (List UInt8) Cert)
ChainToList (Aeres.Grammar.Definitions.mk×ₚ (cons (mkIListCons h t bs≡₁)) sndₚ₁ bs≡) = (_ , h) ∷ helper t
  where
  helper :  ∀ {@0 bs}  → SequenceOf Cert bs → List (Exists─ (List Dig) Cert)
  helper nil = []
  helper (cons (mkSequenceOf h t bs≡)) = (_ , h) ∷ helper t


CCP2Seq : ∀ {@0 bs} → SequenceOf Cert bs → Set  
CCP2Seq nil = ⊤
CCP2Seq (cons (mkSequenceOf h nil bs≡)) = ⊤
CCP2Seq (cons (mkSequenceOf h (cons x) bs≡)) = Cert.getVersion h ≡ ℤ.+ 2 × CCP2Seq (cons x)

MatchRDNATV : ∀ {@0 bs₁ bs₂} → RDNATV bs₁ → RDNATV bs₂ → Set
MatchRDNATV (mkTLV len (mkRDNATVFields oid val bs≡₂) len≡ bs≡) (mkTLV len₁ (mkRDNATVFields oid₁ val₁ bs≡₃) len≡₁ bs≡₁) = _≋_ {A = OID} oid oid₁ × Compare val val₁

data InSeq {@0 bs} (a : RDNATV bs) : (@0 b : List Dig) → SequenceOf RDNATV b → Set where
  here  : ∀ {@0 bs₁ bs₂ bs₃} {x : RDNATV bs₁} {xs : SequenceOf RDNATV bs₂} (px : MatchRDNATV a x) (@0 bs≡ : bs₃ ≡ bs₁ ++ bs₂) → InSeq a (bs₃) (cons (mkSequenceOf x xs bs≡))
  there : ∀ {@0 bs₁ bs₂ bs₃} {x : RDNATV bs₁} {xs : SequenceOf RDNATV bs₂} (pxs : InSeq a bs₂ xs) (@0 bs≡ : bs₃ ≡ bs₁ ++ bs₂) → InSeq a (bs₃) (cons (mkSequenceOf x xs bs≡))

data AllInSeq {@0 bs} (xs : SequenceOf RDNATV bs) : (@0 b : List Dig) → SequenceOf RDNATV b → Set where
  []  : AllInSeq xs [] nil
  cons : ∀ {@0 bs₁ bs₂ bs₃} {x : RDNATV bs₁} {xs' : SequenceOf RDNATV bs₂} (px : InSeq x _ xs) (pxs : AllInSeq xs _ xs') (@0 bs≡ : bs₃ ≡ bs₁ ++ bs₂) → AllInSeq xs bs₃ (cons (mkSequenceOf x xs' bs≡))

MatchRDNElemsLen : ∀ {@0 bs₁ bs₂} → RDNElems bs₁ → RDNElems bs₂ → Set
MatchRDNElemsLen (Aeres.Grammar.Definitions.mk×ₚ fstₚ₁ sndₚ₁ bs≡) (Aeres.Grammar.Definitions.mk×ₚ fstₚ₂ sndₚ₂ bs≡₁) = (lengthSequence fstₚ₁) ≡ (lengthSequence fstₚ₂)

MatchRDN : ∀ {@0 bs₁ bs₂} → RDN bs₁ → RDN bs₂ → Set
MatchRDN (mkTLV len x@(Aeres.Grammar.Definitions.mk×ₚ fstₚ₁ sndₚ₁ bs≡) len≡ refl) (mkTLV len₁ x'@(Aeres.Grammar.Definitions.mk×ₚ {bs = bs₂'} fstₚ₂ sndₚ₂ bs≡₁) len≡₁ refl) = (MatchRDNElemsLen x x') × AllInSeq fstₚ₁ bs₂' fstₚ₂

MatchRDNSeqHelper : ∀ {@0 bs₁ bs₂} → SequenceOfFields RDN bs₁ → SequenceOfFields RDN bs₂ → Set
MatchRDNSeqHelper (mkSequenceOf h nil bs≡) (mkSequenceOf h₁ nil bs≡₁) = MatchRDN h h₁
MatchRDNSeqHelper (mkSequenceOf h nil bs≡) (mkSequenceOf h₁ (cons x) bs≡₁) = MatchRDN h h₁
MatchRDNSeqHelper (mkSequenceOf h (cons x) bs≡) (mkSequenceOf h₁ nil bs≡₁) = MatchRDN h h₁
MatchRDNSeqHelper (mkSequenceOf h (cons x) bs≡) (mkSequenceOf h₁ (cons x₁) bs≡₁) = MatchRDN h h₁ × MatchRDNSeqHelper x x₁

MatchRDNSeq : ∀ {@0 bs₁ bs₂} → RDNSeq bs₁ → RDNSeq bs₂ → Set
MatchRDNSeq (mkTLV len nil len≡ bs≡) (mkTLV len₁ nil len≡₁ bs≡₁) = ⊤
MatchRDNSeq (mkTLV len nil len≡ bs≡) (mkTLV len₁ (cons x) len≡₁ bs≡₁) = ⊥
MatchRDNSeq (mkTLV len (cons x) len≡ bs≡) (mkTLV len₁ nil len≡₁ bs≡₁) = ⊥
MatchRDNSeq (mkTLV len (cons x) len≡ bs≡) (mkTLV len₁ (cons x₁) len≡₁ bs≡₁) = MatchRDNSeqHelper x x₁

CCP6Seq : List (Exists─ (List Dig) Cert) → Set
CCP6Seq [] = ⊥
CCP6Seq ((fst , snd) ∷ []) = MatchRDNSeq (proj₂ (Cert.getIssuer snd)) (proj₂ (Cert.getSubject snd))
CCP6Seq ((fst , snd) ∷ (fst₁ , snd₁) ∷ x₂) = MatchRDNSeq (proj₂ (Cert.getIssuer snd)) (proj₂ (Cert.getSubject snd₁)) × CCP6Seq ((fst₁ , snd₁) ∷ x₂)

CCP10Seq : List (Exists─ (List UInt8) Cert) → Set
CCP10Seq [] = ⊤
CCP10Seq ((fst , snd) ∷ []) = T (isCA (Cert.getBC snd))
CCP10Seq ((fst , snd) ∷ (fst₁ , snd₁) ∷ x₁) = T (isCA (Cert.getBC snd₁)) × CCP10Seq x₁

----------------- helper decidables -------------------------

MatchRDNATV-dec : ∀ {@0 bs₁ bs₂} → (n : RDNATV bs₁) → (m : RDNATV bs₂) → Dec (MatchRDNATV n m)
MatchRDNATV-dec (mkTLV len (mkRDNATVFields oid val bs≡₂) len≡ bs≡) (mkTLV len₁ (mkRDNATVFields oid₁ val₁ bs≡₃) len≡₁ bs≡₁) = _≋?_ {A = OID} oid oid₁ ×-dec Compare-dec val val₁

InSeq-dec : ∀ {@0 bs} (a : RDNATV bs) → (@0 b : List Dig) → (c : SequenceOf RDNATV b) → Dec (InSeq a b c)
InSeq-dec a .[] nil = no (λ ())
InSeq-dec a b (cons (mkIListCons {bs₂ = g} head₁ tail₁ bs≡)) = case MatchRDNATV-dec a head₁ of λ where
  (no ¬p) → case (InSeq-dec a g tail₁) ret (const _) of λ where
    (no ¬q) → no λ where
      (here px .bs≡) → contradiction px ¬p
      (there x .bs≡) → contradiction x ¬q
    (yes p) → yes (there p bs≡)
  (yes p) → yes (here p bs≡)

AllInSeq-dec : ∀ {@0 bs} (xs : SequenceOf RDNATV bs) → (@0 b : List Dig) → (c : SequenceOf RDNATV b) → Dec (AllInSeq xs b c)
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

MatchRDNSeq-dec : ∀ {@0 bs₁ bs₂} → (a : RDNSeq bs₁) → (b : RDNSeq bs₂) → Dec (MatchRDNSeq a b)
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
CCP2 (Aeres.Grammar.Definitions.mk×ₚ (cons (mkSequenceOf h t bs≡₁)) sndₚ₁ bs≡) = CCP2Seq t

ccp2 : ∀ {@0 bs} (c : Chain bs) → Dec (CCP2 c)
ccp2 (Aeres.Grammar.Definitions.mk×ₚ (cons (mkSequenceOf h t bs≡₁)) sndₚ₁ bs≡) = helper t
  where
  helper : ∀ {@0 bs} → (c : SequenceOf Cert bs) → Dec (CCP2Seq c)  
  helper nil = yes tt
  helper (cons (mkSequenceOf h nil bs≡)) = yes tt
  helper (cons (mkSequenceOf h (cons x) bs≡)) = (Cert.getVersion h ≟ ℤ.+ 2) ×-dec helper (cons x)

--- The PathLenConstraint field is meaningful only if the CA boolean
--- is asserted and the Key Usage extension, if present, asserts the KeyCertSign bit. In this case, it gives
--- the maximum number of non-self-issued intermediate certificates that may follow this certificate in a valid certification path.
CCP3 : ∀ {@0 bs} → Chain bs → Set
CCP3 c = CCP3Seq (reverse (ChainToList c))

ccp3 : ∀ {@0 bs} (c : Chain bs) → Dec (CCP3 c)
ccp3 c = CCP3Seq-dec (reverse (ChainToList c))
  where
  CCP3Seq-dec : (c : List (Exists─ (List Dig) Cert)) → Dec (CCP3Seq c)
  CCP3Seq-dec [] = yes tt
  CCP3Seq-dec (x ∷ x₁) = helperCCP3-dec x x₁ ×-dec CCP3Seq-dec x₁

-- A certificate MUST NOT appear more than once in a prospective certification path.
CCP5 : ∀ {@0 bs} → Chain bs → Set
CCP5 c = List.Unique _≟_ (ChainToList c)

ccp5 : ∀ {@0 bs} (c : Chain bs) → Dec (CCP5 c)
ccp5 c = List.unique? _≟_ (ChainToList c)

-- Certificate users MUST be prepared to process the Issuer distinguished name
-- and Subject distinguished name fields to perform name chaining for certification path validation.
CCP6 : ∀ {@0 bs} → Chain bs → Set
CCP6 c = CCP6Seq (ChainToList c)

ccp6 : ∀ {@0 bs} (c : Chain bs) → Dec (CCP6 c)
ccp6 c = helper (ChainToList c)
  where
  helper : (c : List (Exists─ (List Dig) Cert)) → Dec (CCP6Seq c)
  helper [] = no (λ ())
  helper ((fst , snd) ∷ []) = MatchRDNSeq-dec (proj₂ (Cert.getIssuer snd)) (proj₂ (Cert.getSubject snd))
  helper ((fst , snd) ∷ (fst₁ , snd₁) ∷ x₂) = (MatchRDNSeq-dec (proj₂ (Cert.getIssuer snd)) (proj₂ (Cert.getSubject snd₁))) ×-dec helper ((fst₁ , snd₁) ∷ x₂)

--- every issuer certificate in a chain must be CA certificate
CCP10 : ∀ {@0 bs} → Chain bs → Set
CCP10 c = CCP10Seq (ChainToList c)

ccp10 : ∀ {@0 bs} (c : Chain bs) → Dec (CCP10 c)
ccp10 c = helper (ChainToList c)
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
