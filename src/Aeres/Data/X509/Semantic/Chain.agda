{-# OPTIONS --subtyping #-}

import      Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Properties
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.Semantic.Chain where

open Aeres.Binary
open Base256
open Aeres.Grammar.Definitions Dig


------- helper functions ------


ChainToList : ∀ {@0 bs} → X509.Chain bs  → List (Exists─ (List Dig) X509.Cert)
ChainToList (Aeres.Grammar.Definitions.mk×ₚ (Generic.cons (Generic.mkSequenceOf h t bs≡₁)) sndₚ₁ bs≡) = (_ , h) ∷ helper t
  where
  helper :  ∀ {@0 bs}  → Generic.SequenceOf X509.Cert bs → List (Exists─ (List Dig) X509.Cert)
  helper Generic.nil = []
  helper (Generic.cons (Generic.mkSequenceOf h t bs≡)) = (_ , h) ∷ helper t


CCP2Seq : ∀ {@0 bs} → Generic.SequenceOf X509.Cert bs → Set  
CCP2Seq Generic.nil = ⊤
CCP2Seq (Generic.cons (Generic.mkSequenceOf h Generic.nil bs≡)) = ⊤
CCP2Seq (Generic.cons (Generic.mkSequenceOf h (Generic.cons x) bs≡)) = X509.Cert.getVersion h ≡ ℤ.+ 2 × CCP2Seq (Generic.cons x)


-- TODO: call LDAP StringPrep over val and val₁
MatchRDNATV : ∀ {@0 bs₁ bs₂} → X509.RDNATV bs₁ → X509.RDNATV bs₂ → Set
MatchRDNATV (Generic.mkTLV len (X509.mkRDNATVFields oid val bs≡₂) len≡ bs≡) (Generic.mkTLV len₁ (X509.mkRDNATVFields oid₁ val₁ bs≡₃) len≡₁ bs≡₁) = _≋_ {A = Generic.OID} oid oid₁ × _≋_ {A = X509.DirectoryString} val val₁

data InSeq {bs} (a : X509.RDNATV bs) : (b : List Dig) → Generic.SequenceOf X509.RDNATV b → Set where
  here  : ∀ {bs₁ bs₂ bs₃} {x : X509.RDNATV bs₁} {xs : Generic.SequenceOf X509.RDNATV bs₂} (px : MatchRDNATV a x) (bs≡ : bs₃ ≡ bs₁ ++ bs₂) → InSeq a (bs₃) (Generic.cons (Generic.mkSequenceOf x xs bs≡))
  there : ∀ {bs₁ bs₂ bs₃} {x : X509.RDNATV bs₁} {xs : Generic.SequenceOf X509.RDNATV bs₂} (pxs : InSeq a bs₂ xs) (bs≡ : bs₃ ≡ bs₁ ++ bs₂) → InSeq a (bs₃) (Generic.cons (Generic.mkSequenceOf x xs bs≡))

data AllInSeq {@0 bs} (xs : Generic.SequenceOf X509.RDNATV bs) : (@0 b : List Dig) → Generic.SequenceOf X509.RDNATV b → Set where
  []  : AllInSeq xs [] Generic.nil
  cons : ∀ {bs₁ bs₂ bs₃} {x : X509.RDNATV bs₁} {xs' : Generic.SequenceOf X509.RDNATV bs₂} (px : InSeq x _ xs) (pxs : AllInSeq xs _ xs') (bs≡ : bs₃ ≡ bs₁ ++ bs₂) → AllInSeq xs bs₃ (Generic.cons (Generic.mkSequenceOf x xs' bs≡))

MatchRDNElemsLen : ∀ {@0 bs₁ bs₂} → X509.RDNElems bs₁ → X509.RDNElems bs₂ → Set
MatchRDNElemsLen (Aeres.Grammar.Definitions.mk×ₚ fstₚ₁ sndₚ₁ bs≡) (Aeres.Grammar.Definitions.mk×ₚ fstₚ₂ sndₚ₂ bs≡₁) = (Generic.lengthSequence fstₚ₁) ≡ (Generic.lengthSequence fstₚ₂)

MatchRDN : ∀ {@0 bs₁ bs₂} → X509.RDN bs₁ → X509.RDN bs₂ → Set
MatchRDN (Generic.mkTLV len x@(Aeres.Grammar.Definitions.mk×ₚ fstₚ₁ sndₚ₁ bs≡) len≡ refl) (Generic.mkTLV len₁ x'@(Aeres.Grammar.Definitions.mk×ₚ {bs = bs₂'} fstₚ₂ sndₚ₂ bs≡₁) len≡₁ refl) = (MatchRDNElemsLen x x') × AllInSeq fstₚ₁ bs₂' fstₚ₂

MatchRDNSeqHelper : ∀ {@0 bs₁ bs₂} → Generic.SequenceOfFields X509.RDN bs₁ → Generic.SequenceOfFields X509.RDN bs₂ → Set
MatchRDNSeqHelper (Generic.mkSequenceOf h Generic.nil bs≡) (Generic.mkSequenceOf h₁ Generic.nil bs≡₁) = MatchRDN h h₁
MatchRDNSeqHelper (Generic.mkSequenceOf h Generic.nil bs≡) (Generic.mkSequenceOf h₁ (Generic.cons x) bs≡₁) = MatchRDN h h₁
MatchRDNSeqHelper (Generic.mkSequenceOf h (Generic.cons x) bs≡) (Generic.mkSequenceOf h₁ Generic.nil bs≡₁) = MatchRDN h h₁
MatchRDNSeqHelper (Generic.mkSequenceOf h (Generic.cons x) bs≡) (Generic.mkSequenceOf h₁ (Generic.cons x₁) bs≡₁) = MatchRDN h h₁ × MatchRDNSeqHelper x x₁

MatchRDNSeq : ∀ {@0 bs₁ bs₂} → X509.RDNSeq bs₁ → X509.RDNSeq bs₂ → Set
MatchRDNSeq (Generic.mkTLV len Generic.nil len≡ bs≡) (Generic.mkTLV len₁ Generic.nil len≡₁ bs≡₁) = ⊤
MatchRDNSeq (Generic.mkTLV len Generic.nil len≡ bs≡) (Generic.mkTLV len₁ (Generic.cons x) len≡₁ bs≡₁) = ⊥
MatchRDNSeq (Generic.mkTLV len (Generic.cons x) len≡ bs≡) (Generic.mkTLV len₁ Generic.nil len≡₁ bs≡₁) = ⊥
MatchRDNSeq (Generic.mkTLV len (Generic.cons x) len≡ bs≡) (Generic.mkTLV len₁ (Generic.cons x₁) len≡₁ bs≡₁) = MatchRDNSeqHelper x x₁

CCP6Seq : List (Exists─ (List Dig) X509.Cert) → Set
CCP6Seq [] = ⊥
CCP6Seq ((fst , snd) ∷ []) = MatchRDNSeq (proj₂ (X509.Cert.getIssuer snd)) (proj₂ (X509.Cert.getSubject snd))
CCP6Seq ((fst , snd) ∷ (fst₁ , snd₁) ∷ x₂) = MatchRDNSeq (proj₂ (X509.Cert.getIssuer snd)) (proj₂ (X509.Cert.getSubject snd₁)) × CCP6Seq ((fst₁ , snd₁) ∷ x₂)


----------------- helper decidables -------------------------


postulate
  InSeq-dec : ∀ {bs} (a : X509.RDNATV bs) → (b : List Dig) → (c : Generic.SequenceOf X509.RDNATV b) → Dec (InSeq a b c)
  AllInSeq-dec : ∀ {@0 bs} (xs : Generic.SequenceOf X509.RDNATV bs) → (@0 b : List Dig) → (c : Generic.SequenceOf X509.RDNATV b) → Dec (AllInSeq xs b c)

MatchRDNATV-dec : ∀ {@0 bs₁ bs₂} → (n : X509.RDNATV bs₁) → (m : X509.RDNATV bs₂) → Dec (MatchRDNATV n m)
MatchRDNATV-dec (Generic.mkTLV len (X509.mkRDNATVFields oid val bs≡₂) len≡ bs≡) (Generic.mkTLV len₁ (X509.mkRDNATVFields oid₁ val₁ bs≡₃) len≡₁ bs≡₁) = _≋?_ {A = Generic.OID} oid oid₁ ×-dec _≋?_ {A = X509.DirectoryString} val val₁

MatchRDNElemsLen-dec : ∀ {@0 bs₁ bs₂} → (n : X509.RDNElems bs₁) → (m : X509.RDNElems bs₂) → Dec (MatchRDNElemsLen n m)
MatchRDNElemsLen-dec (Aeres.Grammar.Definitions.mk×ₚ fstₚ₁ sndₚ₁ bs≡) (Aeres.Grammar.Definitions.mk×ₚ fstₚ₂ sndₚ₂ bs≡₁) = (Generic.lengthSequence fstₚ₁) ≟ (Generic.lengthSequence fstₚ₂)

MatchRDN-dec : ∀ {@0 bs₁ bs₂} → (n : X509.RDN bs₁) → (m : X509.RDN bs₂) → Dec (MatchRDN n m)
MatchRDN-dec (Generic.mkTLV len x@(Aeres.Grammar.Definitions.mk×ₚ fstₚ₁ sndₚ₁ bs≡) len≡ refl) (Generic.mkTLV len₁ x'@(Aeres.Grammar.Definitions.mk×ₚ {bs = bs₂'} fstₚ₂ sndₚ₂ bs≡₁) len≡₁ refl) = (MatchRDNElemsLen-dec x x') ×-dec AllInSeq-dec fstₚ₁ bs₂' fstₚ₂

MatchRDNSeq-dec : ∀ {@0 bs₁ bs₂} → (a : X509.RDNSeq bs₁) → (b : X509.RDNSeq bs₂) → Dec (MatchRDNSeq a b)
MatchRDNSeq-dec (Generic.mkTLV len Generic.nil len≡ bs≡) (Generic.mkTLV len₁ Generic.nil len≡₁ bs≡₁) = yes tt
MatchRDNSeq-dec (Generic.mkTLV len Generic.nil len≡ bs≡) (Generic.mkTLV len₁ (Generic.cons x) len≡₁ bs≡₁) = no (λ ())
MatchRDNSeq-dec (Generic.mkTLV len (Generic.cons x) len≡ bs≡) (Generic.mkTLV len₁ Generic.nil len≡₁ bs≡₁) = no (λ ())
MatchRDNSeq-dec (Generic.mkTLV len (Generic.cons x) len≡ bs≡) (Generic.mkTLV len₁ (Generic.cons x₁) len≡₁ bs≡₁) = helper x x₁
  where
  helper : ∀ {@0 bs₁ bs₂} → (a : Generic.SequenceOfFields X509.RDN bs₁) → (b : Generic.SequenceOfFields X509.RDN bs₂) → Dec (MatchRDNSeqHelper a b)
  helper (Generic.mkSequenceOf h Generic.nil bs≡) (Generic.mkSequenceOf h₁ Generic.nil bs≡₁) = MatchRDN-dec h h₁
  helper (Generic.mkSequenceOf h Generic.nil bs≡) (Generic.mkSequenceOf h₁ (Generic.cons x) bs≡₁) = MatchRDN-dec h h₁
  helper (Generic.mkSequenceOf h (Generic.cons x) bs≡) (Generic.mkSequenceOf h₁ Generic.nil bs≡₁) = MatchRDN-dec h h₁
  helper (Generic.mkSequenceOf h (Generic.cons x) bs≡) (Generic.mkSequenceOf h₁ (Generic.cons x₁) bs≡₁) = MatchRDN-dec h h₁ ×-dec helper x x₁


-------------------------- CCP rules ---------------------------------------


-- Conforming implementations may choose to reject all Version 1 and Version 2 intermediate CA certificates
CCP2 : ∀ {@0 bs} → X509.Chain bs → Set
CCP2 (Aeres.Grammar.Definitions.mk×ₚ (Generic.cons (Generic.mkSequenceOf h t bs≡₁)) sndₚ₁ bs≡) = CCP2Seq t

ccp2 : ∀ {@0 bs} (c : X509.Chain bs) → Dec (CCP2 c)
ccp2 (Aeres.Grammar.Definitions.mk×ₚ (Generic.cons (Generic.mkSequenceOf h t bs≡₁)) sndₚ₁ bs≡) = helper t
  where
  helper : ∀ {@0 bs} → (c : Generic.SequenceOf X509.Cert bs) → Dec (CCP2Seq c)  
  helper Generic.nil = yes tt
  helper (Generic.cons (Generic.mkSequenceOf h Generic.nil bs≡)) = yes tt
  helper (Generic.cons (Generic.mkSequenceOf h (Generic.cons x) bs≡)) = (X509.Cert.getVersion h ≟ ℤ.+ 2) ×-dec helper (Generic.cons x)


-- A certificate MUST NOT appear more than once in a prospective certification path.
CCP5 : ∀ {@0 bs} → X509.Chain bs → Set
CCP5 c = List.Unique _≟_ (ChainToList c)

ccp5 : ∀ {@0 bs} (c : X509.Chain bs) → Dec (CCP5 c)
ccp5 c = List.unique? _≟_ (ChainToList c)


-- Certificate users MUST be prepared to process the Issuer distinguished name
-- and Subject distinguished name fields to perform name chaining for certification path validation.
CCP6 : ∀ {@0 bs} → X509.Chain bs → Set
CCP6 c = CCP6Seq (ChainToList c)

ccp6 : ∀ {@0 bs} (c : X509.Chain bs) → Dec (CCP6 c)
ccp6 c = helper (ChainToList c)
  where
  helper : (c : List (Exists─ (List Dig) X509.Cert)) → Dec (CCP6Seq c)
  helper [] = no (λ ())
  helper ((fst , snd) ∷ []) = MatchRDNSeq-dec (proj₂ (X509.Cert.getIssuer snd)) (proj₂ (X509.Cert.getSubject snd))
  helper ((fst , snd) ∷ (fst₁ , snd₁) ∷ x₂) = (MatchRDNSeq-dec (proj₂ (X509.Cert.getIssuer snd)) (proj₂ (X509.Cert.getSubject snd₁))) ×-dec helper ((fst₁ , snd₁) ∷ x₂)
