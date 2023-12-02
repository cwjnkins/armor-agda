open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Val.RSA.Ints.TCB
  hiding (equivalent)
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions.Iso
import      Aeres.Grammar.Definitions.NonMalleable
import      Aeres.Grammar.Seq.TCB
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.RSA.TCB where

open import Aeres.Grammar.Definitions.Iso          UInt8
open import Aeres.Grammar.Definitions.NonMalleable UInt8
open import Aeres.Grammar.Seq.TCB                  UInt8

record RSABitStringFields (@0 bs : List UInt8) : Set where
  constructor mkRSABitStringFields
  field
    @0 {neseq} : List UInt8
    z : Singleton ([ # 0 ]) 
    rsane : RSAPkInts neseq
    @0 bs≡ : bs ≡ (Singleton.x z) ++ neseq

RSABitStringFieldsRep : @0 List UInt8 → Set
RSABitStringFieldsRep = &ₚ (λ x → Erased (x ≡ [ # 0 ])) RSAPkInts

equivalent : Equivalent RSABitStringFieldsRep RSABitStringFields
proj₁ equivalent (mk&ₚ (─ refl) sndₚ₁ bs≡) = mkRSABitStringFields self sndₚ₁ bs≡
proj₂ equivalent (mkRSABitStringFields self rsane bs≡) = mk&ₚ (─ refl) rsane bs≡

RawRSABitStringFieldsRep : Raw RSABitStringFieldsRep
RawRSABitStringFieldsRep = Raw&ₚ RawSubSingleton RawRSAPkInts

RawRSABitStringFields : Raw RSABitStringFields
RawRSABitStringFields = Iso.raw equivalent RawRSABitStringFieldsRep

RSABitString : @0 List UInt8 → Set
RSABitString xs = TLV Tag.BitString RSABitStringFields xs

RawRSABitString : Raw RSABitString
RawRSABitString = RawTLV _ RawRSABitStringFields
