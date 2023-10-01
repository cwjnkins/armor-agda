{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.GeneralName.TCB
  hiding (module GeneralName)
open import Aeres.Data.X509.RDN
open import Aeres.Data.X690-DER
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.GeneralName.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

Rep =
   Sum OtherName
  (Sum RfcName
  (Sum DnsName
  (Sum X400Address
  (Sum DirName
  (Sum EdipartyName
  (Sum URI
  (Sum IpAddress
       RegID)))))))

equivalent : Equivalent Rep GeneralName
proj₁ equivalent (Sum.inj₁ x) = oname x
proj₁ equivalent (Sum.inj₂ (Sum.inj₁ x)) = rfcname x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))) = dnsname x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))) = x400add x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))) = dirname x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))) = ediname x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))) = uri x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))) = ipadd x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x)))))))) = rid x
proj₂ equivalent (oname x) = inj₁ x
proj₂ equivalent (rfcname x) = inj₂ (inj₁ x)
proj₂ equivalent (dnsname x) = inj₂ (inj₂ (inj₁ x))
proj₂ equivalent (x400add x) = inj₂ (inj₂ (inj₂ (inj₁ x)))
proj₂ equivalent (dirname x) = inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x))))
proj₂ equivalent (ediname x) = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))
proj₂ equivalent (uri x) = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x))))))
proj₂ equivalent (ipadd x) = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))))
proj₂ equivalent (rid x) = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ x)))))))

iso : Iso Rep GeneralName
proj₁ iso = equivalent
proj₁ (proj₂ iso) (Sum.inj₁ x) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₁ x)) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x)))))))) = refl
proj₂ (proj₂ iso) (oname x) = refl
proj₂ (proj₂ iso) (rfcname x) = refl
proj₂ (proj₂ iso) (dnsname x) = refl
proj₂ (proj₂ iso) (x400add x) = refl
proj₂ (proj₂ iso) (dirname x) = refl
proj₂ (proj₂ iso) (ediname x) = refl
proj₂ (proj₂ iso) (uri x) = refl
proj₂ (proj₂ iso) (ipadd x) = refl
proj₂ (proj₂ iso) (rid x) = refl

nonempty : NonEmpty GeneralName
nonempty (oname ()) refl
nonempty (rfcname ()) refl
nonempty (dnsname ()) refl
nonempty (x400add ()) refl
nonempty (dirname ()) refl
nonempty (ediname ()) refl
nonempty (uri ()) refl
nonempty (ipadd ()) refl
nonempty (rid ()) refl

@0 nosubstrings : NoSubstrings GeneralName
nosubstrings x (oname x₁) (oname x₂) = ‼ TLV.nosubstrings x x₁ x₂
nosubstrings x (oname x₁) (rfcname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (oname x₁) (dnsname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (oname x₁) (x400add x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (oname x₁) (dirname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (oname x₁) (ediname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (oname x₁) (uri x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (oname x₁) (ipadd x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (oname x₁) (rid x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rfcname x₁) (oname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rfcname x₁) (rfcname x₂) = ‼ TLV.nosubstrings x x₁ x₂
nosubstrings x (rfcname x₁) (dnsname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rfcname x₁) (x400add x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rfcname x₁) (dirname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rfcname x₁) (ediname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rfcname x₁) (uri x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rfcname x₁) (ipadd x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rfcname x₁) (rid x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dnsname x₁) (oname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dnsname x₁) (rfcname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dnsname x₁) (dnsname x₂) = ‼ TLV.nosubstrings x x₁ x₂
nosubstrings x (dnsname x₁) (x400add x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dnsname x₁) (dirname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dnsname x₁) (ediname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dnsname x₁) (uri x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dnsname x₁) (ipadd x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dnsname x₁) (rid x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (x400add x₁) (oname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (x400add x₁) (rfcname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (x400add x₁) (dnsname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (x400add x₁) (x400add x₂) = ‼ TLV.nosubstrings x x₁ x₂
nosubstrings x (x400add x₁) (dirname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (x400add x₁) (ediname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (x400add x₁) (uri x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (x400add x₁) (ipadd x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (x400add x₁) (rid x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dirname x₁) (oname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dirname x₁) (rfcname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dirname x₁) (dnsname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dirname x₁) (x400add x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dirname x₁) (dirname x₂) = ‼ TLV.nosubstrings x x₁ x₂
nosubstrings x (dirname x₁) (ediname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dirname x₁) (uri x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dirname x₁) (ipadd x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (dirname x₁) (rid x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ediname x₁) (oname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ediname x₁) (rfcname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ediname x₁) (dnsname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ediname x₁) (x400add x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ediname x₁) (dirname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ediname x₁) (ediname x₂) = ‼ TLV.nosubstrings x x₁ x₂
nosubstrings x (ediname x₁) (uri x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ediname x₁) (ipadd x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ediname x₁) (rid x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (uri x₁) (oname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (uri x₁) (rfcname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (uri x₁) (dnsname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (uri x₁) (x400add x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (uri x₁) (dirname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (uri x₁) (ediname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (uri x₁) (uri x₂) = ‼ TLV.nosubstrings x x₁ x₂
nosubstrings x (uri x₁) (ipadd x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (uri x₁) (rid x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ipadd x₁) (oname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ipadd x₁) (rfcname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ipadd x₁) (dnsname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ipadd x₁) (x400add x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ipadd x₁) (dirname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ipadd x₁) (ediname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ipadd x₁) (uri x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (ipadd x₁) (ipadd x₂) = ‼ TLV.nosubstrings x x₁ x₂
nosubstrings x (ipadd x₁) (rid x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rid x₁) (oname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rid x₁) (rfcname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rid x₁) (dnsname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rid x₁) (x400add x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rid x₁) (dirname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rid x₁) (ediname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rid x₁) (uri x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rid x₁) (ipadd x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (rid x₁) (rid x₂) = ‼ TLV.nosubstrings x x₁ x₂

module GeneralName where
  @0 unambiguous : Unambiguous GeneralName
  unambiguous =
    Iso.unambiguous iso
      (Sum.unambiguous (TLV.unambiguous OctetString.unambiguous)
        ua₁ nc₀)
    where
    Rep₇ = Sum IpAddress RegID
    Rep₆ = Sum URI Rep₇
    Rep₅ = Sum EdipartyName Rep₆
    Rep₄ = Sum DirName Rep₅
    Rep₃ = Sum X400Address Rep₄
    Rep₂ = Sum DnsName Rep₃
    Rep₁ = Sum RfcName Rep₂

    nc₇ : NoConfusion IpAddress RegID
    nc₇ = TLV.noconfusion λ ()

    ua₇ : Unambiguous Rep₇
    ua₇ = Sum.unambiguous
            (TLV.unambiguous OctetString.unambiguous)
            (TLV.unambiguous
              (SequenceOf.Bounded.unambiguous OID.Sub.unambiguous OID.Sub.nonempty OID.Sub.nosubstrings))
            nc₇

    nc₆ : NoConfusion URI Rep₇
    nc₆ = NoConfusion.sumₚ{A = URI} (TLV.noconfusion (λ ())) (TLV.noconfusion λ ())

    ua₆ : Unambiguous Rep₆
    ua₆ = Sum.unambiguous (TLV.unambiguous IA5String.unambiguous) ua₇ nc₆

    nc₅ : NoConfusion EdipartyName Rep₆
    nc₅ = NoConfusion.sumₚ{A = EdipartyName}
            (TLV.noconfusion λ ())
            (NoConfusion.sumₚ{A = EdipartyName} (TLV.noconfusion (λ ()))
              (TLV.noconfusion λ ()))

    ua₅ : Unambiguous Rep₅
    ua₅ = Sum.unambiguous (TLV.unambiguous OctetString.unambiguous)
            ua₆ nc₅

    nc₄ : NoConfusion DirName Rep₅
    nc₄ = NoConfusion.sumₚ {A = DirName}
            (TLV.noconfusion λ ())
            (NoConfusion.sumₚ {A = DirName}
              (TLV.noconfusion λ ())
              (NoConfusion.sumₚ {A = DirName}
                (TLV.noconfusion λ ()) (TLV.noconfusion λ ())))

    ua₄ : Unambiguous Rep₄
    ua₄ = Sum.unambiguous (TLV.unambiguous RDN.unambiguous) ua₅ nc₄

    nc₃ : NoConfusion X400Address Rep₄
    nc₃ = NoConfusion.sumₚ {A = X400Address}
            (TLV.noconfusion λ ())
            (NoConfusion.sumₚ{A = X400Address}
              (TLV.noconfusion λ ())
              (NoConfusion.sumₚ{A = X400Address}
                (TLV.noconfusion λ ())
                (NoConfusion.sumₚ {A = X400Address}
                  (TLV.noconfusion λ ()) (TLV.noconfusion λ ()))))

    ua₃ : Unambiguous Rep₃
    ua₃ = Sum.unambiguous (TLV.unambiguous OctetString.unambiguous)
            ua₄ nc₃

    nc₂ : NoConfusion DnsName Rep₃
    nc₂ = NoConfusion.sumₚ{A = DnsName}
            (TLV.noconfusion λ ())
            (NoConfusion.sumₚ {A = DnsName}
              (TLV.noconfusion λ ())
              (NoConfusion.sumₚ {A = DnsName}
                (TLV.noconfusion λ ())
                (NoConfusion.sumₚ {A = DnsName} (TLV.noconfusion λ ())
                  (NoConfusion.sumₚ {A = DnsName} (TLV.noconfusion λ ()) (TLV.noconfusion λ ())))))

    ua₂ : Unambiguous Rep₂
    ua₂ = Sum.unambiguous (TLV.unambiguous IA5String.unambiguous)
            ua₃ nc₂

    nc₁ : NoConfusion RfcName Rep₂
    nc₁ = NoConfusion.sumₚ {A = RfcName}
            (TLV.noconfusion λ ())
            (NoConfusion.sumₚ {A = RfcName}
              (TLV.noconfusion λ ())
              (NoConfusion.sumₚ {A = RfcName}
                (TLV.noconfusion λ ())
                (NoConfusion.sumₚ {A = RfcName}
                  (TLV.noconfusion λ ())
                  (NoConfusion.sumₚ {A = RfcName}
                    (TLV.noconfusion λ ())
                    (NoConfusion.sumₚ {A = RfcName}
                      (TLV.noconfusion λ ()) (TLV.noconfusion λ ()))))))

    ua₁ : Unambiguous Rep₁
    ua₁ = Sum.unambiguous (TLV.unambiguous IA5String.unambiguous)
            ua₂ nc₁

    nc₀ : NoConfusion OtherName Rep₁
    nc₀ = NoConfusion.sumₚ {A = OtherName} (TLV.noconfusion λ ())
            (NoConfusion.sumₚ {A = OtherName} (TLV.noconfusion λ ())
              (NoConfusion.sumₚ {A = OtherName} (TLV.noconfusion λ ())
                (NoConfusion.sumₚ {A = OtherName} (TLV.noconfusion λ ())
                  (NoConfusion.sumₚ {A = OtherName} (TLV.noconfusion λ ())
                    (NoConfusion.sumₚ {A = OtherName} (TLV.noconfusion λ ())
                      (NoConfusion.sumₚ {A = OtherName} (TLV.noconfusion λ ())
                        (TLV.noconfusion λ ())))))))

module GeneralNamesElems where
  @0 unambiguous : Unambiguous GeneralNamesElems
  unambiguous =
    SequenceOf.Bounded.unambiguous
      GeneralName.unambiguous nonempty nosubstrings

module GeneralNames where
  @0 unambiguous : Unambiguous GeneralNames
  unambiguous = TLV.unambiguous GeneralNamesElems.unambiguous

@0 unambiguous : _
unambiguous = GeneralName.unambiguous
