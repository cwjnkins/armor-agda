{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.IA5StringValue   as IA5Props
import      Aeres.Data.X509.Properties.OID              as OIDProps
import      Aeres.Data.X509.Properties.OIDSub           as OIDSubProps
import      Aeres.Data.X509.Properties.OctetstringValue as OSProps
import      Aeres.Data.X509.Properties.RDNSeq           as RDNProps
import      Aeres.Data.X509.Properties.TLV              as TLVProps
import      Aeres.Data.X509.Properties.SequenceOf       as SeqProps
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Properties.GeneralName where

open Base256
open Aeres.Grammar.Definitions Dig
open Aeres.Grammar.Properties Dig
open Aeres.Grammar.Sum Dig

equivalent
  : Equivalent
      (Sum X509.OtherName
      (Sum X509.RfcName
      (Sum X509.DnsName
      (Sum X509.X400Address
      (Sum X509.DirName
      (Sum X509.EdipartyName
      (Sum X509.URI
      (Sum X509.IpAddress
           X509.RegID))))))))
      X509.GeneralName
proj₁ equivalent (Sum.inj₁ x) = X509.oname x
proj₁ equivalent (Sum.inj₂ (Sum.inj₁ x)) = X509.rfcname x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))) = X509.dnsname x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))) = X509.x400add x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))) = X509.dirname x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))) = X509.ediname x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))) = X509.uri x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))) = X509.ipadd x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x)))))))) = X509.rid x
proj₂ equivalent (X509.oname x) = inj₁ x
proj₂ equivalent (X509.rfcname x) = inj₂ (inj₁ x)
proj₂ equivalent (X509.dnsname x) = inj₂ (inj₂ (inj₁ x))
proj₂ equivalent (X509.x400add x) = inj₂ (inj₂ (inj₂ (inj₁ x)))
proj₂ equivalent (X509.dirname x) = inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x))))
proj₂ equivalent (X509.ediname x) = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))
proj₂ equivalent (X509.uri x) = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x))))))
proj₂ equivalent (X509.ipadd x) = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))))
proj₂ equivalent (X509.rid x) = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ x)))))))

iso
  : Iso
      (Sum X509.OtherName
      (Sum X509.RfcName
      (Sum X509.DnsName
      (Sum X509.X400Address
      (Sum X509.DirName
      (Sum X509.EdipartyName
      (Sum X509.URI
      (Sum X509.IpAddress
           X509.RegID))))))))
      X509.GeneralName
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
proj₂ (proj₂ iso) (X509.oname x) = refl
proj₂ (proj₂ iso) (X509.rfcname x) = refl
proj₂ (proj₂ iso) (X509.dnsname x) = refl
proj₂ (proj₂ iso) (X509.x400add x) = refl
proj₂ (proj₂ iso) (X509.dirname x) = refl
proj₂ (proj₂ iso) (X509.ediname x) = refl
proj₂ (proj₂ iso) (X509.uri x) = refl
proj₂ (proj₂ iso) (X509.ipadd x) = refl
proj₂ (proj₂ iso) (X509.rid x) = refl

nonempty : NonEmpty X509.GeneralName
nonempty (X509.oname ()) refl
nonempty (X509.rfcname ()) refl
nonempty (X509.dnsname ()) refl
nonempty (X509.x400add ()) refl
nonempty (X509.dirname ()) refl
nonempty (X509.ediname ()) refl
nonempty (X509.uri ()) refl
nonempty (X509.ipadd ()) refl
nonempty (X509.rid ()) refl

@0 nonnesting : NonNesting X509.GeneralName
nonnesting x (X509.oname x₁) (X509.oname x₂) = ‼ TLVProps.nonnesting x x₁ x₂
nonnesting x (X509.oname x₁) (X509.rfcname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.oname x₁) (X509.dnsname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.oname x₁) (X509.x400add x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.oname x₁) (X509.dirname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.oname x₁) (X509.ediname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.oname x₁) (X509.uri x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.oname x₁) (X509.ipadd x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.oname x₁) (X509.rid x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.rfcname x₁) (X509.oname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.rfcname x₁) (X509.rfcname x₂) = ‼ TLVProps.nonnesting x x₁ x₂
nonnesting x (X509.rfcname x₁) (X509.dnsname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.rfcname x₁) (X509.x400add x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.rfcname x₁) (X509.dirname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.rfcname x₁) (X509.ediname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.rfcname x₁) (X509.uri x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.rfcname x₁) (X509.ipadd x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.rfcname x₁) (X509.rid x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.dnsname x₁) (X509.oname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.dnsname x₁) (X509.rfcname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.dnsname x₁) (X509.dnsname x₂) = ‼ TLVProps.nonnesting x x₁ x₂
nonnesting x (X509.dnsname x₁) (X509.x400add x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.dnsname x₁) (X509.dirname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.dnsname x₁) (X509.ediname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.dnsname x₁) (X509.uri x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.dnsname x₁) (X509.ipadd x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.dnsname x₁) (X509.rid x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.x400add x₁) (X509.oname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.x400add x₁) (X509.rfcname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.x400add x₁) (X509.dnsname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.x400add x₁) (X509.x400add x₂) = ‼ TLVProps.nonnesting x x₁ x₂
nonnesting x (X509.x400add x₁) (X509.dirname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.x400add x₁) (X509.ediname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.x400add x₁) (X509.uri x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.x400add x₁) (X509.ipadd x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.x400add x₁) (X509.rid x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.dirname x₁) (X509.oname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.dirname x₁) (X509.rfcname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.dirname x₁) (X509.dnsname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.dirname x₁) (X509.x400add x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.dirname x₁) (X509.dirname x₂) = ‼ TLVProps.nonnesting x x₁ x₂
nonnesting x (X509.dirname x₁) (X509.ediname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.dirname x₁) (X509.uri x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.dirname x₁) (X509.ipadd x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.dirname x₁) (X509.rid x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.ediname x₁) (X509.oname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.ediname x₁) (X509.rfcname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.ediname x₁) (X509.dnsname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.ediname x₁) (X509.x400add x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.ediname x₁) (X509.dirname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.ediname x₁) (X509.ediname x₂) = ‼ TLVProps.nonnesting x x₁ x₂
nonnesting x (X509.ediname x₁) (X509.uri x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.ediname x₁) (X509.ipadd x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.ediname x₁) (X509.rid x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.uri x₁) (X509.oname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.uri x₁) (X509.rfcname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.uri x₁) (X509.dnsname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.uri x₁) (X509.x400add x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.uri x₁) (X509.dirname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.uri x₁) (X509.ediname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.uri x₁) (X509.uri x₂) = ‼ TLVProps.nonnesting x x₁ x₂
nonnesting x (X509.uri x₁) (X509.ipadd x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.uri x₁) (X509.rid x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.ipadd x₁) (X509.oname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.ipadd x₁) (X509.rfcname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.ipadd x₁) (X509.dnsname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.ipadd x₁) (X509.x400add x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.ipadd x₁) (X509.dirname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.ipadd x₁) (X509.ediname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.ipadd x₁) (X509.uri x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.ipadd x₁) (X509.ipadd x₂) = ‼ TLVProps.nonnesting x x₁ x₂
nonnesting x (X509.ipadd x₁) (X509.rid x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.rid x₁) (X509.oname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.rid x₁) (X509.rfcname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.rid x₁) (X509.dnsname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.rid x₁) (X509.x400add x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.rid x₁) (X509.dirname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.rid x₁) (X509.ediname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.rid x₁) (X509.uri x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.rid x₁) (X509.ipadd x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.rid x₁) (X509.rid x₂) = ‼ TLVProps.nonnesting x x₁ x₂

module GeneralName where
  @0 unambiguous : Unambiguous X509.GeneralName
  unambiguous =
    isoUnambiguous iso
      (unambiguousSum
        (TLVProps.unambiguous OSProps.unambiguous)
        (unambiguousSum (TLVProps.unambiguous IA5Props.unambiguous)
          (unambiguousSum (TLVProps.unambiguous IA5Props.unambiguous)
            (unambiguousSum (TLVProps.unambiguous OSProps.unambiguous)
              (unambiguousSum
                (TLVProps.unambiguous
                  (SeqProps.unambiguous
                    RDNProps.RDN.unambiguous TLVProps.nonempty TLVProps.nonnesting))
                (unambiguousSum
                  (TLVProps.unambiguous OSProps.unambiguous)
                  (unambiguousSum (TLVProps.unambiguous IA5Props.unambiguous)
                    (unambiguousSum (TLVProps.unambiguous OSProps.unambiguous)
                      (TLVProps.unambiguous
                        (SeqProps.BoundedSequenceOf.unambiguous
                          OIDSubProps.unambiguous OIDSubProps.nonempty OIDSubProps.nonnesting))
                        (TLVProps.noconfusion λ ()))
                      (NoConfusion.sumₚ{A = X509.URI} (TLVProps.noconfusion λ ())
                        (TLVProps.noconfusion λ ())))
                    (NoConfusion.sumₚ{A = X509.EdipartyName} (TLVProps.noconfusion λ ())
                      (NoConfusion.sumₚ{A = X509.EdipartyName} (TLVProps.noconfusion λ ())
                        (TLVProps.noconfusion λ ()))))
                (NoConfusion.sumₚ{A = X509.DirName} (TLVProps.noconfusion (λ ()))
                  (NoConfusion.sumₚ{A = X509.DirName} (TLVProps.noconfusion (λ ()))
                    (NoConfusion.sumₚ{A = X509.DirName} (TLVProps.noconfusion (λ ())) (TLVProps.noconfusion λ ())))))
              (NoConfusion.sumₚ{A = X509.X400Address} (TLVProps.noconfusion (λ ()))
                (NoConfusion.sumₚ{A = X509.X400Address} (TLVProps.noconfusion (λ ()))
                  (NoConfusion.sumₚ{A = X509.X400Address} (TLVProps.noconfusion (λ ()))
                    (NoConfusion.sumₚ{A = X509.X400Address} (TLVProps.noconfusion (λ ())) (TLVProps.noconfusion λ ()))))))
            (NoConfusion.sumₚ{A = X509.DnsName} (TLVProps.noconfusion (λ ()))
              (NoConfusion.sumₚ{A = X509.DnsName} (TLVProps.noconfusion (λ ()))
                (NoConfusion.sumₚ{A = X509.DnsName} (TLVProps.noconfusion (λ ()))
                  (NoConfusion.sumₚ{A = X509.DnsName} (TLVProps.noconfusion (λ ()))
                    (NoConfusion.sumₚ{A = X509.DnsName} (TLVProps.noconfusion (λ ())) (TLVProps.noconfusion λ ())))))))
          (NoConfusion.sumₚ{A = X509.RfcName} (TLVProps.noconfusion (λ ()))
            (NoConfusion.sumₚ{A = X509.RfcName} (TLVProps.noconfusion (λ ()))
              (NoConfusion.sumₚ{A = X509.RfcName} (TLVProps.noconfusion (λ ()))
                (NoConfusion.sumₚ{A = X509.RfcName} (TLVProps.noconfusion (λ ()))
                  (NoConfusion.sumₚ{A = X509.RfcName} (TLVProps.noconfusion (λ ()))
                    (NoConfusion.sumₚ{A = X509.RfcName} (TLVProps.noconfusion (λ ())) (TLVProps.noconfusion λ ()))))))))
        (NoConfusion.sumₚ{A = X509.OtherName} (TLVProps.noconfusion (λ ()))
          (NoConfusion.sumₚ{A = X509.OtherName} (TLVProps.noconfusion (λ ()))
            (NoConfusion.sumₚ{A = X509.OtherName} (TLVProps.noconfusion (λ ()))
              (NoConfusion.sumₚ{A = X509.OtherName} (TLVProps.noconfusion (λ ()))
                (NoConfusion.sumₚ{A = X509.OtherName} (TLVProps.noconfusion (λ ()))
                  (NoConfusion.sumₚ{A = X509.OtherName} (TLVProps.noconfusion (λ ()))
                    (NoConfusion.sumₚ{A = X509.OtherName}
                       (TLVProps.noconfusion (λ ())) (TLVProps.noconfusion λ ())))))))))

module GeneralNamesElems where
  @0 unambiguous : Unambiguous X509.GeneralNamesElems
  unambiguous =
    SeqProps.BoundedSequenceOf.unambiguous
      GeneralName.unambiguous nonempty nonnesting

module GeneralNames where
  @0 unambiguous : Unambiguous X509.GeneralNames
  unambiguous = TLVProps.unambiguous GeneralNamesElems.unambiguous

@0 unambiguous : _
unambiguous = GeneralName.unambiguous
