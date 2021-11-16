{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.Primitives as PrimProps
import      Aeres.Data.X509.Properties.OID as OIDProps
import      Aeres.Data.X509.Properties.TLV as TLVProps
open import Aeres.Prelude

module Aeres.Data.X509.Properties.Extension where

open Base256
open import Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Properties  Dig
open import Aeres.Grammar.Sum Dig

module ExtensionFields where
  equivalent : ∀ {@0 P} {@0 A : @0 List Dig → Set}
               → Equivalent
                   (&ₚ (Generic.OID ×ₚ (Erased ∘ P))
                       (&ₚ (Option Generic.Boool)
                           A))
                   (X509.ExtensionFields P A)
  proj₁ equivalent (mk&ₚ (mk×ₚ fstₚ₁ (─ sndₚ₁) refl) (mk&ₚ fstₚ₂ sndₚ₂ refl) refl) =
    X509.mkExtensionFields fstₚ₁ sndₚ₁ fstₚ₂ sndₚ₂ refl
  proj₂ equivalent (X509.mkExtensionFields extnId extnId≡ crit extension refl) =
    mk&ₚ (mk×ₚ extnId (─ extnId≡) refl) (mk&ₚ crit extension refl) refl

  iso : ∀ {@0 P} {@0 A : @0 List Dig → Set}
        → Iso
            (&ₚ (Generic.OID ×ₚ (Erased ∘ P))
                (&ₚ (Option Generic.Boool)
                    A))
            (X509.ExtensionFields P A)
  proj₁ iso = equivalent
  proj₁ (proj₂ iso) (mk&ₚ (mk×ₚ fstₚ₁ (─ sndₚ₁) refl) (mk&ₚ fstₚ₂ sndₚ₂ refl) refl) = refl
  proj₂ (proj₂ iso) (X509.mkExtensionFields extnId extnId≡ crit extension refl) = refl

  @0 unambiguous : ∀ {@0 P}{@0 A : @0 List Dig → Set} → Unambiguous P → Unambiguous A → NoConfusion Generic.Boool A → Unambiguous (X509.ExtensionFields P A)
  unambiguous ua₁ ua₂ nc =
    isoUnambiguous iso
      (unambiguous&ₚ
        (unambiguous×ₚ OIDProps.unambiguous (erased-unique ua₁))
        (nonnesting×ₚ₁ TLVProps.nonnesting)
        (Unambiguous.unambiguous-option₁&₁ (TLVProps.unambiguous PrimProps.BoolValue.unambiguous) TLVProps.nonnesting ua₂ nc))

module SelectExtn where
  equivalent : Equivalent
                 (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.AKI      )            X509.AKIFields)
                 (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.SKI      )            X509.SKIFields)
                 (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.KU       )            X509.KUFields)
                 (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.EKU      )            X509.EKUFields)
                 (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.BC       )            X509.BCFields)
                 (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.IAN      )            X509.IANFields)
                 (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.SAN      )            X509.SANFields)
                 (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.CPOL     )            X509.CertPolFields)
                 (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.CRLDIST  )            X509.CRLDistFields)
                 (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.AIA      )            X509.AIAFields)
                      (X509.ExtensionFields (False ∘ (_∈? X509.ExtensionOID.Supported)) Generic.Octetstring)))))))))))
                 X509.SelectExtn
  proj₁ equivalent (Sum.inj₁ x) = X509.akiextn x
  proj₁ equivalent (Sum.inj₂ (Sum.inj₁ x)) = X509.skiextn x
  proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))) = X509.kuextn x
  proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))) = X509.ekuextn x
  proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))) = X509.bcextn x
  proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))) = X509.ianextn x
  proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))) = X509.sanextn x
  proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))) = X509.cpextn x
  proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))))) = X509.crlextn x
  proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))))) = X509.aiaextn x
  proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x)))))))))) = X509.other x
  proj₂ equivalent (X509.akiextn x) = Sum.inj₁ x
  proj₂ equivalent (X509.skiextn x) = Sum.inj₂ ∘ Sum.inj₁ $ x
  proj₂ equivalent (X509.kuextn x) = Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₁ $ x
  proj₂ equivalent (X509.ekuextn x) = Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₁ $ x
  proj₂ equivalent (X509.bcextn x) = Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₁ $ x
  proj₂ equivalent (X509.ianextn x) = Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₁ $ x
  proj₂ equivalent (X509.sanextn x) = Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₁ $ x
  proj₂ equivalent (X509.cpextn x) = Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₁ $ x
  proj₂ equivalent (X509.crlextn x) = Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₁ $ x
  proj₂ equivalent (X509.aiaextn x) = Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₁ $ x
  proj₂ equivalent (X509.other x) = Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ $ x

  iso : Iso
          (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.AKI      )            X509.AKIFields)
          (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.SKI      )            X509.SKIFields)
          (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.KU       )            X509.KUFields)
          (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.EKU      )            X509.EKUFields)
          (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.BC       )            X509.BCFields)
          (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.IAN      )            X509.IANFields)
          (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.SAN      )            X509.SANFields)
          (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.CPOL     )            X509.CertPolFields)
          (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.CRLDIST  )            X509.CRLDistFields)
          (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.AIA      )            X509.AIAFields)
               (X509.ExtensionFields (False ∘ (_∈? X509.ExtensionOID.Supported)) Generic.Octetstring)))))))))))
          X509.SelectExtn
  proj₁ iso = equivalent
  proj₁ (proj₂ iso) (Sum.inj₁ x) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₁ x)) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))                                                        = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))                                             = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))                                  = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))))                       = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))))            = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))))) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x)))))))))) = refl
  proj₂ (proj₂ iso) (X509.akiextn x) = refl
  proj₂ (proj₂ iso) (X509.skiextn x) = refl
  proj₂ (proj₂ iso) (X509.kuextn x)  = refl
  proj₂ (proj₂ iso) (X509.ekuextn x) = refl
  proj₂ (proj₂ iso) (X509.bcextn x)  = refl
  proj₂ (proj₂ iso) (X509.ianextn x) = refl
  proj₂ (proj₂ iso) (X509.sanextn x) = refl
  proj₂ (proj₂ iso) (X509.cpextn x)  = refl
  proj₂ (proj₂ iso) (X509.crlextn x) = refl
  proj₂ (proj₂ iso) (X509.aiaextn x) = refl
  proj₂ (proj₂ iso) (X509.other x)   = refl

  postulate
    @0 unambiguous : Unambiguous X509.SelectExtn


module ExtensionsSeq where
  import Aeres.Data.X509.Properties.Seq as SeqProps
  import Aeres.Data.X509.Properties.TLV as TLVProps

  @0 unambiguous : Unambiguous X509.ExtensionsSeq
  unambiguous =
    TLVProps.unambiguous
      (SeqProps.unambiguous
        (TLVProps.unambiguous SelectExtn.unambiguous) TLVProps.nonempty TLVProps.nonnesting)


