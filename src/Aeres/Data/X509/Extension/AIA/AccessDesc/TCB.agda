open import Aeres.Binary
import      Aeres.Data.X509.Extension.AIA.AccessDesc.TCB.OIDs as OIDs
open import Aeres.Data.X509.GeneralNames.GeneralName.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel.TCB
open import Aeres.Prelude

module Aeres.Data.X509.Extension.AIA.AccessDesc.TCB where

open Aeres.Grammar.Definitions  UInt8
open Aeres.Grammar.Parallel.TCB UInt8

supportedAccessMethod : List (Exists─ _ OIDValue)
supportedAccessMethod = (-, OIDs.OSCP) ∷ [ -, OIDs.CAIssuers ]

AccessDescParam : {@0 bs : List UInt8} → OID bs → @0 List UInt8 → Set
AccessDescParam o =
     GeneralName
  ×ₚ (λ _ → (True ((-, TLV.val o) ∈? supportedAccessMethod)))

AccessDesc : @0 List UInt8 → Set
AccessDesc = DefinedByOID AccessDescParam

RawAccessDescParam : Raw₁ RawOID AccessDescParam
Raw₁.D RawAccessDescParam _ = Raw.D RawGeneralName
Raw₁.to RawAccessDescParam _ x = Raw.to RawGeneralName (fstₚ x)

RawAccessDesc : Raw AccessDesc
RawAccessDesc = RawDefinedByOID RawAccessDescParam
