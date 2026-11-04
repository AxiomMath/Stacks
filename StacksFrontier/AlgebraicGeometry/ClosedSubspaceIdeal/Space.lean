module

public import StacksFrontier.AlgebraicGeometry.ClosedSubspaceIdeal.EssImage
public import StacksFrontier.AlgebraicGeometry.ClosedSubspaceIdeal.Support
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The closed subspace carried by the support of `𝒪_X / J`

Continuing from `StacksFrontier.AlgebraicGeometry.ClosedSubspaceIdeal.Support`, the sheaf
`𝒪_X / J` has terminal stalks off the closed set `quotientSupport X J j`, so it is pushed
forward from that closed set. Transporting the structure sheaf back along the inclusion turns
the support into a locally ringed space, and the quotient map `𝒪_X ⟶ 𝒪_X / J` into a morphism
of locally ringed spaces from it to `X`.

## Main definitions

* `Stacks.ClosedSubspaceIdeal.QuotientSupportSpaceData` packages a locally ringed space on the
  support together with the identification of its pushed-forward structure sheaf with
  `𝒪_X / J`.
* `Stacks.ClosedSubspaceIdeal.quotientSupportSpaceData` constructs such data.
* `Stacks.ClosedSubspaceIdeal.quotientSupportSpaceLocallyRingedMap` is the resulting morphism of
  locally ringed spaces into `X`.

## Implementation notes

These names were a second, content-identical copy of the canonical declarations in
`StacksFrontier.AlgebraicGeometry.ClosedImmersion.ClosedSubspaceExistence`, over a separate copy of
the structure `QuotientSupportSpaceData`, so the two developments were not interchangeable. The
structure is now re-exported from `Stacks.ClosedImmersion` and the definitions are aliases of
the canonical ones, so each spelling denotes the canonical construction.

## References

* [Stacks Project, Tag 01HN](https://stacks.math.columbia.edu/tag/01HN)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.ClosedSubspaceIdeal

variable (X : LocallyRingedSpace.{u})

export Stacks.ClosedImmersion (QuotientSupportSpaceData)

alias quotientSupportSpaceData := Stacks.ClosedImmersion.quotientSupportSpaceData

alias quotientRingSheafMapPresheaf := Stacks.ClosedImmersion.quotientRingSheafMapPresheaf

alias quotientSupportSpaceIsoInvPresheaf :=
  Stacks.ClosedImmersion.quotientSupportSpaceIsoInvPresheaf

alias quotientSupportSpaceSheafedMap := Stacks.ClosedImmersion.quotientSupportSpaceSheafedMap

@[ega "IV 16.1.3" "16.1.3(ii)"]
alias quotientSupportSpaceLocallyRingedMap :=
  Stacks.ClosedImmersion.quotientSupportSpaceLocallyRingedMap

end Stacks.ClosedSubspaceIdeal
