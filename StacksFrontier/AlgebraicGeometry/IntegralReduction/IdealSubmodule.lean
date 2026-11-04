module

public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.Coherence
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.IdealSheafDataSubmodule

/-!
# An `IdealSheafData` as a submodule of the structure sheaf

An `AlgebraicGeometry.Scheme.IdealSheafData` is a compatible family of ideals indexed by the
affine opens; the annihilator machinery of [Stacks, Tag 01PO], and with it the first paragraph of
the proof of [Stacks, Tag 01YE], is stated instead over a
`(SheafOfModules.unit X.ringCatSheaf).Submodule`. This file is the passage between the two, and
it is a one-line construction: `Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmul` applied to
the structure sheaf itself with exponent `1`.

## Main definitions

* `I.unitSubmodule`: the ideal sheaf of `I : X.IdealSheafData`, as a submodule of `𝒪_X`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule_obj_affine`: its sections over an
  affine open are `I.ideal U`.
* `AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule_isQuasicoherent`,
  `isCoherent_unitSubmodule`, `isFiniteType_unitSubmodule`: the three finiteness properties the
  annihilator results of
  [Stacks, Tag 01PO] require of their ideal, the last two on a Noetherian scheme.

## Implementation notes

**Nothing here is a new construction.**
`Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmul I n F`
builds the subsheaf `I ^ n • F` of a quasi-coherent `F` from the affine family
`U ↦ I(U) ^ n • Γ(F, U)`, and `F = 𝒪_X`, `n = 1` is the ideal sheaf itself. There is no *named*
declaration for this bridge, and the two existing nearby objects
are not substitutes: `Stacks.AmpleCohomologicalCriterion.idealSubobject` lands in `Subobject`
rather than `SheafOfModules.Submodule`, and `AlgebraicGeometry.Blowup.ReesAlgebra`'s
`idealPowerKernel` is
`private`. No mathematics is needed, only the instantiation, which is why this file is short.

The sections are given only in the `I(U) • ⊤` form that
`Stacks.AlgebraicGeometry.IdealPowerSmul.obj_idealPowSmul` delivers, and **not** identified with
`I.ideal U` itself. That identification is a real step and is deliberately not taken here: the
module `Γ(𝒪_X, U)` does not carry its ring structure at this spelling — `(1 : Γ(𝒪_X, U))`
fails to elaborate for want of an `OfNat` instance, as does `(0 : X.Modules)`
— so `I(U) • ⊤ = I(U)` cannot be proved by `Ideal.mul_top` without first
transporting the module structure. `attribute [local instance_reducible]
AlgebraicGeometry.Scheme.Modules` is needed even to *state* the sections, and it supplies the
`Module` instance but not the `One`.

Coherence and finite type are read off the *structure sheaf's* coherence
([Stacks, Tag 01XZ]) through [Stacks, Tag 01Y1]: an ideal sheaf is a quasi-coherent submodule of
a coherent module, so on a Noetherian scheme it is coherent, hence of finite type. No statement
concluding either property for an ideal sheaf existed in Mathlib or in this tree.

## References

* [Stacks Project, Tag 01PO](https://stacks.math.columbia.edu/tag/01PO)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Tag01YEIntegralReduction

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **An ideal sheaf on a Noetherian scheme is coherent**: it is a quasi-coherent submodule of
the structure sheaf, which is coherent by [Stacks, Tag 01XZ]. -/
theorem isCoherent_unitSubmodule [IsNoetherian X] (I : X.IdealSheafData) :
    I.unitSubmodule.toSheafOfModules.IsCoherent :=
  IdealPowerSmul.isCoherent_of_isQuasicoherent_submodule (SheafOfModules.unit X.ringCatSheaf)
    I.unitSubmodule (AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule_isQuasicoherent I)

/-- **An ideal sheaf on a Noetherian scheme is of finite type**, which is the hypothesis the
quasi-coherence and stalk assertions of [Stacks, Tag 01PO] place on their ideal. -/
theorem isFiniteType_unitSubmodule [IsNoetherian X] (I : X.IdealSheafData) :
    I.unitSubmodule.toSheafOfModules.IsFiniteType :=
  have := isCoherent_unitSubmodule I
  _root_.SheafOfModules.IsCoherent.isFiniteType

end Stacks.AlgebraicGeometry.Tag01YEIntegralReduction

end
