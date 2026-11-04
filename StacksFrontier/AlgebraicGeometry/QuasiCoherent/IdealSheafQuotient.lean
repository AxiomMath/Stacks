module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Topology.Sheaves.Abelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationCokernel
public import StacksFrontier.AlgebraicGeometry.FinitePresentationWitness.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteTypeIdealSheafDirected.Dictionary

/-!
# The quotient of the structure sheaf by a sheaf of ideals of finite type

Let `X` be a scheme and `I : X.IdealSheafData` a quasi-coherent sheaf of ideals whose ideal of
sections over every affine open is finitely generated, that is, with
`AlgebraicGeometry.Scheme.IdealSheafData.IsFiniteType`. This file produces the `𝒪_X`-module
`𝒪_X / I` and shows it is of finite presentation.

The two inputs are already available and need only be joined. The submodule of the structure
sheaf determined by `I` is of finite type without any Noetherian hypothesis on `X`
(`Stacks.FiniteTypeIdealSheaf.isFiniteType_unitSubmodule`), the structure sheaf is of finite
presentation (`Stacks.AlgebraicGeometry.FinitePresentationWitness.isFinitePresentation_unit`),
and [Stacks, Tag 0H96] says the cokernel of a map from a finite type module to a finitely
presented one is finitely presented.

This is the finite presentation assertion of step 2 of the proof of [Stacks, Tag 0GPJ], which
asks for a sheaf of ideals of finite type cutting out the complement of an affine open together
with the finite presentation of the corresponding quotient of the structure sheaf. Nothing about
the vanishing locus of `I` is proved in this file; that half of step 2, the remaining content of
[Stacks, Tag 01PH], is
`Stacks.AlgebraicGeometry.IdealSheafQuotient.supp_structureQuotient` in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/StructureQuotientSupport.lean`.

## Main definitions

* `Stacks.AlgebraicGeometry.IdealSheafQuotient.structureQuotient`: the module `𝒪_X / I`, as the
  cokernel of the inclusion of `I` into the structure sheaf.

## Main results

* `Stacks.AlgebraicGeometry.IdealSheafQuotient.isFinitePresentation_structureQuotient`:
  **`𝒪_X / I` is of finite presentation when `I` is of finite type.** No Noetherian hypothesis.

## Implementation notes

The inclusion of `I` into the structure sheaf is `SheafOfModules.Submodule.ι` applied to
`AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule`, so the cokernel is taken in
`SheafOfModules.{u} X.ringCatSheaf` and not in `AlgebraicGeometry.Scheme.Modules X`. The two
are definitionally equal but carry different `CategoryTheory.Category` instances —
`X.Modules` installs its own `AlgebraicGeometry.Scheme.Modules.Hom` — so every statement below
is phrased at the `SheafOfModules` spelling, which is the one
`Stacks.SheafOfModules.isFinitePresentation_cokernel` is stated at and the one the morphism
`SheafOfModules.Submodule.ι` already lives in. Mixing the two produces two cokernel terms that
`rw` cannot identify.

Finite type of `I.unitSubmodule` is a theorem taking the finite type of `I` as an explicit
argument, not an instance, because `AlgebraicGeometry.Scheme.IdealSheafData.IsFiniteType` is a
plain predicate rather than a class; it is promoted to an instance locally so that the
`[G.IsFiniteType]` argument of [Stacks, Tag 0H96] is discharged by synthesis.

## References

* [Stacks Project, Lemma 0H96](https://stacks.math.columbia.edu/tag/0H96)
* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
* [Stacks Project, Lemma 28.25.1 (Tag 01PH)](https://stacks.math.columbia.edu/tag/01PH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.IdealSheafQuotient

variable {X : Scheme.{u}}

/-- **The quotient `𝒪_X / I` of the structure sheaf by a quasi-coherent sheaf of ideals**, as
the cokernel of the inclusion
`AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule I ⟶ 𝒪_X` of sheaves of modules.

This is the module `𝒪_X / I` that step 2 of [Stacks, Tag 0GPJ] needs to be of finite
presentation. It is stated as an object of `SheafOfModules.{u} X.ringCatSheaf` rather than of
`AlgebraicGeometry.Scheme.Modules X`, which is where the inclusion morphism lives. -/
abbrev structureQuotient (I : X.IdealSheafData) : SheafOfModules.{u} X.ringCatSheaf :=
  cokernel I.unitSubmodule.ι

/-- **`𝒪_X / I` is of finite presentation as soon as `I` is of finite type**, with no
Noetherian hypothesis on `X`.

The submodule of the structure sheaf cut out by `I` is of finite type by
`Stacks.FiniteTypeIdealSheaf.isFiniteType_unitSubmodule`, the structure sheaf itself is of
finite presentation, and [Stacks, Tag 0H96] concludes for the cokernel. -/
theorem isFinitePresentation_structureQuotient (I : X.IdealSheafData) (hI : I.IsFiniteType) :
    (structureQuotient I).IsFinitePresentation :=
  have : I.unitSubmodule.toSheafOfModules.IsFiniteType :=
    Stacks.FiniteTypeIdealSheaf.isFiniteType_unitSubmodule I hI
  Stacks.SheafOfModules.isFinitePresentation_cokernel I.unitSubmodule.ι

end Stacks.AlgebraicGeometry.IdealSheafQuotient

end
