module

public import StacksFrontier.Deformation.RingedSpaceThickening.PulledNaiveCotangentTwoTerm
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackTwoStep

/-!
# Pulling back the cokernel of the conormal map

For morphisms of ringed spaces `g : (Y, 𝒪_Y) ⟶ (X, 𝒪_X)` and `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)`, the
differential of the two-term structure
`AlgebraicGeometry.RingedSpaceThickening.pulledNaiveCotangentTwoTerm` of `g^*𝖭𝖫_{X/S}` is
`AlgebraicGeometry.RingedSpaceThickening.pulledConormalMap`, the image under `g^*` of the
conormal map of the canonical presentation of `𝒪_X` over `f⁻¹𝒪_S`. Clause (2) of
[Stacks Project, Tag 08U8] reads its acting group out of the cokernel of that differential,
which is `H⁰(g^*𝖭𝖫_{X/S})`.

This file proves that `g^*` carries the cokernel of the conormal map to that cokernel: `g^*` is
a left adjoint, so it preserves cokernels. Combined with **Stacks 08TY** in degree `0` —
`H⁰(𝖭𝖫_{X/S}) = Ω_{X/S}`, which the library has — this is what identifies
`H⁰(g^*𝖭𝖫_{X/S})` with `g^*Ω_{X/S}`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.twoStepPullbackCokernelConormalIso`: **`g^*` carries
  the cokernel of the conormal map to the cokernel of `pulledConormalMap`.**

## Implementation notes

`g^*` enters here in the two-step spelling
`AlgebraicGeometry.RingedSpaceModuleAdjunction.twoStepPullback`, the composite of
`inverseImageModulePullback` with `inverseImageExtendScalars`, because that is the spelling
`pulledConormalMap` is built from — the two agree definitionally — and because
`AlgebraicGeometry.RingedSpaceModuleAdjunction.twoStepPullbackAdjunction` exhibits it as a left
adjoint, which is what makes `CategoryTheory.Limits.PreservesCokernel.iso` apply.
`AlgebraicGeometry.RingedSpaceModuleAdjunction.modulePullbackIsoTwoStep` moves a statement about
it onto the one-step `modulePullback`, which is the spelling carrying the adjunction `g^* ⊣ g_*`
and the one the acting group of [Stacks Project, Tag 0CK2] is written with.

This file writes `conormalMap` with `Stacks.SheafOfModules.inverseImageBaseRingOnMiddle` and
`ringedSpaceStructureMap`, while **Stacks 08TY** is stated for `𝖭𝖫_{X/S}` built from
`Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf` and `inverseImageStructureMap`. The
two inverse images are the same `abbrev` body and the two structure maps are equal by `rfl`
(`Stacks.NaiveCotangentSixTermFirstTerms.ringedSpaceStructureMap_eq`), so the two cokernels are
the same term and an isomorphism stated at either spelling applies at the other by type
ascription, with no rewrite inside a dependent type.

For schemes and Mathlib's model of the pullback, the same fact is
`Stacks.NaiveCotangentSixTermSequence.modulePullbackNaiveCotangentComplexHomologyZeroIso`, which
is `H⁰(f^*𝖭𝖫_{Y/Z}) ≅ f^*Ω_{Y/Z}` with `Scheme.Modules.pullback` and
`Scheme.Hom.relativeDifferentials`. The acting group of Tag 0CK2 is read out of
`Stacks.Smooth.pullbackCotangentSheaf`, whose cotangent sheaf is
`Stacks.Sheaves.RingedSpaceDifferentials.moduleOfDifferentials` and not Mathlib's
`relativeDifferentials`.

## References

* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM), the inverse image of the
  naive cotangent complex.
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), `H⁰(𝖭𝖫_{X/S}) = Ω_{X/S}`.
* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8), whose clause (2) reads
  its acting group out of `H⁰`.
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096), the pullback of sheaves
  of modules and its adjunction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction (twoStepPullback twoStepPullbackAdjunction)
open Stacks.SheafOfModules (canonicalConormalSequence inverseImageBaseRingOnMiddle
  ringedSpaceStructureMap)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S Y : RingedSpace.{u, u}} (g : Y ⟶ X) (f : X ⟶ S)

/-- The conormal map of the canonical presentation of `𝒪_X` over `f⁻¹𝒪_S`: the differential of
`𝖭𝖫_{X/S}`, of which `AlgebraicGeometry.RingedSpaceThickening.pulledConormalMap` is the image
under `g^*`. -/
abbrev conormalMap :=
  (canonicalConormalSequence.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
    (inverseImageBaseRingOnMiddle f) X.sheaf (ringedSpaceStructureMap f)).f

/-- **`g^*` carries the cokernel of the conormal map to the cokernel of `pulledConormalMap`.**
The pullback of sheaves of modules is a left adjoint, by
`AlgebraicGeometry.RingedSpaceModuleAdjunction.twoStepPullbackAdjunction`, hence preserves
cokernels; and `pulledConormalMap g f` is the image of the conormal map under its two-step
model.

Since the cokernel of the conormal map is `Ω_{X/S}` by **Stacks 08TY** in degree `0`, this says
`H⁰(g^*𝖭𝖫_{X/S}) = g^*Ω_{X/S}` — the identification of the acting group of clause (2) of
[Stacks Project, Tag 08U8] with the one the source writes, `Hom(g^*Ω_{X/S}, 𝒢)`. -/
def twoStepPullbackCokernelConormalIso :
    (twoStepPullback g).obj (cokernel (conormalMap f)) ≅ cokernel (pulledConormalMap g f) :=
  haveI := (twoStepPullbackAdjunction g).leftAdjoint_preservesColimits
  PreservesCokernel.iso (twoStepPullback g) (conormalMap f)

end AlgebraicGeometry.RingedSpaceThickening

end
