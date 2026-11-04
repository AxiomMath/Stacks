module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentExtZero
public import StacksFrontier.Deformation.RingedSpaceThickening.PulledNaiveCotangentCokernel
public import StacksFrontier.Topology.Sheaves.Modules.Differentials.SectionwiseComparison

/-!
# The cokernel of the pulled-back conormal map is the pulled-back cotangent sheaf

For morphisms of ringed spaces `g : (Y, 𝒪_Y) ⟶ (X, 𝒪_X)` and `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)`, clause
(2) of [Stacks Project, Tag 08U8] reads its acting group out of the cokernel of
`AlgebraicGeometry.RingedSpaceThickening.pulledConormalMap`, the differential of
`g^*𝖭𝖫_{X/S}`, and the source writes that group as `Hom(g^*Ω_{X/S}, 𝒢)`. This file identifies
the two sheaves:

`Coker(g^*(𝒥/𝒥² ⟶ Ω)) ≅ g^*Ω_{X/S}`.

`AlgebraicGeometry.RingedSpaceThickening.twoStepPullbackCokernelConormalIso` carries the cokernel
across `g^*`, and **Stacks 08TY** in degree `0` identifies the cokernel before pulling back with
`Ω_{X/S}`; this file composes them and then moves the right-hand side onto the spelling of
`Ω_{X/S}` that the cotangent sheaf of a morphism of schemes is built from.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.cokernelConormalMapIsoDifferentials`: **Stacks 08TY in
  degree `0`** for the cokernel of `AlgebraicGeometry.RingedSpaceThickening.conormalMap`.
* `AlgebraicGeometry.RingedSpaceThickening.pulledCokernelConormalIsoDifferentials`:
  **`Coker(pulledConormalMap) ≅ g^*Ω_{X/S}`**, with `g^*` in the two-step spelling and
  `Ω_{X/S}` corepresenting relative derivations.
* `AlgebraicGeometry.RingedSpaceThickening.pulledCokernelConormalIsoPullbackCotangent`: the same
  isomorphism with `g^*` in the one-step spelling and `Ω_{X/S}` the sheafified sectionwise
  differentials — the shape `Deformation.Examples.schemeMorphismPullbackCotangent` and
  `Stacks.Smooth.pullbackCotangentSheaf` are written in.

## Implementation notes

**The three spellings of the structure map, and why no rewrite is needed.** `pulledConormalMap`
and `conormalMap` are written with `Stacks.SheafOfModules.ringedSpaceStructureMap` and
`Stacks.SheafOfModules.inverseImageBaseRingOnMiddle`, whereas
`AlgebraicGeometry.RingedSpace.naiveCotangentComplex` and everything derived from it is written
with `Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap` and `inverseImageSheaf`.
The two inverse images are the same `abbrev` body and the two structure maps are equal by `rfl`
(`Stacks.NaiveCotangentSixTermFirstTerms.ringedSpaceStructureMap_eq`), so the two conormal
sequences — `conormalMap f` here and
`AlgebraicGeometry.RingedSpace.naiveCotangentConormalShortComplex f` there — are the same term up
to unfolding, and so are their cokernels.

Nothing therefore has to be rewritten inside a dependent type. The existing
`AlgebraicGeometry.RingedSpace.naiveCotangentCokernelIsoDifferentials`, which is stated at the
`inverseImageStructureMap` spelling, is accepted at the `ringedSpaceStructureMap` spelling by
type ascription alone. What does *not* work is reassembling the isomorphism from the site-level
`Stacks.SheafOfModules.naiveCotangentComplexHomologyZeroIsoCokernel` and
`naiveCotangentComplexHomologyZeroIso` instantiated at `ringedSpaceStructureMap f`: that asks the
elaborator to join the `TopCat.Sheaf` and `CategoryTheory.Sheaf` spellings of the category of
sheaves of modules at a concrete structure sheaf, which is the cost the module docstring of
`StacksFrontier/Topology/Sheaves/Modules/DifferentialsOfSiteBridge.lean` describes, and it exhausts
the heartbeat budget. The cokernel-level statement in the library is what makes the composition
cheap: it is an isomorphism between two objects already on the ringed-space side.

**The two spellings of `Ω_{X/S}`.** `AlgebraicGeometry.SheafOfModules.moduleOfDifferentials` is
the object corepresenting relative derivations and
`Stacks.Sheaves.RingedSpaceDifferentials.moduleOfDifferentials` is the sheafification of the
presheaf of sectionwise Kähler differentials; `Stacks.Smooth.cotangentSheaf` and hence the acting
group of [Stacks Project, Tag 0CK2] use the second.
`AlgebraicGeometry.SheafOfModules.relativeDifferentialsIsoSectionwise` identifies them, and
`AlgebraicGeometry.RingedSpaceModuleAdjunction.modulePullbackIsoTwoStep` moves `g^*` from the
two-step model `twoStepPullback`, which `pulledConormalMap` is built from and which
`twoStepPullbackCokernelConormalIso` exhibits as a left adjoint, onto the one-step
`modulePullback` carrying the adjunction `g^* ⊣ g_*`.

## References

* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), `H⁰(𝖭𝖫_{X/S}) = Ω_{X/S}`.
* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM), the inverse image of the
  naive cotangent complex.
* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8), whose clause (2) reads
  its acting group out of `H⁰`.
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096), the pullback of sheaves
  of modules and its adjunction.
* [Stacks Project, Tag 08RU](https://stacks.math.columbia.edu/tag/08RU), the two descriptions of
  the sheaf of relative differentials.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction (modulePullback modulePullbackIsoTwoStep twoStepPullback)
open Stacks.SheafOfModules (ringedSpaceStructureMap)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S Y : RingedSpace.{u, u}} (g : Y ⟶ X) (f : X ⟶ S)

/-- **Stacks 08TY in degree `0`, for the cokernel of
`AlgebraicGeometry.RingedSpaceThickening.conormalMap`.** The cokernel of the conormal map of the
canonical presentation of `𝒪_X` over `f⁻¹𝒪_S` is the sheaf of relative differentials `Ω_{X/S}`.

This is `AlgebraicGeometry.RingedSpace.naiveCotangentCokernelIsoDifferentials` read at the
spelling of the structure map that `conormalMap` is written with. The two spellings are the same
term, so no transport is involved; see the implementation notes of this file. -/
def cokernelConormalMapIsoDifferentials :
    cokernel (conormalMap f) ≅
      AlgebraicGeometry.SheafOfModules.moduleOfDifferentials.{u, u, u}
        (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f) :=
  AlgebraicGeometry.RingedSpace.naiveCotangentCokernelIsoDifferentials f

/-- **`Coker(g^*(𝒥/𝒥² ⟶ Ω)) ≅ g^*Ω_{X/S}`.** The cokernel of the differential of `g^*𝖭𝖫_{X/S}`
is the pullback along `g` of the sheaf of relative differentials of `f`: the differential is the
image under `g^*` of the conormal map, `g^*` preserves cokernels, and the cokernel of the
conormal map is `Ω_{X/S}`.

This is the identification of the acting group of clause (2) of [Stacks Project, Tag 08U8] —
`Hom(H⁰(g^*𝖭𝖫_{X/S}), 𝒢)` — with the group the source writes, `Hom(g^*Ω_{X/S}, 𝒢)`. Here `g^*`
is the two-step composite `twoStepPullback` that `pulledConormalMap` is built from;
`AlgebraicGeometry.RingedSpaceThickening.pulledCokernelConormalIsoPullbackCotangent` moves it
onto the one-step spelling. -/
def pulledCokernelConormalIsoDifferentials :
    cokernel (pulledConormalMap g f) ≅
      (twoStepPullback g).obj
        (AlgebraicGeometry.SheafOfModules.moduleOfDifferentials.{u, u, u}
          (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f)) :=
  (twoStepPullbackCokernelConormalIso g f).symm ≪≫
    (twoStepPullback g).mapIso (cokernelConormalMapIsoDifferentials f)

/-- **`Coker(g^*(𝒥/𝒥² ⟶ Ω)) ≅ g^*Ω_{X/S}`, at the cotangent sheaf of a morphism of schemes.**
The same isomorphism as
`AlgebraicGeometry.RingedSpaceThickening.pulledCokernelConormalIsoDifferentials`, with `g^*` the
one-step `AlgebraicGeometry.RingedSpaceModuleAdjunction.modulePullback` carrying the adjunction
`g^* ⊣ g_*` and with `Ω_{X/S}` the sheafified sectionwise differentials.

That is the shape `Deformation.Examples.schemeMorphismPullbackCotangent` and
`Stacks.Smooth.pullbackCotangentSheaf` — the sheaf the acting group of
[Stacks Project, Tag 0CK2] is read out of — are written in. -/
def pulledCokernelConormalIsoPullbackCotangent :
    cokernel (pulledConormalMap g f) ≅
      (modulePullback g).obj
        (Stacks.Sheaves.RingedSpaceDifferentials.moduleOfDifferentials f) :=
  pulledCokernelConormalIsoDifferentials g f ≪≫
    ((modulePullbackIsoTwoStep g).app _).symm ≪≫
      (modulePullback g).mapIso
        (AlgebraicGeometry.SheafOfModules.relativeDifferentialsIsoSectionwise f)

end AlgebraicGeometry.RingedSpaceThickening

end
