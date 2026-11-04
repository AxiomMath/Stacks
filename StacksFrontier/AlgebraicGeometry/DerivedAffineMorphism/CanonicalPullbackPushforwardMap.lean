module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafAsADerivedUnit
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaInvertibility

/-!
# The canonical morphism of [Stacks, Tag 08I9], with no hypothesis

Let `f : X ⟶ Y` be a morphism of ringed spaces. [Stacks, Tag 08I9] asserts, for `f` an affine
morphism of schemes and `E` in `D_QCoh(𝒪_Y)`, that

`E ⊗^𝐋_{𝒪_Y} f_*𝒪_X ⟶ Rf_*Lf^*E`

is invertible. `Stacks.Cohomology.DerivedProjectionFormula.pullbackPushforwardTensorMap` builds
that morphism — out of the derived projection-formula map of [Stacks, Tag 0B53] at the source
complex `𝒪_X[0]` — from the left unit law `𝒪_X ⊗^𝐋_{𝒪_X} W ≅ W` of the derived tensor product,
which it carries as the hypothesis `unitLeft`. That hypothesis is **not** a missing mathematical
input: it is `Stacks.RingedSpace.derivedTensorLeftUnitIso`, [Stacks, Tag 0FPT] for a ringed
space. This file supplies it, so that the morphism of [Stacks, Tag 08I9] and the criterion for
its invertibility are available with no hypothesis beyond the morphism `f` itself.

Nothing else about [Stacks, Tag 08I9] is proved here. In particular the morphism below is **not**
shown to be invertible for an affine morphism of schemes, and no `@[stacks 08I9]` attribute is
placed: by `isIso_pullbackPushforwardTensorMap` that invertibility is exactly invertibility of
the projection-formula map at the source complex `𝒪_X[0]` and an arbitrary target complex, which
is [Stacks, Tag 08EU] there, and of that only the case `K = 𝒪_Y[0]` is proved in this library —
as `Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitObject`, and that
still carrying the right-unitor coherence of the comparison of [Stacks, Tag 079U].

## Main definitions

* `Stacks.Cohomology.DerivedProjectionFormula.pullbackPushforwardTensorMap'` — the canonical
  morphism `Rf_*𝒪_X ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*Lf^*K` of [Stacks, Tag 08I9], for an arbitrary morphism
  of ringed spaces and an arbitrary `K` in `D(𝒪_Y)`, with no hypothesis.

## Main results

* `Stacks.Cohomology.DerivedProjectionFormula.isIso_pullbackPushforwardTensorMap` — that morphism
  is invertible exactly when the derived projection-formula map of [Stacks, Tag 0B53] at the
  source complex `𝒪_X[0]` is.

## Implementation notes

*The model of the derived categories is the standard one*, as it is in the two modules this one
reads from: `Stacks.RingedSpace.derivedTensorLeftUnitIso` is pinned there because
`Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso` is, and
`CategoryTheory.HasDerivedCategory` carries the localized category as data, so a statement at one
model does not transport to another.

*The two spellings of the sheaf of rings meet here.* `unitLeft` asks for the unit law at
`Stacks.Cohomology.DerivedProjectionFormula.singleUnit X`, whose category of modules is spelled
`Stacks.DerivedTensor.RingedSite.Modules X.sheaf`, while `derivedTensorLeftUnitIso` is stated over
`AlgebraicGeometry.structureSheafRing X`. The two are the same sheaf of rings — that is
`StacksDraft.KFlat.ringSheaf_eq`, recorded in the documentation of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/StructureSheafAsADerivedUnit.lean` — and the crossing
is made by elaboration here, with no cast.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08I9](https://stacks.math.columbia.edu/tag/08I9)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite

universe u

namespace Stacks.Cohomology.DerivedProjectionFormula

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The canonical morphism `Rf_*𝒪_X ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*Lf^*K`** of [Stacks, Tag 08I9], for an
arbitrary morphism of ringed spaces `f : X ⟶ Y` and an arbitrary `K` in `D(𝒪_Y)`, with no
hypothesis.

This is `pullbackPushforwardTensorMap` with its hypothesis `unitLeft` — the left unit law of the
derived tensor product on `X` — supplied by `Stacks.RingedSpace.derivedTensorLeftUnitIso`, which
is [Stacks, Tag 0FPT] read at the ringed site of the space. -/
def pullbackPushforwardTensorMap'
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    ((derivedTensorProductFunctor Y.sheaf).obj
        ((derivedPushforward f).obj (singleUnit X))).obj K ⟶
      (derivedPushforward f).obj ((derivedPullback f).obj K) :=
  pullbackPushforwardTensorMap f (Stacks.RingedSpace.derivedTensorLeftUnitIso X) K

/-- **What invertibility of the morphism of [Stacks, Tag 08I9] amounts to**: the canonical
morphism `Rf_*𝒪_X ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*Lf^*K` is invertible exactly when the derived
projection-formula morphism of [Stacks, Tag 0B53] at the source complex `𝒪_X[0]` is, the second
leg of the composite being the direct image of an isomorphism.

So what [Stacks, Tag 08I9] needs, for `f` an affine morphism of schemes and `K` in
`D_QCoh(𝒪_Y)`, is [Stacks, Tag 08EU] at `E = 𝒪_X[0]` and that `K`; no hypothesis beyond `f`
intervenes in the reduction. -/
theorem isIso_pullbackPushforwardTensorMap
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    IsIso (pullbackPushforwardTensorMap' f K) ↔
      IsIso (projectionFormulaMap f (singleUnit X) K) :=
  isIso_pullbackPushforwardTensorMap_iff f (Stacks.RingedSpace.derivedTensorLeftUnitIso X) K

end Stacks.Cohomology.DerivedProjectionFormula

end
