module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardTensorMap
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.KunnethSchemeTorIndependent
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.ShiftedStructureSheafTensor
public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceCoherator
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardAnyModel
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQCoh
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaUnitShifts
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProductCommutativity
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived pullback of a shifted structure sheaf as a tensor factor

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, let `L` be an object of `D(𝒪_X)`
and let `n` be an integer. Then

`Lf^*(𝒪_Y[n]) ⊗^𝐋_{𝒪_X} L ≅ L⟦-n⟧`,

with no hypothesis at all: the derived pullback carries the structure sheaf in degree `n` to the
structure sheaf in degree `n` (`Stacks.RingedSpace.derivedPullbackShiftedUnitIso`,
[Stacks, Tag 01CD] in a shifted degree), the structure sheaf in degree `n` is the shift by `-n`
of the structure sheaf in degree `0` (`Stacks.RingedSpace.shiftedUnitShiftIso`), and tensoring by
a shift of the unit object is that shift
(`CategoryTheory.Functor.flipObjShiftIsoOfUnitor`, fed the right unit constraint of
[Stacks, Tag 0FPT] and the compatibility of the derived tensor product of [Stacks, Tag 06YU]
with the shifts in both variables).

This is what the proof of [Stacks, Tag 0B6I] in
`StacksFrontier/AlgebraicGeometry/Duality/SheafyTraceGlobalHom.lean` needs in place of
[Stacks, Tag 08DX] part (1). That tag — `D_QCoh` is closed under the derived tensor product — is
proved only at the locally small model of the derived categories, in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedTilde/QuasiCoherentDerivedTensor.lean`, because
its proof goes through the affine equivalence of [Stacks, Tag 06Z0]; the sheafy trace map is at
`CategoryTheory.HasDerivedCategory.standard`. It is not needed: [Stacks, Tag 0A9Q] is applied in
the proof of [Stacks, Tag 0B6I] at the single object `M = 𝒪_Y[n]`, and there the identification
above puts `Lf^*M ⊗^𝐋 L` in `D_QCoh(𝒪_X)` as soon as `L` is, because `D_QCoh` is stable under
shifts — the quasi-coherent modules on a scheme being a weak Serre subcategory
(`Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre`,
`CategoryTheory.DerivedCategoryB.derivedCategoryB_shift_mem`).

The same file supplies the third hypothesis the sheafy trace development carries, `hpush`: that
`Rf_*` preserves quasi-coherence of the cohomology sheaves, which is part (1) of
[Stacks, Tag 08D5] and is what lets `Rf_*` be restricted to `D_QCoh` at all. It too holds for a
quasi-compact quasi-separated morphism with quasi-compact target, and at the standard model, by
`AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_qcqs`.

## Main definitions

* `Stacks.RingedSpace.pullbackShiftedUnitTensorIso` — the isomorphism
  `Lf^*(𝒪_Y[n]) ⊗^𝐋_{𝒪_X} L ≅ L⟦-n⟧`.

## Main results

* `Stacks.Duality.isQuasicoherent_homology_derivedPushforward_qcqs` — part (1) of
  [Stacks, Tag 08D5] at `CategoryTheory.HasDerivedCategory.standard`, in the shape of the
  hypothesis `hpush` of `Stacks.Duality.quasiCoherentDerivedPushforward`.

## Implementation notes

*The model.* As in the files whose results are used, everything is at
`CategoryTheory.HasDerivedCategory.standard`, installed with a raised priority because the
import closure also contains the locally small instances.

*The symmetry.* `CategoryTheory.Functor.flipObjShiftIsoOfUnitor` identifies tensoring on the
*right* by a shift of the unit with that shift, the right unit constraint being the datum it
consumes; the pullback sits in the *left* factor here, so the commutativity constraint of
[Stacks, Tag 0FPB] — `Stacks.Cohomology.DerivedRelativeCupProduct.derivedBraiding`, invertible
by `Stacks.Cohomology.DerivedKunneth.isIso_derivedBraiding` — is applied first.

## References

* [Stacks Project, Tag 0B6I](https://stacks.math.columbia.edu/tag/0B6I)
* [Stacks Project, Tag 0A9Q](https://stacks.math.columbia.edu/tag/0A9Q)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedAdjunction)
open Stacks.Cohomology.DerivedProjectionFormula (singleUnit derivedTensorCommShift₂)
open Stacks.Cohomology.DerivedRelativeCupProduct (derivedBraiding)
open Stacks.Cohomology.DerivedKunneth (isIso_derivedBraiding)
open Stacks.DerivedTensor.RingedSite

universe u

-- Standard model only: `Stacks.RingedSpace.derivedPullbackShiftedUnitIso`,
--   `Stacks.RingedSpace.shiftedUnitShiftIso`.
attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.RingedSpace

attribute [local implicit_reducible] structureSheafRing

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **`Lf^*(𝒪_Y[n]) ⊗^𝐋_{𝒪_X} L ≅ L⟦-n⟧`**, for an arbitrary morphism of ringed spaces and an
arbitrary `L` in `D(𝒪_X)`.

The commutativity constraint of [Stacks, Tag 0FPB] moves the pullback into the second tensor
factor, `Stacks.RingedSpace.derivedPullbackShiftedUnitIso` identifies `Lf^*(𝒪_Y[n])` with
`𝒪_X[n]` and `Stacks.RingedSpace.shiftedUnitShiftIso` identifies that with `𝒪_X[0]⟦-n⟧`, and
tensoring on the right by a shift of the unit object is that shift, which is
`CategoryTheory.Functor.flipObjShiftIsoOfUnitor` fed the right unit constraint of
[Stacks, Tag 0FPT] and the compatibility of the derived tensor product with the shifts in both
variables. -/
def pullbackShiftedUnitTensorIso
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (n : ℤ) :
    ((derivedTensorProductFunctor X.sheaf).obj
        ((derivedPullback f).obj (shiftedUnitObject Y n))).obj L ≅
      (shiftFunctor (DerivedCategory
        (SheafOfModules.{u} (structureSheafRing X))) (-n)).obj L :=
  haveI := derivedTensorCommShift₂ X
  haveI : IsIso (derivedBraiding X ((derivedPullback f).obj (shiftedUnitObject Y n)) L) :=
    isIso_derivedBraiding X _ _
  asIso (derivedBraiding X ((derivedPullback f).obj (shiftedUnitObject Y n)) L) ≪≫
    ((derivedTensorProductFunctor X.sheaf).obj L).mapIso
        (derivedPullbackShiftedUnitIso f n ≪≫ (shiftedUnitShiftIso X n).symm) ≪≫
      (Functor.flipObjShiftIsoOfUnitor (derivedTensorProductFunctor X.sheaf)
        (singleUnit X) (derivedTensorRightUnitorNatIso X) (-n)).app L

end Stacks.RingedSpace

/-! ### [Stacks, Tag 08D5] part (1) at the standard model -/

namespace Stacks.Duality

/-- **Part (1) of [Stacks, Tag 08D5] at `CategoryTheory.HasDerivedCategory.standard`**, in the
shape of the hypothesis `hpush` of `Stacks.Duality.quasiCoherentDerivedPushforward`: along a
quasi-compact quasi-separated morphism of schemes with quasi-compact target, derived direct image
preserves quasi-coherence of the cohomology sheaves.

This is `AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_qcqs`,
which carries the model of the two derived categories as a binder and is therefore available
here. `Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs` is the same result at
the locally small model, which is the one the `Stacks.Duality` namespace works at elsewhere; the
sheafy trace map of [Stacks, Tag 0B6H] is at the standard model and needs this reading. The
conclusion is written as a single `∀`-statement because that is the shape the hypothesis `hpush`
has.

No `@[stacks 08D5]` attribute is placed, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/QcqsPushforwardAnyModel.lean`: part (3) of
the tag — that the integer `N` of part (2) survives an arbitrary base change — is not available,
so the covering set of the tag is incomplete. -/
@[sga "3 I 6.6" "special case"]
theorem isQuasicoherent_homology_derivedPushforward_qcqs {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y] :
    ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent :=
  fun K i =>
    AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_qcqs
      f K.obj K.2 i

end Stacks.Duality

end
