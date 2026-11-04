module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaStrictlyPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaUnitKFlat

/-!
# The base case of [Stacks, Tag 0B54] at the degree zero is discharged

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and `E ∈ D(𝒪_X)`.  The dévissage
`Stacks.Cohomology.ProjectionFormulaPerfect.isIso_projectionFormulaMap_of_isStrictlyPerfect` asks
for the projection-formula morphism of [Stacks, Tag 0B53] to be invertible at `𝒪_Y[i]⟦n⟧` for
every pair of integers; by `isIso_projectionFormulaMap_singleUnit_iff_unitShift` that family is
the family `𝒪_Y[0]⟦m⟧` of the shifts of one object, and the member `m = 0` is now a theorem,
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitObject_unconditional`
([Stacks, Tag 08EU]).  This file removes that member from the hypothesis.

## Main results

* `Stacks.Cohomology.ProjectionFormulaPerfect.isIso_projectionFormulaMap_unitShift_zero`: Tag
  08EU read at `𝒪_Y[0]⟦0⟧` rather than at `𝒪_Y[0]`, with no hypothesis.
* `isIso_projectionFormulaMap_singleUnit_of_unitShift_ne_zero` and
  `isIso_projectionFormulaMap_singleUnit_shift_of_unitShift_ne_zero`: the two shapes in which the
  dévissage consumes its base case, from invertibility at the **nonzero** shifts of `𝒪_Y[0]`
  alone.
* `isIso_projectionFormulaMap_of_isStrictlyPerfect_of_unitShift_ne_zero`: the dévissage with its
  base case asked for only at the nonzero shifts of `𝒪_Y[0]`.

All four are in the namespace `Stacks.Cohomology.ProjectionFormulaPerfect`.

## ⚠ SUPERSEDED — nothing below is owed for [Stacks, Tag 0B54] any more ⚠

The hypothesis this file was written to shrink is now discharged outright:
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitShift_unconditional`
in `ProjectionFormulaUnitShifts.lean` proves invertibility at `𝒪_Y[0]⟦m⟧` for **every** `m`, with
no hypothesis, from the abstract projection formula at a ⊗-invertible object.  So
`isIso_projectionFormulaMap_of_isStrictlyPerfect` and `isIso_projectionFormulaMap_of_isPerfect`
are both unconditional, the theorems below have redundant hypotheses and are kept only because
consumers hold them in that shape, and
`Stacks.Cohomology.DerivedPullbackTensor.ModelsComparisonCommShift₂` is **not** owed for Tag 0B54.
The account that follows is accurate about the route this file took and is no longer a statement
of what the tag owes.

## What the earlier route still owed, and what it was not

That the remaining hypothesis *follows* from the shift compatibility named below is now proved,
in the sibling module `ProjectionFormulaUnitShift`:
`Stacks.Cohomology.ProjectionFormulaPerfect.isIso_projectionFormulaMap_unitShift_of_commShift`
derives every member of it from
`CategoryTheory.NatTrans.CommShift (projectionFormulaTransformation f E) ℤ`, and
`isIso_projectionFormulaMap_of_isPerfect_of_commShift` there runs that through the whole of
[Stacks, Tag 0B54].  So the list below is the list of what is owed *for that one datum*, and it
is the only thing between this development and Tag 0B54 with no hypothesis at all.

The remaining hypothesis is invertibility at `𝒪_Y[0]⟦m⟧` for `m ≠ 0`.  It is **not** a case of
the unitor coherence that Tag 08EU needed — that is discharged, for every morphism of ringed
spaces and every `E`, in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/ProjectionFormulaUnitKFlat.lean`.
It is a shift statement, and not one that the degree bookkeeping of `singleUnitShiftIso` and
`singleUnitDegreeIso` can supply: those isomorphisms permute the objects `𝒪_Y[i]⟦n⟧` among
themselves, and `𝒪_Y[0]⟦m⟧` is not isomorphic to `𝒪_Y[0]` for `m ≠ 0`.  Deducing invertibility
at `Z⟦m⟧` from invertibility at `Z` is exactly a `CategoryTheory.NatTrans.CommShift` for the
projection-formula morphism, which by `projectionFormulaMap_eq` is a shift compatibility of the
comparison of [Stacks, Tag 079U]; the comparison is
`CategoryTheory.Localization.liftNatIso` of
`Stacks.Cohomology.DerivedPullbackTensor.modelsComparison` through a localization of a *product*
of two categories, so what is needed there is a
`CategoryTheory.NatTrans.CommShift₂` in one variable.  The descent of such a datum exists —
`CategoryTheory.Localization.lift₂NatIso_hom_commShift₂` in
`StacksFrontier/CategoryTheory/Localization/BifunctorLiftNatTransCommShift.lean`, whose
`curry_map_liftNatTrans` is built to accept exactly a comparison produced by the one-variable
`liftNatIso` over a product localization — but it takes that `NatTrans.CommShift₂` as a
hypothesis, and the hypothesis is what is missing.

Two of its ingredients are now present and should not be mistaken for the whole.
`CochainComplex.KFlatBifunctor.derivedBifunctor_commShift₂Int`
(`StacksFrontier.Homology.KFlat.BifunctorCommShiftTwoInstances`) is the
`CategoryTheory.Functor.CommShift₂Int` of the bifunctor, and
`CochainComplex.KFlatBifunctor.kFlatObjects_isStableUnderShift`
(`StacksFrontier/Homology/KFlat/BifunctorShift.lean`) puts a shift on the K-flat models.  Both are
statements about the *functors*, which is what makes the compatibility expressible; the
compatibility itself is a statement about the *transformation* between them, one equation per
object, and does not follow from them.  What is still owed is therefore

* the `CategoryTheory.NatTrans.CommShift₂` of `modelsComparison` in the second variable — the
  complex-level statement, against the sign convention `(-1) ^ (p * q)` of the total tensor
  complex, which is the mathematical content; and
* the shift behaviour of `CategoryTheory.adjunctionTensorMap`, which is how
  `projectionFormulaMap` is assembled from that comparison and the derived adjunction, and which
  no lemma computes.

Note also that the `commShift₂` field of the `DerivedTensorProduct` structure is *not* constructed, so
the bifunctor datum above has to be used directly and identified with
`derivedTensorProductFunctor`, in which Tag 0B53 and Tag 079U are stated.

## References

* [Stacks Project, Tag 0B54](https://stacks.math.columbia.edu/tag/0B54)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.DerivedTensor.RingedSite

universe u

noncomputable section

namespace Stacks.Cohomology.ProjectionFormulaPerfect

attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing
  StrictlyPerfect.structureSheafOfRings CategoryTheory.sheafCompose

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

variable (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))

/-- **[Stacks, Tag 08EU] at `𝒪_Y[0]⟦0⟧`.**  The projection-formula morphism of
[Stacks, Tag 0B53] is invertible at the zero shift of the structure sheaf of `Y` placed in degree
zero, for an arbitrary morphism of ringed spaces and an arbitrary `E`.

This is
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitObject_unconditional`
transported along `CategoryTheory.shiftFunctorZero`; the shift by `0` is isomorphic to the
identity, so no shift compatibility is involved. -/
theorem isIso_projectionFormulaMap_unitShift_zero :
    IsIso (projectionFormulaMap f E
      (((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj
        (structureModule Y))⟦(0 : ℤ)⟧)) :=
  ((projectionFormulaTransformation f E).isIso_app_iff_of_iso
      ((shiftFunctorZero _ ℤ).app
        ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj (structureModule Y)))).mpr
    (isIso_projectionFormulaMap_unitObject_unconditional f E)

/-- **The base case of the dévissage, in the degree shape, from the nonzero shifts of `𝒪_Y[0]`
alone.**  If the projection-formula morphism of [Stacks, Tag 0B53] is invertible at `𝒪_Y[0]⟦m⟧`
for every `m ≠ 0`, then it is invertible at the structure sheaf of `Y` placed in every degree.

The case `m = 0` is not assumed because it is proved: it is
`isIso_projectionFormulaMap_unitShift_zero`, that is [Stacks, Tag 08EU]. -/
theorem isIso_projectionFormulaMap_singleUnit_of_unitShift_ne_zero
    (hunit : ∀ m : ℤ, m ≠ 0 → IsIso (projectionFormulaMap f E
      (((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj (structureModule Y))⟦m⟧)))
    (i : ℤ) :
    IsIso (projectionFormulaMap f E
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) i).obj (structureModule Y))) :=
  isIso_projectionFormulaMap_singleUnit_of_unitShift f E
    (fun m => by
      rcases eq_or_ne m 0 with rfl | hm
      · exact isIso_projectionFormulaMap_unitShift_zero f E
      · exact hunit m hm) i

/-- **The base case of the dévissage, in the shifted-degree shape, from the nonzero shifts of
`𝒪_Y[0]` alone.**  This is the hypothesis `hunit` of
`isIso_projectionFormulaMap_of_isStrictlyPerfect`, supplied from invertibility at `𝒪_Y[0]⟦m⟧`
for `m ≠ 0`. -/
theorem isIso_projectionFormulaMap_singleUnit_shift_of_unitShift_ne_zero
    (hunit : ∀ m : ℤ, m ≠ 0 → IsIso (projectionFormulaMap f E
      (((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj (structureModule Y))⟦m⟧)))
    (i n : ℤ) :
    IsIso (projectionFormulaMap f E
      (((DerivedCategory.singleFunctor (OXMod.{u, u} Y) i).obj (structureModule Y))⟦n⟧)) :=
  isIso_projectionFormulaMap_singleUnit_shift f E
    (isIso_projectionFormulaMap_singleUnit_of_unitShift_ne_zero f E hunit) i n

/-- **The dévissage half of [Stacks, Tag 0B54], with its base case asked for only at the nonzero
shifts of the structure sheaf placed in degree zero.**  For a morphism of ringed spaces `f`, an
arbitrary `E ∈ D(𝒪_X)` and a strictly perfect complex `P` of `𝒪_Y`-modules, the
projection-formula morphism

`Rf_*E ⊗^L_{𝒪_Y} P ⟶ Rf_*(E ⊗^L_{𝒪_X} Lf^*P)`

of [Stacks, Tag 0B53] is invertible, granted that it is invertible at `𝒪_Y[0]⟦m⟧` for every
`m ≠ 0`.

This is `isIso_projectionFormulaMap_of_isStrictlyPerfect_of_singleUnit` with the degree `0`
member of its hypothesis discharged by [Stacks, Tag 08EU], which is now unconditional.  The
hypothesis is weaker than the one it replaces and the conclusion is unchanged; what remains to be
proved is a shift compatibility, as the note at the head of this file explains. -/
theorem isIso_projectionFormulaMap_of_isStrictlyPerfect_of_unitShift_ne_zero
    (hunit : ∀ m : ℤ, m ≠ 0 → IsIso (projectionFormulaMap f E
      (((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj (structureModule Y))⟦m⟧)))
    (P : CochainComplex (OXMod.{u, u} Y) ℤ) (hP : IsStrictlyPerfect P) :
    IsIso (projectionFormulaMap f E (DerivedCategory.Q.obj P)) :=
  isIso_projectionFormulaMap_of_isStrictlyPerfect_of_singleUnit f E
    (isIso_projectionFormulaMap_singleUnit_of_unitShift_ne_zero f E hunit) P hP

end Stacks.Cohomology.ProjectionFormulaPerfect

end

end
