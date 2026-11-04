module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaStrictlyPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaUnitCoherence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaUnitKFlat

/-!
# The projection formula at a finite-free summand placed in degree zero

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, `E ∈ D(𝒪_X)` and let `G` be an
`𝒪_Y`-module which is a direct summand of a finite free `𝒪_Y`-module.  The projection-formula
morphism of [Stacks, Tag 0B53]

`Rf_*E ⊗^𝐋_{𝒪_Y} G[0] ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*G[0])`

is an isomorphism, for an arbitrary morphism `f` and an arbitrary `E`.

## Main results

* `Stacks.Cohomology.ProjectionFormulaPerfect.isIso_projectionFormulaMap_single_zero`: the
  statement above.
* `Stacks.Cohomology.ProjectionFormulaPerfect.isIso_projectionFormulaMap_of_iso_single_zero`:
  the same for any object of `D(𝒪_Y)` isomorphic to such a `G[0]`.

## References

* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction StrictlyPerfect
open Stacks.CategoryTheory.ComponentwiseInvertibility
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.DerivedTensor.RingedSite

universe u

noncomputable section

namespace Stacks.Cohomology.ProjectionFormulaPerfect

attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing Stacks.SheafOfModules.Tensor.ringSheaf
  StrictlyPerfect.structureSheafOfRings CategoryTheory.sheafCompose
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The projection formula at a finite-free summand placed in degree zero.** For an arbitrary
morphism of ringed spaces `f : X ⟶ Y`, an arbitrary `E` in `D(𝒪_X)` and an `𝒪_Y`-module `G` which
is a direct summand of a finite free `𝒪_Y`-module, the projection-formula morphism of
[Stacks, Tag 0B53]

`Rf_*E ⊗^𝐋_{𝒪_Y} G[0] ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*G[0])`

is invertible. -/
theorem isIso_projectionFormulaMap_single_zero
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (G : OXMod.{u, u} Y) (hG : IsDirectSummandOfFiniteFree G) :
    IsIso (projectionFormulaMap f E
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj G)) := by
  let _ : (derivedPushforward f).CommShift ℤ := (derivedAdjunction f).rightAdjointCommShift ℤ
  let _ : (derivedAdjunction f).CommShift ℤ := (derivedAdjunction f).commShift_of_leftAdjoint ℤ
  have _ : (derivedPushforward f).IsTriangulated :=
    (derivedAdjunction f).isTriangulated_rightAdjoint
  let _ : (projectionFormulaSource f E).CommShift ℤ :=
    (canonicalDerivedTensorProduct Y.sheaf).commShift_right _
  have _ : (projectionFormulaSource f E).IsTriangulated :=
    (canonicalDerivedTensorProduct Y.sheaf).exact_right _
  let _ : ((derivedTensorProductFunctor X.sheaf).obj E).CommShift ℤ :=
    (canonicalDerivedTensorProduct X.sheaf).commShift_right _
  have _ : ((derivedTensorProductFunctor X.sheaf).obj E).IsTriangulated :=
    (canonicalDerivedTensorProduct X.sheaf).exact_right _
  let _ : ((derivedTensorProductFunctor X.sheaf).obj E ⋙ derivedPushforward f).CommShift ℤ :=
    Functor.CommShift.comp _ _
  let _ : (projectionFormulaTarget f E).CommShift ℤ := Functor.CommShift.comp _ _
  have _ : (projectionFormulaTarget f E).IsTriangulated :=
    inferInstanceAs ((derivedPullback f ⋙ ((derivedTensorProductFunctor X.sheaf).obj E ⋙
      derivedPushforward f)).IsTriangulated)
  let H := DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0
  let β := Functor.whiskerLeft H (projectionFormulaTransformation f E)
  obtain ⟨m, ⟨r⟩⟩ := (isDirectSummandOfFiniteFree_iff_retract G).mp hG
  have hfree : IsIso (β.app (finiteFree Y m)) :=
    isIso_app_of_biproduct (H ⋙ projectionFormulaSource f E)
      (H ⋙ projectionFormulaTarget f E) (fun _ : Fin m => structureModule Y) β
      (fun _ => isIso_projectionFormulaMap_unitObject_unconditional f E)
  exact isIso_app_of_splitRetract (H ⋙ projectionFormulaSource f E)
    (H ⋙ projectionFormulaTarget f E) β r.i r.r r.retract hfree

/-- **The projection formula at any object of `D(𝒪_Y)` isomorphic to a finite-free summand placed
in degree zero.** For an arbitrary morphism of ringed spaces `f : X ⟶ Y`, an arbitrary `E` in
`D(𝒪_X)` and `K ≅ G[0]` with `G` a direct summand of a finite free `𝒪_Y`-module, the
projection-formula morphism `projectionFormulaMap f E K` is invertible. -/
theorem isIso_projectionFormulaMap_of_iso_single_zero
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (G : OXMod.{u, u} Y) (hG : IsDirectSummandOfFiniteFree G)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (e : (DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj G ≅ K) :
    IsIso (projectionFormulaMap f E K) :=
  isIso_projectionFormulaMap_of_iso_right f E e
    (isIso_projectionFormulaMap_single_zero f E G hG)

end Stacks.Cohomology.ProjectionFormulaPerfect

end

end
