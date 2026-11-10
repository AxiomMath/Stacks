module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaPerfect

/-!
# The projection formula at shifts of the structure sheaf from a shift compatibility

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and `E ∈ D(𝒪_X)`. If the
projection-formula morphism, read as the natural transformation
`projectionFormulaTransformation f E` between the two functors of `K`, commutes with the shift,
then it is invertible at every shift `𝒪_Y[0]⟦m⟧`, hence at `𝒪_Y[i]` for every `i`, at every
strictly perfect complex and at every perfect complex.

## Main results

All in the namespace `Stacks.Cohomology.ProjectionFormulaPerfect`.

* `isIso_app_shift`: invertibility of a shift-compatible natural transformation at an object
  passes to every shift of the object.
* `isIso_projectionFormulaMap_unitShift_of_commShift`: invertibility at `𝒪_Y[0]⟦m⟧`, for every
  `m`, from the shift compatibility.
* `isIso_projectionFormulaMap_singleUnit_of_commShift`: invertibility at `𝒪_Y[i]`, for every `i`.
* `isIso_projectionFormulaMap_of_isStrictlyPerfect_of_commShift`: invertibility at a strictly
  perfect complex, from the shift compatibility.
* `isIso_projectionFormulaMap_of_isPerfect_of_commShift`: invertibility at a perfect complex,
  from the shift compatibility at every morphism of ringed spaces and every `E`.

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

/-- If `τ : F ⟶ G` is a natural transformation commuting with the shift and `τ.app W` is an
isomorphism, then `τ.app (W⟦m⟧)` is an isomorphism for every `m : ℤ`. -/
theorem isIso_app_shift {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ] {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G)
    [NatTrans.CommShift τ ℤ] (W : C) [IsIso (τ.app W)] (m : ℤ) : IsIso (τ.app (W⟦m⟧)) := by
  rw [NatTrans.app_shift τ m W]
  infer_instance

/-- The commutation of the source functor `K ↦ Rf_*E ⊗^L_{𝒪_Y} K` with the shift, given by the
`commShift_right` field of the derived tensor product. -/
@[instance_reducible]
def projectionFormulaSourceCommShift : (projectionFormulaSource f E).CommShift ℤ :=
  (canonicalDerivedTensorProduct Y.sheaf).commShift_right _

/-- If the projection-formula morphism, read as the natural transformation
`projectionFormulaTransformation f E`, commutes with the shift (`hcs`), then it is invertible at
`𝒪_Y[0]⟦m⟧` for every `m : ℤ`. -/
theorem isIso_projectionFormulaMap_unitShift_of_commShift
    (hcs :
      letI := projectionFormulaSourceCommShift f E
      letI := projectionFormulaTargetCommShift f E
      NatTrans.CommShift (projectionFormulaTransformation f E) ℤ)
    (m : ℤ) :
    IsIso (projectionFormulaMap f E
      (((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj (structureModule Y))⟦m⟧)) := by
  let := projectionFormulaSourceCommShift f E
  let := projectionFormulaTargetCommShift f E
  let := hcs
  have h0 : IsIso ((projectionFormulaTransformation f E).app
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj (structureModule Y))) :=
    isIso_projectionFormulaMap_unitObject_unconditional f E
  exact isIso_app_shift (projectionFormulaTransformation f E)
    ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj (structureModule Y)) m

/-- If the projection-formula morphism commutes with the shift (`hcs`), then it is invertible at
the structure sheaf `𝒪_Y[i]` placed in degree `i`, for every `i : ℤ`. -/
theorem isIso_projectionFormulaMap_singleUnit_of_commShift
    (hcs :
      letI := projectionFormulaSourceCommShift f E
      letI := projectionFormulaTargetCommShift f E
      NatTrans.CommShift (projectionFormulaTransformation f E) ℤ)
    (i : ℤ) :
    IsIso (projectionFormulaMap f E
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) i).obj (structureModule Y))) :=
  isIso_projectionFormulaMap_singleUnit_of_unitShift f E
    (isIso_projectionFormulaMap_unitShift_of_commShift f E hcs) i

/-- For a morphism of ringed spaces `f`, an arbitrary `E ∈ D(𝒪_X)` and a strictly perfect
complex `P` of `𝒪_Y`-modules, the projection-formula morphism

`Rf_*E ⊗^L_{𝒪_Y} P ⟶ Rf_*(E ⊗^L_{𝒪_X} Lf^*P)`

is invertible. -/
theorem isIso_projectionFormulaMap_of_isStrictlyPerfect_of_commShift
    (P : CochainComplex (OXMod.{u, u} Y) ℤ) (hP : IsStrictlyPerfect P) :
    IsIso (projectionFormulaMap f E (DerivedCategory.Q.obj P)) :=
  isIso_projectionFormulaMap_of_isStrictlyPerfect_of_singleUnit f E P hP

attribute [local instance] hasSheafifyOpens wEqualsLocallyBijectiveOpens

/-- For a morphism of ringed spaces `f`, an arbitrary `E ∈ D(𝒪_X)` and a perfect complex `K` of
`𝒪_Y`-modules, the projection-formula morphism `Rf_*E ⊗^L_{𝒪_Y} K ⟶ Rf_*(E ⊗^L_{𝒪_X} Lf^*K)`
is invertible. -/
theorem isIso_projectionFormulaMap_of_isPerfect_of_commShift
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (hK : AlgebraicGeometry.RingedSpace.IsPerfect K) :
    IsIso (projectionFormulaMap f E K) :=
  isIso_projectionFormulaMap_of_isPerfect f E K hK

end Stacks.Cohomology.ProjectionFormulaPerfect

end

end
