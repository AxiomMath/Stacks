module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedBaseChangeGlobal
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaCokernel
public import StacksFrontier.Homology.KFlat.FilteredColimitShifts
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaShiftedUnit

/-!
# The dévissage of the projection formula over an affine base

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and `E` an object of `D(𝒪_X)`.
[Stacks, Tag 08EU] asserts that the projection-formula morphism of [Stacks, Tag 0B53]

`Rf_*E ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)`

is invertible for `K` in `D_QCoh(𝒪_Y)`, and proves it by a dévissage in `K`: direct sums,
distinguished triangles, and the reduction of a general `K` over an affine base to the shifts of
the structure sheaf through the equivalence `D(A) ≌ D_QCoh(𝒪_{Spec A})` of [Stacks, Tag 06Z0] and
the remark of [Stacks, Tag 09PB].  This file carries out that dévissage.

## Main results

* `Stacks.Cohomology.ProjectionFormulaDevissage.isIso_projectionFormulaMap_twoOutOfThree`: for a
  distinguished triangle of `D(𝒪_Y)`, invertibility of the projection-formula morphism at all
  shifts of two of the three vertices gives it at all shifts of the third, in each of the three
  rotations.
* `Stacks.Cohomology.ProjectionFormulaDevissage.isIso_projectionFormulaMap_coproduct`:
  invertibility at each member of a family gives it at the direct sum, as soon as the target
  functor `K ↦ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)` commutes with that direct sum.
* `Stacks.Cohomology.ProjectionFormulaDevissage.isIso_projectionFormulaMap_of_derivedModuleFunctor`
  — for a ring `A` and an exact, direct-sum-preserving functor `Φ : D(A) ⥤ D(𝒪_Y)` carrying the
  regular module in degree zero to `𝒪_Y[0]`, the projection-formula morphism is invertible at
  `Φ.obj M` for every `M` in `D(A)`.
* `Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_third_of_all_shifts`: a natural
  transformation between exact functors, not assumed compatible with the shift, that is
  invertible at every shift of the first two vertices of a distinguished triangle is invertible at
  every shift of the third.

## Implementation notes

The dévissage is run on the property "the projection-formula morphism is invertible at every shift
of this object", which is closed under the shift by construction. The projection-formula morphism
is not known to commute with the shift in the sense of `CategoryTheory.NatTrans.CommShift`: the
shift isomorphisms of its source and of its target come from the `commShift_right` datum of the
derived tensor product of [Stacks, Tag 06YU] and from the adjunction of [Stacks, Tag 079W], and no
coherence between them is recorded.

The hypothesis `hpush` of `isIso_projectionFormulaMap_of_derivedModuleFunctor`, that
`K ↦ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)` commutes with the direct sums of the objects reached by `Φ`, is the
assertion that `Rf_*` commutes with those direct sums, since `Lf^*` and `- ⊗^𝐋_{𝒪_X} E` are left
adjoints. This is [Stacks, Tag 08DZ] for a quasi-compact and quasi-separated morphism of schemes
and complexes with quasi-coherent cohomology, and is false for a bare ringed space. Over
`Y = Spec A`, the functor `Φ` of [Stacks, Tag 06Z0] is the composite of
`Stacks.DerivedQCoh.derivedTildeEquiv`, the comparison functor of [Stacks, Tag 06VT] and the
inclusion `D_QCoh(𝒪_Y) ⥤ D(𝒪_Y)`.

The direct sums in `CochainComplex.KFlat.property_of_coproducts_of_two_out_of_three_of_shifts`
([Stacks, Tag 09PB]) are indexed by the types of the module universe, so the two preservation
hypotheses are quantified over `Type u`.

## References

* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 09PB](https://stacks.math.columbia.edu/tag/09PB)
* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.Cohomology.ProjectionFormulaPerfect
open Stacks.Cohomology.ProjectionFormulaShiftedUnit
open Stacks.DerivedTensor.RingedSite

universe u

noncomputable section

/-! ### The missing rotation of the triangle step -/

namespace Stacks.CategoryTheory.ComponentwiseInvertibility

/-- A natural transformation between exact functors, invertible at every shift of the first and
second vertices of a distinguished triangle, is invertible at every shift of the third. -/
theorem isIso_app_third_of_all_shifts {C : Type*} [Category* C] {D : Type*} [Category* D]
    [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [HasZeroObject D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F G : C ⥤ D) (hFs : F.CommShift ℤ) (hGs : G.CommShift ℤ)
    (hFt : letI := hFs; F.IsTriangulated) (hGt : letI := hGs; G.IsTriangulated)
    (α : F ⟶ G) (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : ∀ n : ℤ, IsIso (α.app (T.obj₁⟦n⟧)))
    (h₂ : ∀ n : ℤ, IsIso (α.app (T.obj₂⟦n⟧))) :
    ∀ n : ℤ, IsIso (α.app (T.obj₃⟦n⟧)) := by
  let _ : F.CommShift ℤ := hFs
  let _ : G.CommShift ℤ := hGs
  have _ : F.IsTriangulated := hFt
  have _ : G.IsTriangulated := hGt
  intro n
  exact isIso_app_third_of_distinguished F G α ((shiftFunctor (Triangle C) n).obj T)
    (T.shift_distinguished hT n) (h₁ n) (h₂ n)
    ((α.isIso_app_iff_of_iso ((shiftFunctorAdd C n 1).app T.obj₁)).1 (h₁ (n + 1)))
    ((α.isIso_app_iff_of_iso ((shiftFunctorAdd C n 1).app T.obj₂)).1 (h₂ (n + 1)))

end Stacks.CategoryTheory.ComponentwiseInvertibility

namespace Stacks.Cohomology.ProjectionFormulaDevissage

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

variable (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))

/-! ### The triangle step -/

/-- Let `Δ` be a distinguished triangle of `D(𝒪_Y)`. If the projection-formula morphism of
[Stacks, Tag 0B53] is invertible at every shift of two of the three vertices of `Δ`, it is
invertible at every shift of the third, in each of the three rotations. -/
@[stacks 08EU "the triangle step of the source's dévissage, with no hypothesis: for a \
distinguished triangle of D(𝒪_Y), invertibility of the Tag 0B53 map at all shifts of two of the \
three vertices gives it at all shifts of the third, in each of the three rotations. The source \
states this as `two out of three of the functors being exact`; the direct-sum step is \
isIso_projectionFormulaMap_coproduct and the affine reduction is \
isIso_projectionFormulaMap_of_derivedModuleFunctor, both of which carry a geometric input and so \
are not registered"]
theorem isIso_projectionFormulaMap_twoOutOfThree
    (Δ : Triangle (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))))
    (hΔ : Δ ∈ distTriang _) :
    ((∀ n : ℤ, IsIso (projectionFormulaMap f E (Δ.obj₁⟦n⟧))) →
        (∀ n : ℤ, IsIso (projectionFormulaMap f E (Δ.obj₂⟦n⟧))) →
        ∀ n : ℤ, IsIso (projectionFormulaMap f E (Δ.obj₃⟦n⟧))) ∧
      ((∀ n : ℤ, IsIso (projectionFormulaMap f E (Δ.obj₁⟦n⟧))) →
        (∀ n : ℤ, IsIso (projectionFormulaMap f E (Δ.obj₃⟦n⟧))) →
        ∀ n : ℤ, IsIso (projectionFormulaMap f E (Δ.obj₂⟦n⟧))) ∧
      ((∀ n : ℤ, IsIso (projectionFormulaMap f E (Δ.obj₂⟦n⟧))) →
        (∀ n : ℤ, IsIso (projectionFormulaMap f E (Δ.obj₃⟦n⟧))) →
        ∀ n : ℤ, IsIso (projectionFormulaMap f E (Δ.obj₁⟦n⟧))) := by
  let hFs : (projectionFormulaSource f E).CommShift ℤ :=
    (canonicalDerivedTensorProduct Y.sheaf).commShift_right _
  have hFt : (projectionFormulaSource f E).IsTriangulated :=
    (canonicalDerivedTensorProduct Y.sheaf).exact_right _
  let hGs : (projectionFormulaTarget f E).CommShift ℤ := projectionFormulaTargetCommShift f E
  have hGt : (projectionFormulaTarget f E).IsTriangulated :=
    projectionFormulaTarget_isTriangulated f E
  exact ⟨Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_third_of_all_shifts
      _ _ hFs hGs hFt hGt (projectionFormulaTransformation f E) Δ hΔ,
    Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_middle_of_all_shifts
      _ _ (projectionFormulaTransformation f E) Δ hΔ,
    Stacks.Cohomology.DerivedBaseChange.isIso_app_first_of_all_shifts
      _ _ hFs hGs hFt hGt (projectionFormulaTransformation f E) Δ hΔ⟩

/-! ### The direct-sum step -/

/-- Let `K : ι → D(𝒪_Y)` be a family with a direct sum. If the projection-formula morphism of
[Stacks, Tag 0B53] is invertible at each `K i`, it is invertible at `⨁ᵢ K i`, provided the target
functor `K ↦ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)` carries that direct sum to a direct sum. -/
theorem isIso_projectionFormulaMap_coproduct {ι : Type*}
    (K : ι → DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) [HasCoproduct K]
    (htarget : PreservesColimitsOfShape (Discrete ι) (projectionFormulaTarget f E))
    (hK : ∀ i, IsIso (projectionFormulaMap f E (K i))) :
    IsIso (projectionFormulaMap f E (∐ K)) := by
  have hsrc := preservesColimitsOfSize_projectionFormulaSource f E
  exact CategoryTheory.NatTrans.isIso_app_of_isColimit_mapCocone
    (projectionFormulaTransformation f E) (colimit.cocone (Discrete.functor K))
    (isColimitOfPreserves _ (colimit.isColimit _))
    (isColimitOfPreserves _ (colimit.isColimit _)) fun j ↦ hK j.as

/-! ### The dévissage over an affine base -/

/-- Let `f : X ⟶ Y` be a morphism of ringed spaces, `E` an object of `D(𝒪_X)`, `A` a ring and

`Φ : D(A) ⥤ D(𝒪_Y)`

an exact functor commuting with the direct sums indexed by the module universe and carrying the
regular module in degree zero to the structure sheaf in degree zero.  If the target functor
`K ↦ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)` commutes with the direct sums of the objects `Φ` reaches, then the
projection-formula morphism of [Stacks, Tag 0B53]

`Rf_*E ⊗^𝐋_{𝒪_Y} Φ(M) ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*Φ(M))`

is an isomorphism for every `M` in `D(A)`. -/
theorem isIso_projectionFormulaMap_of_derivedModuleFunctor
    {A : Type u} [Ring A]
    (Φ : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (hΦshift : Φ.CommShift ℤ) (hΦexact : letI := hΦshift; Φ.IsTriangulated)
    (hΦsum : ∀ ι : Type u, PreservesColimitsOfShape (Discrete ι) Φ)
    (hpush : ∀ ι : Type u,
      PreservesColimitsOfShape (Discrete ι) (Φ ⋙ projectionFormulaTarget f E))
    (e : Φ.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      (ModuleCat.of A (Shrink.{u} A))) ≅ singleUnit Y)
    (M : DerivedCategory (ModuleCat.{u} A)) :
    IsIso (projectionFormulaMap f E (Φ.obj M)) := by
  let _ : Φ.CommShift ℤ := hΦshift
  have _ : Φ.IsTriangulated := hΦexact
  let _ : (projectionFormulaSource f E).CommShift ℤ :=
    (canonicalDerivedTensorProduct Y.sheaf).commShift_right _
  have _ : (projectionFormulaSource f E).IsTriangulated :=
    (canonicalDerivedTensorProduct Y.sheaf).exact_right _
  let _ : (projectionFormulaTarget f E).CommShift ℤ := projectionFormulaTargetCommShift f E
  have _ : (projectionFormulaTarget f E).IsTriangulated :=
    projectionFormulaTarget_isTriangulated f E
  let hFs : (Φ ⋙ projectionFormulaSource f E).CommShift ℤ := Functor.CommShift.comp _ _
  have hFt : (Φ ⋙ projectionFormulaSource f E).IsTriangulated := inferInstance
  let hGs : (Φ ⋙ projectionFormulaTarget f E).CommShift ℤ := Functor.CommShift.comp _ _
  have hGt : (Φ ⋙ projectionFormulaTarget f E).IsTriangulated := inferInstance
  set β := Functor.whiskerLeft Φ (projectionFormulaTransformation f E)
  have key : ∀ N : DerivedCategory (ModuleCat.{u} A), ∀ n : ℤ, IsIso (β.app (N⟦n⟧)) := by
    refine (CochainComplex.KFlat.property_of_coproducts_of_two_out_of_three_of_shifts
      (R := A)).2 (fun N ↦ ∀ n : ℤ, IsIso (β.app (N⟦n⟧))) ?_ ?_ ?_
    · intro ι N _ hN n
      have hsrc := hΦsum ι
      have htgt := hpush ι
      have hsrc' : PreservesColimitsOfShape (Discrete ι) (Φ ⋙ projectionFormulaSource f E) := by
        have := preservesColimitsOfSize_projectionFormulaSource.{u} f E
        exact comp_preservesColimitsOfShape _ _
      exact CategoryTheory.NatTrans.isIso_app_of_isColimit_mapCocone β
        ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) n).mapCocone
          (colimit.cocone (Discrete.functor N)))
        (isColimitOfPreserves _ (isColimitOfPreserves _ (colimit.isColimit _)))
        (isColimitOfPreserves _ (isColimitOfPreserves _ (colimit.isColimit _)))
        fun j ↦ hN j.as n
    · intro Δ hΔ
      exact ⟨Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_third_of_all_shifts
          _ _ hFs hGs hFt hGt β Δ hΔ,
        Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_middle_of_all_shifts
          _ _ β Δ hΔ,
        Stacks.Cohomology.DerivedBaseChange.isIso_app_first_of_all_shifts
          _ _ hFs hGs hFt hGt β Δ hΔ⟩
    · intro k n
      exact isIso_projectionFormulaMap_of_iso_shift_unit f E _ (k + n)
        ((Φ.commShiftIso n).app _ ≪≫ (shiftFunctor _ n).mapIso ((Φ.commShiftIso k).app _) ≪≫
          (shiftFunctor _ n).mapIso ((shiftFunctor _ k).mapIso e) ≪≫
          ((shiftFunctorAdd' (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
            k n (k + n) rfl).app (singleUnit Y)).symm)
  exact CategoryTheory.NatTrans.isIso_app_of_iso β
    ((shiftFunctorZero (DerivedCategory (ModuleCat.{u} A)) ℤ).app M) (key M 0)

end Stacks.Cohomology.ProjectionFormulaDevissage

end

end
