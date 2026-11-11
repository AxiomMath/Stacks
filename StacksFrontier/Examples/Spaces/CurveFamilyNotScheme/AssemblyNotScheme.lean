module

public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.AssemblySolution
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.AssemblyFibres
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.NotScheme.Space
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations

/-!
# The contraction of the strict transform is not a scheme

Let `(f : h_Z ⟶ X, T, a)` be a solution of Artin's contraction problem for the strict transform
`C ⊆ Z` of the central fibre in the blowup `Z` of the cubic surface `Y` at the chosen point `y`
(`Stacks.Examples.CurveFamilyNotScheme.exists_solution_cubicContraction`). This file shows, in the
construction of [Stacks, Tag 0D5E], that `X` is not representable by a scheme, as soon as `X` is
proper over `A¹_k`, `f` is surjective on points and `T` is a single point; these three facts
about `X` are the hypotheses of
`Stacks.Examples.CurveFamilyNotScheme.not_exists_iso_yoneda_solution_cubicContraction`.

The remaining inputs of `Stacks.Examples.CurveFamilyNotScheme.not_exists_iso_yoneda_of_transport`
are proved here: `f` is injective on points off `C`, because it maps `Z ∖ C` isomorphically onto
the open subspace `U` of `X`; it collapses `C` to the point of `T`, because `C = f⁻¹(T)`; and the
scheme-level inputs (the blowup `π : Z ⟶ Y` is closed, the central fibre of `Z` is `E ∪ C`, the
exceptional curve `E` maps to `y`, property (2) of `y`, and the fibres of `Z ∖ C` over `A¹_k` are
infinite) come from `StacksFrontier/Examples/Spaces/CurveFamilyNotScheme/AssemblyFibres.lean` and
`Instance/CentralFibre.lean`.

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.injective_pointsMap_f_of_notMem`: `f` is injective on
  points off `C`.
* `Stacks.Examples.CurveFamilyNotScheme.not_exists_iso_yoneda_solution_cubicContraction`: `X` is
  not a scheme.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Space

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

attribute [local instance] Space.pointTopology

variable {k : Type u} [Field k] [IsAlgClosed k] [Uncountable k] {h3 : ringChar k ≠ 3}
  {X : (BigFppfOver (cubicSite k h3) (affineLine k) (cubicSite_contains_affineLine k h3))ᵒᵖ ⥤
    Type u}
  (s : Artin.ContractionSituation.Solution (cubicContraction k h3) X)

/-- The points of `X' = h_Z` are the points of `Z`. -/
abbrev cubicPointsEquiv :
    Space.points _ _ _ (cubicContraction k h3).X' ≃ cubicBlowup k h3 :=
  pointsEquivScheme _ _ _ (cubicBlowupObject k h3)

/-- A point of `Z` lies in `T'` exactly when it lies in `C`. -/
theorem symm_cubicPointsEquiv_mem_T'_iff (z : cubicBlowup k h3) :
    (cubicPointsEquiv (h3 := h3)).symm z ∈ (cubicContraction k h3).T' ↔
      z ∈ ((strictTransformCentralFibre k h3).support : Set (cubicBlowup k h3)) := by
  have hsymm :
      pointsToScheme _ _ _ (cubicBlowupObject k h3) ((cubicPointsEquiv (h3 := h3)).symm z) = z :=
    (cubicPointsEquiv (h3 := h3)).apply_symm_apply z
  change pointsToScheme _ _ _ (cubicBlowupObject k h3) ((cubicPointsEquiv (h3 := h3)).symm z) ∈
    ((strictTransformCentralFibre k h3).support : Set (cubicBlowup k h3)) ↔ _
  rw [hsymm]

/-- **`f` is injective on points off `C`**: two points of `Z ∖ C` with the same image in `|X|`
are equal, because `f` maps the open subspace `U' = h_{Z ∖ C}` isomorphically onto `U ⊆ X`. -/
theorem injective_pointsMap_f_of_notMem (z₁ z₂ : cubicBlowup k h3)
    (hz₁ : z₁ ∉ ((strictTransformCentralFibre k h3).support : Set (cubicBlowup k h3)))
    (hz₂ : z₂ ∉ ((strictTransformCentralFibre k h3).support : Set (cubicBlowup k h3)))
    (h : pointsMap _ _ _ _ s.f ((cubicPointsEquiv (h3 := h3)).symm z₁) =
      pointsMap _ _ _ _ s.f ((cubicPointsEquiv (h3 := h3)).symm z₂)) :
    z₁ = z₂ := by
  have hmem : ∀ z : cubicBlowup k h3,
      z ∉ ((strictTransformCentralFibre k h3).support : Set (cubicBlowup k h3)) →
      ∃ u, pointsMap _ _ _ (cubicContraction k h3).U'.toFunctor (cubicContraction k h3).U'.ι u =
        (cubicPointsEquiv (h3 := h3)).symm z := fun z hz => by
    have h1 : (cubicPointsEquiv (h3 := h3)).symm z ∈ (cubicContraction k h3).T'ᶜ :=
      fun hT => hz ((symm_cubicPointsEquiv_mem_T'_iff z).mp hT)
    rw [← (cubicContraction k h3).range_pointsMap_ι_U'] at h1
    exact h1
  obtain ⟨u₁, hu₁⟩ := hmem z₁ hz₁
  obtain ⟨u₂, hu₂⟩ := hmem z₂ hz₂
  have hU : Function.Injective (pointsMap _ _ _ s.U.toFunctor s.U.ι) :=
    injective_pointsMap_of_isImmersion _ _ _ s.isAlgebraicSpace_X s.U.ι
      (isImmersion_of_isOpenImmersion _ _ _ s.isOpenSubspace_U.2)
  have h1 : ∀ w, pointsMap _ _ _ s.U.toFunctor s.isoU.inv
      (pointsMap _ _ _ (cubicContraction k h3).U'.toFunctor s.isoU.hom w) = w := fun w => by
    rw [← Function.comp_apply (f := pointsMap _ _ _ s.U.toFunctor s.isoU.inv),
      ← pointsMap_comp, Iso.hom_inv_id, pointsMap_id, id]
  have hcomp : ∀ u, pointsMap _ _ _ _ s.f
      (pointsMap _ _ _ (cubicContraction k h3).U'.toFunctor (cubicContraction k h3).U'.ι u) =
        pointsMap _ _ _ s.U.toFunctor s.U.ι
          (pointsMap _ _ _ (cubicContraction k h3).U'.toFunctor s.isoU.hom u) := fun u => by
    rw [← Function.comp_apply (f := pointsMap _ _ _ _ s.f), ← pointsMap_comp,
      ← Function.comp_apply (f := pointsMap _ _ _ s.U.toFunctor s.U.ι), ← pointsMap_comp,
      s.isoU_comp_ι]
  rw [← hu₁, ← hu₂, hcomp, hcomp] at h
  have hu : u₁ = u₂ := by
    rw [← h1 u₁, ← h1 u₂, hU h]
  have h2 : (cubicPointsEquiv (h3 := h3)).symm z₁ = (cubicPointsEquiv (h3 := h3)).symm z₂ := by
    rw [← hu₁, ← hu₂, hu]
  exact (cubicPointsEquiv (h3 := h3)).symm.injective h2

/-- **`f` collapses `C` to the point of `T`**: `C = f⁻¹(T)`, so if `T = {x}` every point of `C`
maps to `x`. -/
theorem pointsMap_f_eq_of_mem {x : points _ _ _ X} (hT : s.T = {x}) (z : cubicBlowup k h3)
    (hz : z ∈ ((strictTransformCentralFibre k h3).support : Set (cubicBlowup k h3))) :
    pointsMap _ _ _ _ s.f ((cubicPointsEquiv (h3 := h3)).symm z) = x := by
  have hT' := (symm_cubicPointsEquiv_mem_T'_iff z).mpr hz
  rw [← s.preimage_T] at hT'
  have hx : pointsMap _ _ _ _ s.f ((cubicPointsEquiv (h3 := h3)).symm z) ∈ s.T := hT'
  rw [hT] at hx
  exact hx

/-- **The contraction of `C` is not a scheme** ([Stacks, Tag 0D5E]). Let `(f : h_Z ⟶ X, T, a)` be
a solution of Artin's contraction problem for `C ⊆ Z`. If `X` is proper over `A¹_k`, `f` is
surjective on points and `T` is a single point, then `X` is not representable by a scheme. -/
theorem not_exists_iso_yoneda_solution_cubicContraction
    (hXproper : ∀ g : X ⟶ yoneda.obj (baseObj (B := cubicSite k h3)
      (hS := cubicSite_contains_affineLine k h3)), Space.IsProper _ _ _ g)
    (hF : Function.Surjective (pointsMap _ _ _ _ s.f)) (hT : ∃ x, s.T = {x}) :
    ¬ ∃ U : BigFppfOver (cubicSite k h3) (affineLine k) (cubicSite_contains_affineLine k h3),
      Nonempty (X ≅ yoneda.obj U) := by
  obtain ⟨x, hx⟩ := hT
  obtain ⟨y', hy', hy'y⟩ := exists_ne_chosenPoint_cubicSurfaceToLine_eq_originPoint k h3
  exact not_exists_iso_yoneda_of_transport (Zo := cubicBlowupObject k h3) s.isAlgebraicSpace_X
    hXproper s.f hF (pointBlowupToBase (chosenPoint k h3) (isClosed_chosenPoint k h3))
    (pointBlowupToBase (chosenPoint k h3) (isClosed_chosenPoint k h3)).isClosedMap
    (cubicSurfaceToLine k) rfl (s₀ := originPoint k) (y := chosenPoint k h3)
    (E := exceptionalSet (chosenPoint k h3) (isClosed_chosenPoint k h3))
    (C := ((strictTransformCentralFibre k h3).support : Set (cubicBlowup k h3)))
    (mem_exceptionalSet_union_of_cubicSurfaceToLine_eq k h3)
    (fun _ hz => pointBlowupToBase_eq_of_mem_exceptionalSet _ _ hz) y' hy' hy'y
    (exists_ne_chosenPoint_of_isClosed_surjective k h3) x (pointsMap_f_eq_of_mem s hx)
    (infinite_setOf_cubicBlowup_notMem_strictTransform k h3)
    (injective_pointsMap_f_of_notMem s)

end Stacks.Examples.CurveFamilyNotScheme

end
