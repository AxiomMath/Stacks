module

public import StacksFrontier.Algebra.Homology.RightExactHomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphismOnARingedSite

/-!
# The comparison `H^n(F X) ⟶ F(H^n X)` of a left exact functor: exactness and composition

For a left exact additive functor `F` between abelian categories,
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.homologyComparison` is the canonical
comparison `H^n(F X) ⟶ F(H^n X)`.  This file records that it is an isomorphism when `F` is
exact, and how it behaves under composition of functors.

## Main results

* `homologyComparison_comp_homologyComparison_leftExactHomologyComparison`: for an exact
  functor, the comparison of `F` as a left exact functor is left inverse to its comparison
  `F(H^n X) ⟶ H^n(F X)` as a right exact functor.
* `homologyComparison_comp_of_iso_leftExactHomologyComparison`: for `e : F₁ ⋙ F₂ ≅ F₃`, the
  comparison of `F₃` is the comparison of `F₂` at `F₁(X)` followed by `F₂` of the comparison
  of `F₁`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

variable {A B C : Type*} [Category A] [Category B] [Category C] [Abelian A] [Abelian B]
  [Abelian C]

section Exact

variable (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] (X : CochainComplex A ℤ) (n : ℤ)

/-- The cycles comparison of a left exact functor is inverse to the one of an additive
functor. -/
theorem cyclesComparison_comp_cyclesComparison_leftExactHomologyComparison :
    F.cyclesComparisonRightExactHomologyComparison X n ≫ cyclesComparison F X n = 𝟙 _ := by
  have := mono_map_iCycles F X n
  apply (cancel_mono (F.map (X.iCycles n))).1
  rw [Category.assoc, cyclesComparison_comp_map_iCycles,
    Functor.cyclesComparisonRightExactHomologyComparison, HomologicalComplex.liftCycles_i,
    Category.id_comp]

/-- The comparison of the left exact functor `F` is left inverse to the comparison
`F(H^n X) ⟶ H^n(F X)` of the right exact functor `F`. -/
theorem homologyComparison_comp_homologyComparison_leftExactHomologyComparison
    [PreservesFiniteColimits F] :
    F.homologyComparisonRightExactHomologyComparison X n ≫ homologyComparison F X n = 𝟙 _ := by
  refine F.homologyComparison_hom_ext_rightExactHomologyComparison X n ?_
  rw [Functor.map_homologyπ_comp_homologyComparison_rightExactHomologyComparison_assoc,
    homologyπ_comp_homologyComparison, ← Category.assoc,
    cyclesComparison_comp_cyclesComparison_leftExactHomologyComparison, Category.id_comp,
    Category.comp_id]

end Exact

section Comp

variable (F₁ : A ⥤ B) (F₂ : B ⥤ C) (F₃ : A ⥤ C) [F₁.Additive] [F₂.Additive] [F₃.Additive]
  [PreservesFiniteLimits F₁] [PreservesFiniteLimits F₂] [PreservesFiniteLimits F₃]
  (e : F₁ ⋙ F₂ ≅ F₃) (X : CochainComplex A ℤ) (n : ℤ)

/-- For `e : F₁ ⋙ F₂ ≅ F₃`, the cycles comparison of `F₃` at `X`, read through `e`, is the cycles
comparison of `F₂` at `F₁(X)` followed by `F₂` of the cycles comparison of `F₁` at `X`. -/
theorem cyclesComparison_comp_of_iso_leftExactHomologyComparison :
    HomologicalComplex.cyclesMap
        (Functor.mapHomologicalComplexCompIsoOfIsoRightExactHomologyComparison F₁ F₂ F₃ e X).hom
        n ≫
        cyclesComparison F₂ ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) n ≫
        F₂.map (cyclesComparison F₁ X n) =
      cyclesComparison F₃ X n ≫ e.inv.app (X.cycles n) := by
  have := mono_map_iCycles F₁ X n
  apply (cancel_mono (F₂.map (F₁.map (X.iCycles n)))).1
  have h := e.inv.naturality (X.iCycles n)
  dsimp only [Functor.comp_map] at h
  rw [Category.assoc, Category.assoc, ← F₂.map_comp, cyclesComparison_comp_map_iCycles,
    cyclesComparison_comp_map_iCycles, HomologicalComplex.cyclesMap_i, Category.assoc, ← h,
    cyclesComparison_comp_map_iCycles_assoc]
  rfl

/-- **The comparison and composition of left exact functors.**  For `e : F₁ ⋙ F₂ ≅ F₃`, the
comparison of `F₃` at `X`, read through `e`, is the comparison of `F₂` at `F₁(X)` followed by
`F₂` of the comparison of `F₁` at `X`. -/
theorem homologyComparison_comp_of_iso_leftExactHomologyComparison :
    HomologicalComplex.homologyMap
        (Functor.mapHomologicalComplexCompIsoOfIsoRightExactHomologyComparison F₁ F₂ F₃ e X).hom
        n ≫
        homologyComparison F₂ ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) n ≫
        F₂.map (homologyComparison F₁ X n) =
      homologyComparison F₃ X n ≫ e.inv.app (X.homology n) := by
  apply (cancel_epi (((F₃.mapHomologicalComplex (ComplexShape.up ℤ)).obj X).homologyπ n)).1
  have h := e.inv.naturality (X.homologyπ n)
  dsimp only [Functor.comp_map] at h
  rw [HomologicalComplex.homologyπ_naturality_assoc, homologyπ_comp_homologyComparison_assoc,
    ← F₂.map_comp, homologyπ_comp_homologyComparison, F₂.map_comp,
    reassoc_of% (cyclesComparison_comp_of_iso_leftExactHomologyComparison F₁ F₂ F₃ e X n),
    homologyπ_comp_homologyComparison_assoc, h]

include e in
/-- For `e : F₁ ⋙ F₂ ≅ F₃` with the comparison of `F₂` at `F₁(X)` an isomorphism, `F₂` of the
comparison of `F₁` is an isomorphism exactly when the comparison of `F₃` is. -/
theorem isIso_map_homologyComparison_iff_leftExactHomologyComparison
    [IsIso (homologyComparison F₂ ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) n)] :
    IsIso (F₂.map (homologyComparison F₁ X n)) ↔ IsIso (homologyComparison F₃ X n) := by
  rw [← isIso_comp_right_iff _ (e.inv.app (X.homology n)),
    ← homologyComparison_comp_of_iso_leftExactHomologyComparison F₁ F₂ F₃ e X n,
    isIso_comp_left_iff, isIso_comp_left_iff]

end Comp

end Stacks.Cohomology.HypercohomologyEdge.HomologyComparison
