module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import StacksCore.CategoryTheory.Filtration.GradedStrict
public import StacksCore.CategoryTheory.GradedObject.Abelian
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.Defs

/-!
# Homological functors on `K(Fil^f(𝒜))`

Let `𝒜` be an abelian category. The category `Fil^f(𝒜)` of finite filtered objects
(`CategoryTheory.FiniteFilteredObject`, [Stacks, Tag 05RY]) is additive: it is a full subcategory
of `Fil(𝒜) = FilteredObject 𝒜 ℤᵒᵖ`, which is preadditive with a zero object and binary biproducts
([Stacks, Tag 0122]), and it contains the zero object and is closed under direct sums. The functors
`gr : Fil(𝒜) ⥤ Gr(𝒜)`, `gr^p : Fil(𝒜) ⥤ 𝒜` and `(forget F) : Fil(𝒜) ⥤ 𝒜` are additive, so they
induce triangulated functors on homotopy categories, and composing with the homological functor
`H^0` gives homological functors on `K(Fil^f(𝒜))` ([Stacks, Tag 05S0]).

## Main definitions

* `CategoryTheory.FiniteFilteredObject.gr`, `CategoryTheory.FiniteFilteredObject.grP`,
  `CategoryTheory.FiniteFilteredObject.forget`: the functors `gr`, `gr^p` and `(forget F)` on
  `Fil^f(𝒜)`.

## Main results

* `CategoryTheory.FiniteFilteredObject.homologyFunctor_gr_isHomological`,
  `CategoryTheory.FiniteFilteredObject.homologyFunctor_grP_isHomological`,
  `CategoryTheory.FiniteFilteredObject.homologyFunctor_forget_isHomological`: the functors
  `K^• ↦ H^0(gr(K^•))`, `K^• ↦ H^0(gr^p(K^•))` and `K^• ↦ H^0((forget F)K^•)` on `K(Fil^f(𝒜))`
  are homological ([Stacks, Tag 05S0] (1), (2), (3)).

## References

* [Stacks, Tag 05S0](https://stacks.math.columbia.edu/tag/05S0)
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits Opposite

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

namespace FiniteFilteredObject

/-- The filtered objects with finite filtration are closed under isomorphism. -/
instance : ObjectProperty.IsClosedUnderIsomorphisms
    fun F : FilteredObject 𝒜 ℤᵒᵖ => F.filtration.IsFinite where
  of_iso e _ := FilteredObject.isFinite_of_iso e

/-- The zero object of `Fil(𝒜)` has a finite filtration. -/
lemma isFinite_zero : (FilteredObject.zero : FilteredObject 𝒜 ℤᵒᵖ).filtration.IsFinite := by
  have h := (FilteredObject.isZero_iff _).1 (FilteredObject.isZero_zero (C := 𝒜) (I := ℤᵒᵖ))
  have h₀ := h.of_mono (FilteredObject.zero.filtration.ι.app (op 0))
  exact .of_exists ⟨0, IsZero.isIso h₀ h _⟩ ⟨0, h₀⟩

/-- The direct sum `A ⊕ B` of filtered objects with finite filtrations has a finite filtration. -/
lemma isFinite_biprodObj {A B : FilteredObject 𝒜 ℤᵒᵖ} (hA : A.filtration.IsFinite)
    (hB : B.filtration.IsFinite) : (FilteredObject.biprodObj A B).filtration.IsFinite := by
  obtain ⟨nA, hnA⟩ := hA.exists_isIso_ι
  obtain ⟨nB, hnB⟩ := hB.exists_isIso_ι
  obtain ⟨mA, hmA⟩ := hA.exists_isZero_obj
  obtain ⟨mB, hmB⟩ := hB.exists_isZero_obj
  have := A.filtration.isIso_ι_app_of_le (min_le_left nA nB) hnA
  have := B.filtration.isIso_ι_app_of_le (min_le_right nA nB) hnB
  refine .of_exists ⟨min nA nB, ?_⟩ ⟨max mA mB, ?_⟩
  · rw [FilteredObject.biprodObj_ι_app]
    exact isIso_of_mono_of_epi _
  · exact (biprod_isZero_iff _ _).2
      ⟨A.filtration.isZero_obj_of_le (le_max_left mA mB) hmA,
        B.filtration.isZero_obj_of_le (le_max_right mA mB) hmB⟩

/-- The filtered objects with finite filtration contain a zero object. -/
instance : ObjectProperty.ContainsZero
    fun F : FilteredObject 𝒜 ℤᵒᵖ => F.filtration.IsFinite :=
  ⟨FilteredObject.zero, FilteredObject.isZero_zero, isFinite_zero⟩

/-- The filtered objects with finite filtration are closed under binary products. -/
instance : ObjectProperty.IsClosedUnderBinaryProducts
    fun F : FilteredObject 𝒜 ℤᵒᵖ => F.filtration.IsFinite := by
  refine ⟨fun X ⟨L⟩ => ?_⟩
  have hc := (FilteredObject.biprodBiconeIsBilimit (L.diag.obj ⟨WalkingPair.left⟩)
    (L.diag.obj ⟨WalkingPair.right⟩)).isLimit
  have e : X ≅ FilteredObject.biprodObj (L.diag.obj ⟨WalkingPair.left⟩)
      (L.diag.obj ⟨WalkingPair.right⟩) :=
    IsLimit.conePointsIsoOfNatIso L.isLimit hc (diagramIsoPair L.diag)
  exact ObjectProperty.prop_of_iso (fun F : FilteredObject 𝒜 ℤᵒᵖ => F.filtration.IsFinite) e.symm
    (isFinite_biprodObj (L.prop_diag_obj _) (L.prop_diag_obj _))

/-- The category `Fil^f(𝒜)` of finite filtered objects has binary biproducts. -/
instance : HasBinaryBiproducts (FiniteFilteredObject 𝒜) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- The functor `gr : Fil^f(𝒜) ⥤ Gr(𝒜)`, `(A, F) ↦ (gr^p A)_p`. -/
noncomputable abbrev gr : FiniteFilteredObject 𝒜 ⥤ GradedObject ℤ 𝒜 :=
  ObjectProperty.ι _ ⋙ FilteredObject.grGraded

/-- The functor `gr^p : Fil^f(𝒜) ⥤ 𝒜`, `(A, F) ↦ F^p A / F^{p + 1} A`. -/
noncomputable abbrev grP (p : ℤ) : FiniteFilteredObject 𝒜 ⥤ 𝒜 :=
  ObjectProperty.ι _ ⋙ FilteredObject.gr p

/-- The functor `(forget F) : Fil^f(𝒜) ⥤ 𝒜`, `(A, F) ↦ A`. -/
abbrev forget : FiniteFilteredObject 𝒜 ⥤ 𝒜 :=
  ObjectProperty.ι _ ⋙ FilteredObject.forget

/-- **Stacks 05S0 (1).** The functor `K(Fil^f(𝒜)) ⥤ Gr(𝒜)`, `K^• ↦ H^0(gr(K^•))`, is
homological. -/
@[stacks 05S0 "(1)"]
theorem homologyFunctor_gr_isHomological :
    ((gr (𝒜 := 𝒜)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      HomotopyCategory.homologyFunctor (GradedObject ℤ 𝒜) (ComplexShape.up ℤ) 0).IsHomological :=
  inferInstance

/-- **Stacks 05S0 (2).** For every `p : ℤ`, the functor `K(Fil^f(𝒜)) ⥤ 𝒜`,
`K^• ↦ H^0(gr^p(K^•))`, is homological. -/
@[stacks 05S0 "(2)"]
theorem homologyFunctor_grP_isHomological (p : ℤ) :
    ((grP (𝒜 := 𝒜) p).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      HomotopyCategory.homologyFunctor 𝒜 (ComplexShape.up ℤ) 0).IsHomological :=
  inferInstance

/-- **Stacks 05S0 (3).** The functor `K(Fil^f(𝒜)) ⥤ 𝒜`, `K^• ↦ H^0((forget F)K^•)`, is
homological. -/
@[stacks 05S0 "(3)"]
theorem homologyFunctor_forget_isHomological :
    ((forget (𝒜 := 𝒜)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      HomotopyCategory.homologyFunctor 𝒜 (ComplexShape.up ℤ) 0).IsHomological :=
  inferInstance

end FiniteFilteredObject

end CategoryTheory
