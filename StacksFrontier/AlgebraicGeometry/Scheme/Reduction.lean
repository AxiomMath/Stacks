module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Thickenings

/-!
# The reduction of a scheme

The *reduction* `X_red` of a scheme `X` is the reduced induced closed subscheme structure on all of
`X`, that is the closed subscheme cut out by the nilradical ideal sheaf. It is reduced, and its
closed immersion into `X` is surjective, hence a thickening.

## Main definitions

* `AlgebraicGeometry.Scheme.reduction` is the reduction `X_red` of a scheme `X`.
* `AlgebraicGeometry.Scheme.reductionι` is the closed immersion `X_red ⟶ X`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.isThickening_subschemeι_iff`: a closed subscheme is a
  thickening of the ambient scheme exactly when its ideal sheaf is supported everywhere.
* `AlgebraicGeometry.Scheme.isReduced_reduction`: `X_red` is reduced.
* `AlgebraicGeometry.Scheme.range_reductionι` and
  `AlgebraicGeometry.Scheme.surjective_reductionι`: `X_red ⟶ X` is surjective on points.
* `AlgebraicGeometry.Scheme.isThickening_reductionι`: `X_red ⟶ X` is a thickening.

## References

* [Stacks Project, Tag 01J4](https://stacks.math.columbia.edu/tag/01J4)
* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The closed subscheme cut out by an ideal sheaf is a thickening of the ambient scheme exactly
when that ideal sheaf is supported everywhere. -/
theorem IdealSheafData.isThickening_subschemeι_iff {X : Scheme.{u}} (I : X.IdealSheafData) :
    Stacks.Thickenings.IsThickening I.subschemeι ↔ I.support = ⊤ := by
  have h : Function.Surjective I.subschemeι ↔ I.support = ⊤ := by
    rw [← Set.range_eq_univ, range_subschemeι]
    exact ⟨fun h ↦ SetLike.coe_injective (by simpa using h), fun h ↦ by rw [h]; simp⟩
  exact ⟨fun hI ↦ h.mp hI.2, fun hI ↦ ⟨inferInstance, h.mpr hI⟩⟩

variable (X : Scheme.{u})

/-- The **reduction** `X_red` of a scheme `X`: the closed subscheme cut out by the nilradical
ideal sheaf, that is the reduced induced closed subscheme structure on all of `X`. -/
@[stacks 01J4 "the reduction X_red of X", ega "I 5.1.3"]
noncomputable def reduction : Scheme.{u} :=
  X.nilradical.subscheme

/-- The canonical closed immersion `X_red ⟶ X` from the reduction of a scheme. -/
noncomputable def reductionι : X.reduction ⟶ X :=
  X.nilradical.subschemeι

/-- The morphism `X_red ⟶ X` from the reduction of a scheme is a closed immersion. -/
instance isClosedImmersion_reductionι : IsClosedImmersion X.reductionι :=
  inferInstanceAs (IsClosedImmersion X.nilradical.subschemeι)

/-- The reduction of a scheme is reduced. -/
@[ega "I 5.1.2" "partial"]
instance isReduced_reduction : IsReduced X.reduction :=
  inferInstanceAs (IsReduced (IdealSheafData.radical (⊥ : X.IdealSheafData)).subscheme)

/-- The image of the closed immersion `X_red ⟶ X` is all of `X`. -/
@[simp]
theorem range_reductionι : Set.range X.reductionι = Set.univ := by
  show Set.range X.nilradical.subschemeι = Set.univ
  rw [IdealSheafData.range_subschemeι, support_nilradical]
  simp

/-- The closed immersion `X_red ⟶ X` is surjective. -/
theorem surjective_reductionι : Function.Surjective X.reductionι :=
  Set.range_eq_univ.mp X.range_reductionι

/-- The closed immersion `X_red ⟶ X` from the reduction of a scheme is a thickening. -/
theorem isThickening_reductionι : Stacks.Thickenings.IsThickening X.reductionι :=
  (IdealSheafData.isThickening_subschemeι_iff X.nilradical).mpr (support_nilradical X)

end AlgebraicGeometry.Scheme

end
