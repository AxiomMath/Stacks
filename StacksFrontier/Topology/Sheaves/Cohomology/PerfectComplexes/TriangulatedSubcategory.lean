module

public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import StacksFrontier.CategoryTheory.Triangulated.Functor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Perfect objects form a triangulated subcategory

The perfect objects of the derived category of modules on a ringed space form a strictly full
triangulated subcategory.

## Main results

* `Stacks.Cohomology.PerfectTriangulatedSubcategory.isPerfect_zero`: a zero object is perfect.
* `Stacks.Cohomology.PerfectTriangulatedSubcategory.isTriangulated_isPerfect`: the perfect objects
  form a triangulated subcategory.

## Implementation notes

The space, ring and module universes all coincide, as they already must for Tag 08CR. Strict
fullness, that is closure under isomorphism, is already
`Stacks.Cohomology.PerfectComplexes.isClosedUnderIsomorphisms_isPerfect`, so no second copy appears
  here.

`CategoryTheory.ObjectProperty.IsTriangulated` asks for three things. A zero object is perfect
because the zero complex is, over the one-member cover by the whole space. Stability under
shifts is `Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift`, which already covers every
  integer. Closure under
distinguished triangles is the two-out-of-three property of Tag 08CR, in the form that the
second vertex is perfect when the other two are.

## References

* [Stacks Project, Tag 08CR](https://stacks.math.columbia.edu/tag/08CR)
* [Stacks Project, Tag 0FDG](https://stacks.math.columbia.edu/tag/0FDG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace StrictlyPerfect
open scoped ZeroObject

namespace Stacks.Cohomology.PerfectTriangulatedSubcategory

universe u d

variable {X : RingedSpace.{u, u}}

/-- A zero module is a direct summand of the finite free module of rank zero. -/
theorem isDirectSummandOfFiniteFree_of_isZero (M : OXMod.{u, u} X) (hM : IsZero M) :
    IsDirectSummandOfFiniteFree M :=
  ⟨0, ⟨⟨0, 0, (Functor.map_isZero _ hM).eq_of_src _ _⟩⟩⟩

/-- **The zero object of the derived category is perfect.** It is represented by the zero
complex, which over the one-member cover by the whole space receives the zero map from the zero
strictly perfect complex, an isomorphism between zero objects. -/
theorem isPerfect_zero [HasDerivedCategory.{d} (OXMod.{u, u} X)] :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (0 : DerivedCategory (OXMod.{u, u} X)) := by
  refine ⟨0, ?_, ⟨(DerivedCategory.Q (C := OXMod.{u, u} X)).mapZeroObject⟩⟩
  refine ⟨ULift.{u} Unit, (fun _ => ⊤), by simp, fun _ => ⟨0, ?_, ?_⟩⟩
  · refine ⟨?_, ?_⟩
    · apply Set.Finite.subset (s := (∅ : Set ℤ)) Set.finite_empty
      intro j hj
      exact hj ((HomologicalComplex.eval _ _ j).map_isZero (isZero_zero _))
    · intro j
      exact isDirectSummandOfFiniteFree_of_isZero _
        ((HomologicalComplex.eval _ _ j).map_isZero (isZero_zero _))
  · refine ⟨0, ?_⟩
    let F := (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules.{u} X
      ⊤).mapHomologicalComplex (ComplexShape.up ℤ)
    have : IsIso (0 : (0 : CochainComplex
        (OXMod.{u, u} (X.restrict (⊤ : Opens X.carrier).isOpenEmbedding)) ℤ) ⟶
        F.obj (0 : CochainComplex (OXMod.{u, u} X) ℤ)) :=
      (isIsoZero_iff_source_target_isZero _ _).2
        ⟨isZero_zero _, Functor.map_isZero _ (isZero_zero _)⟩
    infer_instance

/-- **Perfect derived objects form a triangulated subcategory.** It contains a zero object, is
stable under all shifts, and the two-out-of-three property of Tag 08CR supplies closure under
distinguished triangles. -/
@[sga "6 I 5.8.4" "special case"]
instance isTriangulated_isPerfect (X : RingedSpace.{u, u})
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] :
    ObjectProperty.IsTriangulated
      (Stacks.Cohomology.PerfectComplexes.IsPerfect : ObjectProperty (DerivedCategory (OXMod.{u, u}
        X))) where
  toContainsZero := ⟨⟨0, isZero_zero _, isPerfect_zero⟩⟩
  toIsStableUnderShift := ⟨fun n => ⟨fun _ hK =>
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift hK n⟩⟩
  toIsTriangulatedClosed₂ :=
    ObjectProperty.IsTriangulatedClosed₂.mk' (fun T hT h₁ h₃ =>
      Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₂_of_distinguished T hT h₁ h₃)

end Stacks.Cohomology.PerfectTriangulatedSubcategory

end
