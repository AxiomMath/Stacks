module

public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence

/-!
# Morphisms into the open subspace cut out by a set of points

Let `W` be a set of points of an algebraic space `X`. A morphism `f : Y ⟶ X` factors through
the subfunctor `AlgebraicGeometry.Space.openSubspaceOfPoints` cut out by `W` exactly when `f`
maps every point of `Y` into `W`.

## Main results

* `AlgebraicGeometry.Space.exists_lift_openSubspaceOfPoints_iff`: the factorization criterion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism of presheaves factors through the subfunctor cut out by a set of points `W`
exactly when it maps every point into `W`.** -/
theorem exists_lift_openSubspaceOfPoints_iff {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (W : Set (points B S hS F)) (f : G ⟶ F) :
    (∃ g : G ⟶ (openSubspaceOfPoints B S hS F W).toFunctor,
        g ≫ (openSubspaceOfPoints B S hS F W).ι = f) ↔
      ∀ y : points B S hS G, pointsMap B S hS G f y ∈ W := by
  constructor
  · rintro ⟨g, rfl⟩ y
    rw [pointsMap_comp, Function.comp_apply]
    have h : pointsMap B S hS _ (openSubspaceOfPoints B S hS F W).ι (pointsMap B S hS G g y) ∈
        Set.range (pointsMap B S hS _ (openSubspaceOfPoints B S hS F W).ι) := ⟨_, rfl⟩
    rwa [range_pointsMap_ι_openSubspaceOfPoints B S hS W] at h
  · intro h
    refine ⟨Subfunctor.lift f ?_, Subfunctor.lift_ι _ _⟩
    rintro T _ ⟨s, rfl⟩ x ⟨w, rfl⟩
    have : yonedaEquiv.symm (f.app T s) = yonedaEquiv.symm s ≫ f :=
      (yonedaEquiv_symm_naturality_right _ f s).symm
    rw [this, pointsMap_comp, Function.comp_apply]
    exact h _

end AlgebraicGeometry.Space

end
