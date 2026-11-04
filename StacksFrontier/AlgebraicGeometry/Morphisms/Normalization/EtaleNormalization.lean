module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Normalization
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.UnibranchConnected
public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch

/-!
# An unramified relative normalization is finite étale

Let `f : Y ⟶ X` be a dominant quasi-compact quasi-separated morphism of integral schemes with `X`
normal, and let `f.normalization ⟶ X` be the relative normalization of `X` in `f`. The three
conditions "unramified", "étale" and "finite étale" on that morphism all agree.

Unramified implies étale because a normal scheme is geometrically unibranch and the normalization
is irreducible and dominates `X`, so the criterion for an unramified morphism from a connected
scheme over a geometrically unibranch base applies; the converse holds because an étale morphism
is smooth and unramified at every point. Étale implies finite étale because the morphism from a
relative normalization is integral by construction, so as soon as it is locally of finite type it
is finite.

## Main results

* `AlgebraicGeometry.unramified_normalization_iff_etale`: the morphism from the relative
  normalization of a normal integral scheme is unramified if and only if it is étale.
* `AlgebraicGeometry.etale_normalization_iff_finite_etale`: the morphism from the relative
  normalization is étale if and only if it is finite étale.

## Implementation notes

The source phrases the hypothesis as "`X` is unramified in `L`" for a finite extension `L` of the
function field of `X`, which says exactly that the normalization of `X` in `Spec L ⟶ X` is an
unramified morphism. Stating the equivalences for an arbitrary dominant morphism of integral
schemes avoids choosing a presentation of the function field and covers that case.
Quasi-compactness and quasi-separatedness are what the relative normalization construction
requires.

## References

* [Stacks Project, Tag 0BQK](https://stacks.math.columbia.edu/tag/0BQK)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The morphism from the relative normalization of a normal integral scheme in a dominant
morphism of integral schemes is unramified exactly when it is étale: the normalization is
irreducible and dominates the normal, hence geometrically unibranch, target. -/
@[stacks 0BQK "unramified iff étale", sga "1 I 9.11" "special case"]
theorem unramified_normalization_iff_etale
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsIntegral Y] [IsIntegral X] [IsNormal X]
    [QuasiCompact f] [QuasiSeparated f] [IsDominant f] :
    Unramified f.fromNormalization ↔ Etale f.fromNormalization := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : Unramified f.fromNormalization := h
    have : IsDominant (f.toNormalization ≫ f.fromNormalization) := by
      rw [Scheme.Hom.toNormalization_fromNormalization]
      infer_instance
    have : IsDominant f.fromNormalization := IsDominant.of_comp f.toNormalization _
    have hdom : ∃ Z : irreducibleComponents f.normalization,
        closure (f.fromNormalization '' (Z : Set f.normalization)) = Set.univ :=
      ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; simp⟩,
        by simpa only [Set.image_univ] using f.fromNormalization.denseRange.closure_range⟩
    exact etale_of_unramified_of_dominant_component f.fromNormalization
      isGeometricallyUnibranch_of_isNormal hdom
  · exact (unramified_iff f.fromNormalization).mpr fun x =>
      ((etaleAt_iff_smoothAt_and_unramifiedAt f.fromNormalization x).mp
        ((etale_iff_forall_etaleAt f.fromNormalization).mp h x)).2

/-- The morphism from a relative normalization is étale exactly when it is finite étale: it is
always integral, and an étale morphism is locally of finite type. -/
@[stacks 0BQK "étale iff finite étale"]
theorem etale_normalization_iff_finite_etale
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] :
    Etale f.fromNormalization ↔ (IsFinite f.fromNormalization ∧ Etale f.fromNormalization) := by
  refine ⟨fun h => ?_, And.right⟩
  have : Etale f.fromNormalization := h
  exact ⟨(IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f.fromNormalization).mpr
    ⟨inferInstance, inferInstance⟩, h⟩

end AlgebraicGeometry

end
