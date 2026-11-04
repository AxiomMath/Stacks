module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingDimension

/-!
# The dimension of an algebraic space and its local rings

The dimension of an algebraic space is the supremum, over its points, of the Krull dimensions
of its local rings.

## Main results

* `AlgebraicGeometry.Space.dimension_eq_iSup_localRingDimension` is that equality.
* `AlgebraicGeometry.Space.iSup_dimensionAtPoint_eq_iSup_localRingDimension` is the same
  equality with the dimension of the algebraic space written out as the supremum, over the
  points, of the dimension at the point.

## Implementation notes

The source lists three quantities. Quantity (1), the dimension of the algebraic space, and
quantity (3), the supremum over `x ∈ |X|` of `dim_x(X)`, are the same by Definition 04N6,
which is how `AlgebraicGeometry.Space.dimension` is defined here; so the two results above,
equating each of them with quantity (2), are the three equalities of the source.

The dimension of an algebraic space is the supremum of its dimensions at points (Tag 04N6),
and both the dimension at a point (Tag 04N5) and the dimension of the local ring at a point
(Tag 04NA) are computed on an étale scheme chart. Fixing one étale atlas `a : yoneda.obj U ⟶ F`
turns each supremum over the points of `F` into a supremum over the points of the scheme
underlying `U`: the map on points of the atlas is surjective (Tag 03H5) and the points of a
represented presheaf are the points of the representing scheme (Tag 03BX). Both resulting
suprema over the scheme are the dimension of that scheme, by the two descriptions of the
dimension of a scheme in Tag 04MU.

Everything is computed in `WithBot ℕ∞`, so an algebraic space with no points has dimension
`⊥` on both sides.

## References

* [Stacks Project, Tag 0BAN](https://stacks.math.columbia.edu/tag/0BAN)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 0BAN, quantities (1) and (2).** The dimension of an algebraic space is the
supremum of the Krull dimensions of its local rings. -/
@[stacks 0BAN "the dimension of the space is the supremum over its local rings"]
theorem dimension_eq_iSup_localRingDimension (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    dimension B S hS F hF =
      ⨆ x : points B S hS F, (localRingDimension B S hS x : WithBot ℕ∞) := by
  obtain ⟨U, a, hsurj, ha⟩ := hF.exists_atlas
  have hsurjPoints : Function.Surjective (pointsMap B S hS (yoneda.obj U) a) :=
    (surjective_iff_surjective_pointsMap B S hS F hF U a).mp hsurj
  -- Both suprema over `|F|` are computed on the chart `U`, where they become suprema over the
  -- points of the scheme underlying `U`.
  have key (φ : points B S hS F → WithBot ℕ∞)
      (ψ : (BigFppfOver.toScheme B S hS).obj U → WithBot ℕ∞)
      (hcompat : ∀ y : points B S hS (yoneda.obj U), ψ (pointsToScheme B S hS U y) =
        φ (pointsMap B S hS (yoneda.obj U) a y)) :
      (⨆ x : points B S hS F, φ x) =
        ⨆ u : (BigFppfOver.toScheme B S hS).obj U, ψ u :=
    (hsurjPoints.iSup_congr _ fun _ ↦ rfl).symm.trans
      ((surjective_pointsToScheme B S hS U).iSup_congr _ hcompat)
  have hdim : dimension B S hS F hF =
      topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj U) := by
    rw [dimension, key (dimensionAtPoint B S hS F hF)
      (topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U))
      fun y ↦ Quot.inductionOn y fun q ↦
        (dimensionAtPoint_eq_of_etale_chart B S hS F hF _ U a ha q rfl).symm]
    simpa only [topologicalKrullDimAt_eq_localKrullDim] using
      (topologicalKrullDim_eq_iSup_localKrullDim
        ((BigFppfOver.toScheme B S hS).obj U)).symm
  have hlocal : (⨆ x : points B S hS F, (localRingDimension B S hS x : WithBot ℕ∞)) =
      topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj U) := by
    rw [key (fun x ↦ (localRingDimension B S hS x : WithBot ℕ∞))
      (fun u ↦ ringKrullDim (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk u))
      fun y ↦ (localRingDimension_eq_of_chartPoint B S hS hF U a ha _ _
        (chartPoint_pointsToScheme B S hS U a y)).symm]
    exact (topologicalKrullDim_eq_iSup_krullDimOfRing_stalk _).symm
  rw [hdim, hlocal]

/-- **Stacks 0BAN, quantities (3) and (2).** The supremum, over the points `x` of an algebraic
space, of its dimension `dim_x(X)` at `x` is the supremum of the Krull dimensions of its local
rings. By Definition 04N6 the left-hand side is the dimension of the algebraic space, so
together with `AlgebraicGeometry.Space.dimension_eq_iSup_localRingDimension` this is the
equality of all three quantities of the source. -/
@[stacks 0BAN "the supremum over the points of the dimension at the point"]
theorem iSup_dimensionAtPoint_eq_iSup_localRingDimension (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    (⨆ x : points B S hS F, dimensionAtPoint B S hS F hF x) =
      ⨆ x : points B S hS F, (localRingDimension B S hS x : WithBot ℕ∞) :=
  dimension_eq_iSup_localRingDimension B S hS F hF

end AlgebraicGeometry.Space

end
