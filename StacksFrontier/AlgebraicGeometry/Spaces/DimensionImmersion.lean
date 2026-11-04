module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.LimitFibreDimensionBound.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback

/-!
# An immersion of algebraic spaces does not raise the dimension at a point

Let `f : F ⟶ G` be an immersion of algebraic spaces over a scheme `S` and let `x ∈ |F|`. Then
the dimension of `F` at `x` is at most the dimension of `G` at the image of `x`; in particular
this holds for a closed immersion. Here the dimension of an algebraic space at a point is the
local Krull dimension of an étale scheme chart at a point above it (Stacks 04N5).

## Main results

* `AlgebraicGeometry.Space.dimensionAtPoint_le_of_isImmersion`: the dimension at a point does
  not increase along an immersion of algebraic spaces.
* `AlgebraicGeometry.Space.dimensionAtPoint_le_of_isClosedImmersion`: its case of a closed
  immersion.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 04N5](https://stacks.math.columbia.edu/tag/04N5)
-/


@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- **An immersion of algebraic spaces does not raise the dimension at a point.** If
`f : F ⟶ G` is an immersion of algebraic spaces over `S` and `x ∈ |F|`, then
`dim_x(F) ≤ dim_{f(x)}(G)`. -/
theorem dimensionAtPoint_le_of_isImmersion (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (f : F ⟶ G) (hf : IsImmersion B S hS f) (x : points B S hS F) :
    dimensionAtPoint B S hS F hF x ≤
      dimensionAtPoint B S hS G hG (pointsMap B S hS F f x) := by
  classical
  obtain ⟨U, a, ha, p, hp⟩ :=
    exists_etale_chart_at_point B S hS G hG (pointsMap B S hS F f x)
  set R := hf.rep.pullback a with hR
  set j := hf.rep.snd a with hj
  have hsq : IsPullback (hf.rep.fst a) (yoneda.map j) f a := hf.rep.isPullback a
  have hci : AlgebraicGeometry.IsImmersion
      ((BigFppfOver.toScheme B S hS).map j) := hf.property_snd a
  have hEt : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (hf.rep.fst a) :=
    (isEtale_iff_presheaf_of_yoneda B S hS (hf.rep.fst a)).1
      (isEtale_of_isPullback_yoneda B S hS hsq.flip
        ((isEtale_iff_presheaf_of_yoneda B S hS a).2 ha))
  obtain ⟨w, hw₁, hw₂⟩ := exists_point_of_isPullback_presheaf B S hS hsq x
    (p.class B S hS (yoneda.obj U)) hp.symm
  obtain ⟨r, hr⟩ := Quot.exists_rep w
  rw [← hr] at hw₁ hw₂
  set q := FieldValuedPoint.map B S hS (yoneda.obj R) (yoneda.map j) r with hq
  have hqclass : q.class B S hS (yoneda.obj U) = p.class B S hS (yoneda.obj U) := hw₂.symm ▸ rfl
  rw [dimensionAtPoint_eq_of_etale_chart B S hS F hF x R (hf.rep.fst a) hEt r hw₁,
    dimensionAtPoint_eq_of_etale_chart B S hS G hG (pointsMap B S hS F f x) U a ha q
      (hqclass ▸ hp),
    hq, schemePoint_map_yoneda B S hS j r]
  exact Stacks.AlgebraicGeometry.LimitFibreDimensionBound.topologicalKrullDimAt_le_of_isInducing
    ((BigFppfOver.toScheme B S hS).map j).isEmbedding.isInducing
    (schemePoint B S hS R r)

/-- **A closed immersion of algebraic spaces does not raise the dimension at a point.** If
`f : F ⟶ G` is a closed immersion of algebraic spaces over `S` and `x ∈ |F|`, then
`dim_x(F) ≤ dim_{f(x)}(G)`. -/
theorem dimensionAtPoint_le_of_isClosedImmersion (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (f : F ⟶ G) (hf : IsClosedImmersion B S hS f) (x : points B S hS F) :
    dimensionAtPoint B S hS F hF x ≤
      dimensionAtPoint B S hS G hG (pointsMap B S hS F f x) :=
  dimensionAtPoint_le_of_isImmersion B S hS hF hG f
    (isImmersion_of_isClosedImmersion B S hS hf) x

end AlgebraicGeometry.Space

end
