module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyReduced
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.EtaleAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage

/-!
# Geometric reducedness of algebraic spaces is étale local

Let `k` be a field. Geometric reducedness at a point of an algebraic space over `k` is
unchanged along a morphism which is étale at that point, and geometric reducedness of the whole
space is unchanged along a surjective étale morphism.

## Main results

* `AlgebraicGeometry.Space.isGeometricallyReducedAt_iff_of_isEtale`: the comparison along a
  morphism that is étale everywhere.
* `AlgebraicGeometry.Space.isGeometricallyReducedAt_iff_of_isEtaleAt` is Stacks 0E05 part (1)
  and `AlgebraicGeometry.Space.isGeometricallyReduced_iff_of_surjective_isEtale` is part (2).

## Implementation notes

The source argues with the identification `𝒪_{X, x̄} = 𝒪_{Y, ȳ}` of étale local rings along an
étale morphism. Here the comparison is made on scheme charts instead, which avoids having to
check that that identification is a `k`-algebra isomorphism: by Stacks 0DMR an algebraic space
is geometrically reduced at a point exactly when *some* étale scheme chart is geometrically
reduced at a point above it, and exactly when *every* one is. An étale scheme chart of the
source composed with an étale morphism is an étale scheme chart of the target over the image
point, so each of the two conditions in one space produces the other condition in the other
space. Étale charts above the point exist because an algebraic space has a surjective étale
atlas.

For part (1) étaleness at `x` gives an open subspace `U` of `X` containing `x` on which `f` is
étale. Both `U ⟶ X` and `U ⟶ Y` are then étale, so the comparison above applies to each, and
the two images of the point of `U` are `x` and `y`.

## References

* [Stacks Project, Tag 0E05](https://stacks.math.columbia.edu/tag/0E05)
* [Stacks Project, Tag 0DMR](https://stacks.math.columbia.edu/tag/0DMR)
* [Stacks Project, Tag 04RH](https://stacks.math.columbia.edu/tag/04RH)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))

/-- Geometric reducedness at a point is unchanged along an étale morphism of algebraic spaces
over a field: an étale scheme chart of the source above the point is, after composing with the
morphism, an étale scheme chart of the target above the image point, and the chart criteria of
Stacks 0DMR for the two spaces are matched by it. -/
theorem isGeometricallyReducedAt_iff_of_isEtale
    {W X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B (Spec (.of k)) hk W)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (g : W ⟶ X) (hg : IsEtale B (Spec (.of k)) hk g)
    (w : points B (Spec (.of k)) hk W) :
    IsGeometricallyReducedAt k B hk W hW w ↔
      IsGeometricallyReducedAt k B hk X hX (pointsMap B (Spec (.of k)) hk W g w) := by
  obtain ⟨U, a, hsurj, ha⟩ := hW.exists_atlas
  have ha' : IsEtale B (Spec (.of k)) hk a :=
    (isEtale_iff_presheaf_of_yoneda B (Spec (.of k)) hk a).mpr ha
  obtain ⟨z, hz⟩ :=
    (surjective_iff_surjective_pointsMap B (Spec (.of k)) hk W hW U a).mp hsurj w
  obtain ⟨p, rfl⟩ := Quot.exists_rep z
  have hag : IsEtale B (Spec (.of k)) hk (a ≫ g) := isEtale_comp B (Spec (.of k)) hk ha' hg
  have hpg : pointsMap B (Spec (.of k)) hk (yoneda.obj U) (a ≫ g)
      (p.class B (Spec (.of k)) hk (yoneda.obj U)) =
      pointsMap B (Spec (.of k)) hk W g w := by
    rw [← hz, pointsMap_comp]
    rfl
  constructor
  · intro h
    refine (isGeometricallyReducedAt_iff_exists_etaleChart k B hk X hX _).mpr
      ⟨U, a ≫ g, hag, p, hpg, ?_⟩
    exact (isGeometricallyReducedAt_iff_forall_etaleChart k B hk W hW w).mp h U a ha' p hz
  · intro h
    refine (isGeometricallyReducedAt_iff_exists_etaleChart k B hk W hW w).mpr
      ⟨U, a, ha', p, hz, ?_⟩
    exact (isGeometricallyReducedAt_iff_forall_etaleChart k B hk X hX _).mp h U (a ≫ g) hag p hpg

/-- **Stacks 0E05, part (1).** Let `f : X ⟶ Y` be a morphism of algebraic spaces over a field
`k` and let `x` be a point of `X` with image `y`. If `f` is étale at `x`, then `X` is
geometrically reduced at `x` if and only if `Y` is geometrically reduced at `y`. -/
@[stacks 0E05 "part (1)"]
theorem isGeometricallyReducedAt_iff_of_isEtaleAt
    {X Y : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hY : IsAlgebraicSpace B (Spec (.of k)) hk Y)
    (f : X ⟶ Y) (x : points B (Spec (.of k)) hk X)
    (hf : IsEtaleAt B (Spec (.of k)) hk f x) :
    IsGeometricallyReducedAt k B hk X hX x ↔
      IsGeometricallyReducedAt k B hk Y hY (pointsMap B (Spec (.of k)) hk X f x) := by
  obtain ⟨U, hU, x', hx', hUf⟩ := hf
  have hι : IsEtale B (Spec (.of k)) hk U.ι := isEtale_ι_of_isOpenSubspace hU
  have h₁ := isGeometricallyReducedAt_iff_of_isEtale k B hk hU.1 hX U.ι hι x'
  have h₂ := isGeometricallyReducedAt_iff_of_isEtale k B hk hU.1 hY (U.ι ≫ f) hUf x'
  rw [hx'] at h₁
  rw [pointsMap_comp, Function.comp_apply, hx'] at h₂
  exact h₁.symm.trans h₂

/-- **Stacks 0E05, part (2).** Let `f : X ⟶ Y` be a surjective étale morphism of algebraic
spaces over a field `k`. Then `X` is geometrically reduced if and only if `Y` is. -/
@[stacks 0E05 "part (2)"]
theorem isGeometricallyReduced_iff_of_surjective_isEtale
    {X Y : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hY : IsAlgebraicSpace B (Spec (.of k)) hk Y)
    (f : X ⟶ Y) (hf : IsEtale B (Spec (.of k)) hk f)
    (hs : IsSurjective B (Spec (.of k)) hk f) :
    IsGeometricallyReduced k B hk X hX ↔ IsGeometricallyReduced k B hk Y hY := by
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := hs y
    exact (isGeometricallyReducedAt_iff_of_isEtale k B hk hX hY f hf x).mp (h x)
  · intro h x
    exact (isGeometricallyReducedAt_iff_of_isEtale k B hk hX hY f hf x).mpr (h _)

end AlgebraicGeometry.Space

end
