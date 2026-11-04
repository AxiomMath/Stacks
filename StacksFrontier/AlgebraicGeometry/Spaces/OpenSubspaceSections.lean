module

public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceOfRepresentable

/-!
# Sections of an open subspace of a chart, and finiteness of a represented morphism

An open subspace of the algebraic space represented by an object `V` of the big fppf site over
`S` is cut out by an open subscheme of the representing scheme, by
`AlgebraicGeometry.Space.subspaceOfOpens_opensOfOpenSubspace`.  This file reads that
correspondence on *sections*: a morphism of the site into `V` is a section of the subspace cut
out by an open exactly when its underlying morphism of schemes takes every point into that
open.  That is the form in which an open subspace is used to produce an open subscheme closed
under given operations, since factoring a morphism through an open immersion is exactly a
pointwise condition on its image.

It also records the converse of `AlgebraicGeometry.Space.isFinite_yoneda_map`: a represented
morphism of algebraic spaces which is finite has a finite underlying morphism of schemes.

## Main results

* `AlgebraicGeometry.Space.mem_subspaceOfOpens_iff`: a morphism of the site is a section of
  `AlgebraicGeometry.Space.subspaceOfOpens` exactly when the underlying morphism of schemes
  lands pointwise in the open.
* `AlgebraicGeometry.Space.finite_of_isFinite_yoneda_map`: finiteness of a represented morphism
  of algebraic spaces descends to the underlying morphism of schemes.

## Implementation notes

`AlgebraicGeometry.Space.subspaceOfOpens` is defined as the subspace cut out by the set of
points lying over the open, and membership in such a subspace is, by
`AlgebraicGeometry.Space.mem_openSubspaceOfPoints_iff`, containment of the point set of the
section.  Translating that into a statement about scheme points is
`AlgebraicGeometry.Space.pointsToScheme_pointsMap_yoneda`, the naturality of the comparison of
Stacks 03BV, together with its surjectivity; the section of `yoneda.obj V` is identified with
the Yoneda image of the morphism it is by `CategoryTheory.yonedaEquiv_yoneda_map`.

Finiteness descends because finiteness of a morphism of algebraic spaces is literally the
affine-base-change pattern at Mathlib's `AlgebraicGeometry.IsFinite`
(`AlgebraicGeometry.Space.isFinite_iff_holdsOnAffineBaseChange`), that pattern passes to the
relatively representable form for a morphism of algebraic spaces by
`AlgebraicGeometry.Space.presheaf_of_holdsOnAffineBaseChange_of_isAlgebraicSpace` — finiteness
being Zariski local at the target — and the relatively representable form of a base-change
stable property of a represented morphism is that property of the underlying morphism of
schemes, by `AlgebraicGeometry.BigFppfOver.presheaf_inverseImage_yoneda_map_iff`.

## References

* [Stacks Project, Tag 03BV](https://stacks.math.columbia.edu/tag/03BV)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Finiteness of a represented morphism -/

/-- **Finiteness of a represented morphism of algebraic spaces descends to schemes.**  This is
the converse of `AlgebraicGeometry.Space.isFinite_yoneda_map`. -/
theorem finite_of_isFinite_yoneda_map {W V : BigFppfOver B S hS} (p : W ⟶ V)
    (h : IsFinite B S hS (yoneda.map p)) :
    _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map p) := by
  have hpre := presheaf_of_holdsOnAffineBaseChange_of_isAlgebraicSpace B S hS
    isZariskiLocalAtTarget_isFinite (isAlgebraicSpace_yoneda B S hS W)
    (isAlgebraicSpace_yoneda B S hS V) ((isFinite_iff_holdsOnAffineBaseChange _).1 h)
  exact (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
    (@_root_.AlgebraicGeometry.IsFinite.{u}) p).1 hpre

/-! ### Sections of the subspace cut out by an open -/

/-- **A morphism of the site is a section of the open subspace cut out by an open of the
representing scheme exactly when it lands pointwise in that open.** -/
theorem mem_subspaceOfOpens_iff (V : BigFppfOver B S hS)
    (Q : ((BigFppfOver.toScheme B S hS).obj V).Opens) {T : BigFppfOver B S hS} (x : T ⟶ V) :
    x ∈ (subspaceOfOpens B S hS V Q).obj (Opposite.op T) ↔
      ∀ y, ((BigFppfOver.toScheme B S hS).map x).base y ∈ Q := by
  have hx : (yonedaEquiv.symm x : yoneda.obj T ⟶ yoneda.obj V) = yoneda.map x :=
    yonedaEquiv.symm_apply_eq.2 (yonedaEquiv_yoneda_map x).symm
  rw [subspaceOfOpens, mem_openSubspaceOfPoints_iff, hx]
  constructor
  · intro h y
    obtain ⟨w, rfl⟩ := surjective_pointsToScheme B S hS T y
    have hmem := h ⟨w, rfl⟩
    rw [Set.mem_preimage, pointsToScheme_pointsMap_yoneda B S hS x w] at hmem
    exact hmem
  · rintro h z ⟨w, rfl⟩
    rw [Set.mem_preimage, pointsToScheme_pointsMap_yoneda B S hS x w]
    exact h _

/-- **Every open subspace of a chart is the subspace cut out by an open of the representing
scheme, read on sections**: a morphism of the site is a section of the open subspace exactly
when its underlying morphism of schemes lands pointwise in the attached open. -/
theorem mem_iff_of_isOpenSubspace (V : BigFppfOver B S hS) (A : Subfunctor (yoneda.obj V))
    (hA : IsOpenSubspace B S hS A) {T : BigFppfOver B S hS} (x : T ⟶ V) :
    x ∈ A.obj (Opposite.op T) ↔
      ∀ y, ((BigFppfOver.toScheme B S hS).map x).base y ∈
        opensOfOpenSubspace B S hS V A hA := by
  rw [← mem_subspaceOfOpens_iff B S hS V (opensOfOpenSubspace B S hS V A hA) x,
    subspaceOfOpens_opensOfOpenSubspace B S hS V A hA]

end AlgebraicGeometry.Space

end
