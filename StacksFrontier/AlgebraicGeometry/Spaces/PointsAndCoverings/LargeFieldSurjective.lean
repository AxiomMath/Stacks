module

public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.LargeFieldCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.LargeFieldLift

/-!
# Surjectivity tested on points over large algebraically closed fields

A morphism `X → Y` of algebraic spaces over a scheme `S` is surjective if and only if the
induced map `X(k) → Y(k)` is surjective for every algebraically closed field `k` over `S`
whose cardinality exceeds `λ(X)` and is at least `λ(Y)`.

## Main results

* `AlgebraicGeometry.Space.isSurjective_iff_surjective_app_of_lambdaCard` is Stacks 0488
  part (5).

## Implementation notes

Surjectivity of a morphism of algebraic spaces is `AlgebraicGeometry.Space.IsSurjective` of
Tag 03ME, that is surjectivity of the induced map on the point sets of Tag 03BU.

One direction is part (4), `AlgebraicGeometry.Space.exists_lift_of_large_field`: a `k`-valued
point of `Y` has an image in `|Y|`, surjectivity produces a point of `|X|` above it, and
part (4) lifts the pair to a `k`-valued point of `X`. The other direction is part (2),
`AlgebraicGeometry.Space.exists_geometricPoint_liesOver_of_lambdaCard`: a point of `|Y|` is
represented by a geometric point over a field satisfying the two cardinality bounds, and the
`k`-valued point of `X` over it represents a point of `|X|` above the given one.

## References

* [Stacks Project, Tag 0488](https://stacks.math.columbia.edu/tag/0488)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 0488, part (5).** A morphism `a : X ⟶ Y` of algebraic spaces over `S` is
surjective if and only if, for every algebraically closed field `k` over `S` with
`|k| > λ(X)` and `|k| ≥ λ(Y)`, the map `X(k) → Y(k)` is surjective.

Following the source, `λ(X)` and `λ(Y)` are read off from chosen scheme atlases `UX → X` and
`UY → Y`, carried along as explicit parameters. -/
theorem isSurjective_iff_surjective_app_of_lambdaCard
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (a : X ⟶ Y)
    (UX UY : BigFppfOver B S hS)
    (fX : yoneda.obj UX ⟶ X) (fY : yoneda.obj UY ⟶ Y)
    (hfX_surjective : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) fX)
    (hfX_etale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) fX)
    (hfY_surjective : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) fY)
    (hfY_etale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) fY) :
    IsSurjective B S hS a ↔
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (hk : B.Contains (Spec (.of k)))
        (b : Spec (.of k) ⟶ S),
        ((BigFppfOver.toScheme B S hS).obj UX).lambdaCard < Cardinal.mk k →
        ((BigFppfOver.toScheme B S hS).obj UY).lambdaCard ≤ Cardinal.mk k →
        Function.Surjective
          (a.app (Opposite.op (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)))) := by
  constructor
  · intro hsurj k _ _ hk b hlx _ ybar
    obtain ⟨x, hx⟩ := hsurj ((⟨k, hk, b, ybar⟩ : FieldValuedPoint B S hS Y).class B S hS Y)
    obtain ⟨z, hz, -⟩ :=
      exists_lift_of_large_field B S hS hX hY a UX fX hfX_surjective hfX_etale k hk b hlx x
        ybar hx
    exact ⟨z, hz⟩
  · intro h y
    obtain ⟨q, hq, hqY, hqX⟩ :=
      exists_geometricPoint_liesOver_of_lambdaCard B S hS X Y hX hY UX UY fX fY
        hfX_surjective hfX_etale hfY_surjective hfY_etale y
    have : IsAlgClosed q.val.carrier := q.property
    obtain ⟨z, hz⟩ :=
      h q.val.carrier q.val.contained q.val.toBase hqX hqY q.val.value
    refine ⟨(⟨q.val.carrier, q.val.contained, q.val.toBase, z⟩ :
      FieldValuedPoint B S hS X).class B S hS X, ?_⟩
    rw [pointsMap_class]
    exact (congrArg (fun w => FieldValuedPoint.class B S hS Y
      (⟨q.val.carrier, q.val.contained, q.val.toBase, w⟩ : FieldValuedPoint B S hS Y)) hz).trans hq

end AlgebraicGeometry.Space

end
