module

public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.LargeFieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.LargeFieldSurjective

/-!
# Geometric points over large enough algebraically closed fields

Let `X` and `Y` be algebraic spaces over a scheme `S`.  Geometric points of `Y` cover the
point set `|Y|`, and the algebraically closed field may be taken as large as one pleases
relative to the cardinals `λ(X)` and `λ(Y)`; over such a field every point of a fibre of `X`,
and more generally every point of `X` above a given geometric point of `Y`, is represented by
a field-valued point; and surjectivity of a morphism `X → Y` may be tested on the
field-valued points over such fields.

## Main results

* `AlgebraicGeometry.Space.geometricPoints_large_enough` is the whole of Stacks 0488: its
  five parts, conjoined, under the sole hypotheses that `X` and `Y` are algebraic spaces
  over `S`.

## Implementation notes

The five parts are already available separately:
`AlgebraicGeometry.Space.exists_geometricRepresentative` (part 1),
`AlgebraicGeometry.Space.exists_geometricPoint_liesOver_of_lambdaCard` (part 2),
`AlgebraicGeometry.Space.surjective_fibrePointOfFieldPoint` (part 3),
`AlgebraicGeometry.Space.exists_lift_of_large_field` (part 4) and
`AlgebraicGeometry.Space.isSurjective_iff_surjective_app_of_lambdaCard` (part 5); the proof
here only assembles them.

The source writes `λ(X)` for the cardinal `λ` of a scheme carrying a surjective étale
morphism onto `X`.  Such an atlas exists by the algebraic-space hypothesis, and rather than
choosing one the clauses that mention `λ` quantify over every atlas, so each holds for the
source's chosen one whichever it is.  Likewise the morphism `X → Y` of parts (4) and (5) is
quantified over inside those clauses, which is where the source introduces it, so that
parts (1), (2) and (3) are not made to depend on the existence of a morphism.

The fibre `X_s = Spec κ(s) ×_S X` of part (3) is presented, as in
`AlgebraicGeometry.Space.surjective_fibrePointOfFieldPoint`, as an arbitrary cartesian
square over the terminal object `S` of the big fppf site, and `X(k) → |X_s|` is
`AlgebraicGeometry.Space.fibrePointOfFieldPoint`.  The target `|X| ×_{|Y|} Y(k)` of part (4)
is spelled out as the pairs consisting of a point of `|X|` and a `k`-valued point of `Y`
with the same image in `|Y|`.

## References

* [Stacks Project, Tag 0488](https://stacks.math.columbia.edu/tag/0488)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 0488.** Let `S` be a scheme and let `X`, `Y` be algebraic spaces over `S`.

1. As `k` ranges over all algebraically closed fields over `S` the geometric points
   `ȳ ∈ Y(k)` cover all of `|Y|`.
2. As `k` ranges over all algebraically closed fields over `S` with `|k| ≥ λ(Y)` and
   `|k| > λ(X)` the geometric points `ȳ ∈ Y(k)` cover all of `|Y|`.
3. For any geometric point `s̄ : Spec k → S` where `k` has cardinality `> λ(X)` the map
   `X(k) → |X_s|` is surjective.
4. For a morphism `X → Y` and any geometric point `s̄ : Spec k → S` where `k` has
   cardinality `> λ(X)`, the map `X(k) → |X| ×_{|Y|} Y(k)` is surjective.
5. A morphism `X → Y` is surjective if and only if `X(k) → Y(k)` is surjective for all
   algebraically closed fields `k` over `S` with `|k| > λ(X)` and `|k| ≥ λ(Y)`.

Following the source, `λ(X)` and `λ(Y)` are the cardinals `AlgebraicGeometry.Scheme.lambdaCard`
of schemes carrying a surjective étale morphism onto `X` and onto `Y`; the clauses quantify
over all such atlases. -/
@[stacks 0488]
theorem geometricPoints_large_enough
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) :
    -- (1) geometric points cover the point set
    (∀ y : points B S hS Y, ∃ p : GeometricPoint B S hS Y, p.image = y) ∧
    -- (2) geometric points over large enough fields cover the point set
    (∀ (UX UY : BigFppfOver B S hS) (fX : yoneda.obj UX ⟶ X) (fY : yoneda.obj UY ⟶ Y),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) fX →
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) fX →
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) fY →
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) fY →
      ∀ y : points B S hS Y, ∃ p : GeometricPoint B S hS Y, p.LiesOver y ∧
        ((BigFppfOver.toScheme B S hS).obj UY).lambdaCard ≤ Cardinal.mk p.val.carrier ∧
        ((BigFppfOver.toScheme B S hS).obj UX).lambdaCard < Cardinal.mk p.val.carrier) ∧
    -- (3) `X(k) → |X_s|` is surjective
    (∀ (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ X),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f →
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f →
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (hk : B.Contains (Spec (.of k)))
        (b : Spec (.of k) ⟶ S),
        ((BigFppfOver.toScheme B S hS).obj U).lambdaCard < Cardinal.mk k →
      ∀ (s : S) (hs : ∀ t, b t = s) (Xs : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
        (pr : Xs ⟶ X) (pr' : Xs ⟶ yoneda.obj (residueSiteObject B S hS s))
        (hpb : IsPullback pr pr' (toBaseSiteMap B S hS X)
          (yoneda.map (toBaseSiteObject B S hS (residueSiteObject B S hS s)))),
        Function.Surjective (fibrePointOfFieldPoint B S hS hk b s hs pr pr' hpb)) ∧
    -- (4) `X(k) → |X| ×_{|Y|} Y(k)` is surjective
    (∀ (a : X ⟶ Y) (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ X),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f →
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f →
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (hk : B.Contains (Spec (.of k)))
        (b : Spec (.of k) ⟶ S),
        ((BigFppfOver.toScheme B S hS).obj U).lambdaCard < Cardinal.mk k →
      ∀ (x : points B S hS X)
        (y : Y.obj (Opposite.op (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)))),
        pointsMap B S hS X a x =
            (⟨k, hk, b, y⟩ : FieldValuedPoint B S hS Y).class B S hS Y →
        ∃ z : X.obj (Opposite.op (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS))),
          a.app (Opposite.op (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS))) z = y ∧
          (⟨k, hk, b, z⟩ : FieldValuedPoint B S hS X).class B S hS X = x) ∧
    -- (5) surjectivity is tested on the field-valued points over large enough fields
    (∀ (a : X ⟶ Y) (UX UY : BigFppfOver B S hS)
        (fX : yoneda.obj UX ⟶ X) (fY : yoneda.obj UY ⟶ Y),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) fX →
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) fX →
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) fY →
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) fY →
      (IsSurjective B S hS a ↔
        ∀ (k : Type u) [Field k] [IsAlgClosed k] (hk : B.Contains (Spec (.of k)))
          (b : Spec (.of k) ⟶ S),
          ((BigFppfOver.toScheme B S hS).obj UX).lambdaCard < Cardinal.mk k →
          ((BigFppfOver.toScheme B S hS).obj UY).lambdaCard ≤ Cardinal.mk k →
          Function.Surjective
            (a.app (Opposite.op (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)))))) :=
  ⟨fun y => exists_geometricRepresentative B S hS Y y,
   fun UX UY fX fY hXs hXe hYs hYe y =>
     exists_geometricPoint_liesOver_of_lambdaCard B S hS X Y hX hY UX UY fX fY
       hXs hXe hYs hYe y,
   fun U f hfs hfe k _ _ hk b hlarge s hs _Xs pr pr' hpb =>
     surjective_fibrePointOfFieldPoint B S hS hX U f hfs hfe k hk b hlarge s hs pr pr' hpb,
   fun a U f hfs hfe k _ _ hk b hlarge x y hxy =>
     exists_lift_of_large_field B S hS hX hY a U f hfs hfe k hk b hlarge x y hxy,
   fun a UX UY fX fY hXs hXe hYs hYe =>
     isSurjective_iff_surjective_app_of_lambdaCard B S hS hX hY a UX UY fX fY
       hXs hXe hYs hYe⟩

end AlgebraicGeometry.Space

end
