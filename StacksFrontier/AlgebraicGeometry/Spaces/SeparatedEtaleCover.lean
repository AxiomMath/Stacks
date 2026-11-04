module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Every algebraic space is covered by a separated algebraic space

Every algebraic space over a scheme `S` is the target of a morphism which is surjective and
étale and whose source is an algebraic space separated over `S`.

This is the step which the Stacks Project asserts without a reference in the proof of the
fullness half of Tag 05ZH — "let `a' : V'' ⟶ V'` be a surjective étale morphism such that
`V''` is a separated algebraic space" — and which licenses the reduction, there, to the case
of a separated space. The two statements below are that assertion.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.IsAlgebraicSpace.exists_isSeparatedOver_etale_surjective_cover`: a
  presheaf which is an algebraic space over `S` admits a surjective étale morphism from an
  algebraic space separated over `S`.
* `AlgebraicGeometry.Space.exists_isSeparatedOver_etale_surjective_cover`: the same statement
  for an object of the category of algebraic spaces over `S`, with the cover a morphism of
  that category.

## Implementation notes

Nothing is proved here that the library did not already carry; the content is the assembly of
four existing results, and the point of the assembly is that the separatedness is delivered in
the space-level predicate `AlgebraicGeometry.Space.IsSeparatedOver` rather than as
separatedness of an underlying scheme, and the covering morphism in the space-level predicates
`AlgebraicGeometry.Space.IsEtale` of Tag 03FR and `AlgebraicGeometry.Space.IsSurjective` of
Tag 03ME rather than in the relatively representable properties of Tag 025V.

The cover itself is the chart of Tag 03FX. By
`AlgebraicGeometry.IsAlgebraicSpace.exists_etale_surjective_isSeparated_cover` the chart may
be taken to have separated underlying scheme, that being the chart of Tag 03FX whose source is
a disjoint union of affine schemes. An object of the site whose underlying scheme is separated
represents a presheaf separated over `S`, by
`AlgebraicGeometry.Space.isSeparatedOver_yoneda_obj`; the represented presheaf is an algebraic
space by Tag 025Z, `AlgebraicGeometry.isAlgebraicSpace_yoneda`; and the two relatively
representable properties of the chart become the space-level ones by
`AlgebraicGeometry.Space.isEtale_iff_presheaf_of_yoneda` and
`AlgebraicGeometry.Space.isSurjective_of_presheafSurjective`.

Note that the separatedness obtained is over `S` and not merely relative to the space being
covered: the underlying scheme of the chart is absolutely separated, so the chart is separated
over any base.

A consumer which needs the cover inside the spaces-étale site of a space `Y`, that is a cover
of an object `p : X ⟶ Y` of that site by another object of it, composes the cover `a` with `p`
and uses `AlgebraicGeometry.Space.isEtale_comp` to see that `a ≫ p` is again étale.

## References

* [Stacks Project, Tag 025V](https://stacks.math.columbia.edu/tag/025V)
* [Stacks Project, Tag 025Z](https://stacks.math.columbia.edu/tag/025Z)
* [Stacks Project, Tag 02X5](https://stacks.math.columbia.edu/tag/02X5)
* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Every algebraic space is covered by a separated algebraic space.** An algebraic space
over `S` admits a morphism from an algebraic space separated over `S` which is surjective, Tag
03ME, and étale, Tag 03FR.

The cover is the affine atlas of Tag 03FX: its source is a disjoint union of affine schemes,
which is a separated scheme and therefore represents an algebraic space separated over `S`.

This is the assertion made without a reference in the proof of the fullness half of Tag
05ZH. -/
theorem IsAlgebraicSpace.exists_isSeparatedOver_etale_surjective_cover
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    ∃ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (a : V ⟶ F),
      IsAlgebraicSpace B S hS V ∧
      Space.IsSeparatedOver B S hS V ∧
      Space.IsEtale B S hS a ∧
      Space.IsSurjective B S hS a := by
  obtain ⟨U, f, hUsep, hfS, hfE⟩ :=
    IsAlgebraicSpace.exists_etale_surjective_isSeparated_cover B S hS F hF
  exact ⟨yoneda.obj U, f, isAlgebraicSpace_yoneda B S hS U,
    Space.isSeparatedOver_yoneda_obj B S hS U hUsep,
    (Space.isEtale_iff_presheaf_of_yoneda B S hS f).2 hfE,
    Space.isSurjective_of_presheafSurjective B S hS f hfS⟩

/-- **Every algebraic space is covered by a separated algebraic space**, in the category of
algebraic spaces over `S`: every object of that category is the target of a morphism of it
which is surjective and étale and whose source is separated over `S`.

`AlgebraicGeometry.IsAlgebraicSpace.exists_isSeparatedOver_etale_surjective_cover` is the same
statement for a presheaf carrying the algebraic space property as a hypothesis. -/
theorem Space.exists_isSeparatedOver_etale_surjective_cover (X : AlgebraicSpaces B S hS) :
    ∃ (V : AlgebraicSpaces B S hS) (a : V ⟶ X),
      Space.IsSeparatedOver B S hS V.1 ∧
      Space.IsEtale B S hS a.hom ∧
      Space.IsSurjective B S hS a.hom := by
  obtain ⟨V, a, hV, hVsep, haE, haS⟩ :=
    IsAlgebraicSpace.exists_isSeparatedOver_etale_surjective_cover B S hS X.1 X.2
  exact ⟨⟨V, hV⟩, ObjectProperty.homMk a, hVsep, haE, haS⟩

end AlgebraicGeometry

end
