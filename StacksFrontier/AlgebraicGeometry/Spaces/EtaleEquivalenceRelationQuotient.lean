module

public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafChartFromDiagonal

/-!
# The quotient of a scheme by an étale equivalence relation presents it

Let `B` be a big fppf site, let `S` be a scheme contained in it, let `U` be an object of the
big fppf site of `S` — *no* hypothesis on its underlying scheme — and let `s, t : R ⟶ U` be an
étale equivalence relation on `U` over `S`. Stacks 02WW asserts that the quotient sheaf `U/R`
is an algebraic space over `S` and that `U ⟶ U/R` is étale and surjective, so that
`(U, R, U ⟶ U/R)` is a presentation of `U/R` in the sense of Stacks 0263.

The algebraicity of `U/R` for an arbitrary `U` is
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_affineBase`, and the two properties
of the quotient map follow from it by Stacks 02WV. This file assembles the presentation those
three statements describe, which is the conclusion Stacks 02WW is quoted for.

## Main results

* `AlgebraicGeometry.Space.quotientPresentation_of_diagDescent`: the presentation of the
  quotient of an object of the site by an étale equivalence relation on it, conditional on
  effective descent along the covering sieves of the site at the monomorphisms locally of
  finite type.
* `AlgebraicGeometry.Space.quotientPresentation_of_affineBase`: the same presentation,
  conditional only on the affine-base body of that predicate, which is the form in which the
  hypothesis is cheapest to supply.
* `AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_relation_of_affineBase` and
  `AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_relation_of_diagDescent` record the
  algebraicity of the quotient in the spelling of the relation `s, t : R ⟶ U` that the
  presentation uses.

## Implementation notes

Nothing here asks the underlying scheme of `U` to be affine. The source reduces Stacks 02WW to
the affine case of Stacks 0265 by replacing `U` with a disjoint union of affine opens, using
that the quotient is unchanged under restriction along a surjective étale morphism
(Stacks 02VH) and that the quotient of a restriction to an open sits inside the quotient as an
open subspace (Stacks 02WU). That reduction is not needed in this library, because affineness
of `U` is not used anywhere in the chain that produces the chart of a quotient sheaf from the
representable diagonal:

* `AlgebraicGeometry.Space.relativelyRepresentable_diag_quotientSheaf` never used it;
* `AlgebraicGeometry.Space.exists_isPullback_quotientChart` records the base change of the
  chart along a lifted point as the relation pulled back along that lift, and the Cartesian
  square together with surjectivity, étaleness, local quasi-finiteness and local finite type
  of the projection are properties of the target map of the relation alone;
* the only property of that target map which needs `U` affine is separatedness, and
  separatedness is not among the hypotheses of
  `AlgebraicGeometry.Space.presheaf_quotientChart_of_relativelyRepresentable_diag`: it asks
  for a property which is stable under base change, Zariski local on the target and fppf
  descending, and surjectivity together with étaleness is such a property.

So the general case of Stacks 02WW costs exactly what the affine case of Stacks 0265 costs,
and the descent hypothesis is literally the same one; neither statement is weakened to make
this work. Consequently nothing here carries `@[stacks 02WW]` or `@[stacks 0263]`: the descent
hypothesis is undischarged, exactly as it is for Stacks 0265.

The relation is presented as a pair `s, t : R ⟶ U` of morphisms of objects of the site rather
than as a `Stacks.Groupoids.PreRelation` over an arbitrary `S`-scheme, because that is the
shape `AlgebraicGeometry.Space.Presentation` and Stacks 02WV are stated in. This loses no
generality: the relation scheme of an étale equivalence relation is an object of the site by
`Stacks.Groupoids.contains_left_of_isEtaleEquivalenceRelation`.

## References

* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 02WV](https://stacks.math.columbia.edu/tag/02WV)
* [Stacks Project, Tag 0263](https://stacks.math.columbia.edu/tag/0263)
* [Stacks Project, Tag 0265](https://stacks.math.columbia.edu/tag/0265)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open Stacks.Groupoids

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  {R U : BigFppfOver B S hS} (s t : R ⟶ U)
  [IsEtaleEquivalenceRelation (relation B S hS s t)]

/-! ### The presentation from effective descent at the monomorphisms of finite type -/

/-- **The algebraicity half of Stacks 02WW**, in the spelling of a relation given by a pair of
morphisms `s, t : R ⟶ U` of objects of the site, and conditional on effective descent along
the covering sieves at the monomorphisms locally of finite type.

The underlying scheme of `U` is arbitrary. This is
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_diagDescent` at the pre-relation
`AlgebraicGeometry.Space.relation`. It does **not** carry `@[stacks 02WW]`: the descent
hypothesis is undischarged. -/
theorem isAlgebraicSpace_quotientSheaf_relation_of_diagDescent
    (hdesc : IsEffectiveDescentAlongCoveringSieve B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)) :
    IsAlgebraicSpace B S hS
      (quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (relation B S hS s t)).obj :=
  isAlgebraicSpace_quotientSheaf_of_diagDescent B S hS U (relation B S hS s t) hdesc

/-- **Stacks 02WW, the presentation**, conditional on effective descent along the covering
sieves at the monomorphisms locally of finite type.

An étale equivalence relation `s, t : R ⟶ U` on an object of the big fppf site of `S` presents
its quotient sheaf: that sheaf is an algebraic space over `S`, the quotient map
`yoneda.obj U ⟶ U/R` is surjective and étale after every representable base change, and `R` is
the fibre product `U ×_{U/R} U`. The underlying scheme of `U` is arbitrary, which is the
generality of Stacks 02WW against the affine case of Stacks 0265.

The three data are supplied by Stacks 02WV, which needs nothing of the relation beyond the
quotient being an algebraic space. It does **not** carry `@[stacks 02WW]`: the descent
hypothesis is undischarged. -/
def quotientPresentation_of_diagDescent
    (hdesc : IsEffectiveDescentAlongCoveringSieve B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)) :
    Presentation B S hS
      (quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (relation B S hS s t)).obj
      (isAlgebraicSpace_quotientSheaf_relation_of_diagDescent B S hS s t hdesc) :=
  quotientPresentation B S hS s t
    (isAlgebraicSpace_quotientSheaf_relation_of_diagDescent B S hS s t hdesc)

/-! ### The presentation from the affine-base body alone

`H` below is the body of `AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` at the
monomorphisms locally of finite type with the single extra assumption that the base object is
affine, exactly as in
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_affineBase`. Nothing is asked of the
site's cutoff.
-/

section AffineBase

variable (H : ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
  Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
  Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
  ∀ ⦃a : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (T : Sieve a),
    IsAffine ((BigFppfOver.toScheme B S hS).obj a) →
    T ∈ BigFppfOver.topology B S hS a →
    (∀ ⦃b : BigFppfOver B S hS⦄ (q : b ⟶ a), T q →
      ((MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType).inverseImage
        (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f (yoneda.map q ≫ h))) →
    ((MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType).inverseImage
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h))

include H in
/-- **The algebraicity half of Stacks 02WW**, in the spelling of a relation given by a pair of
morphisms `s, t : R ⟶ U` of objects of the site, and conditional on the affine-base body `H`
alone. No cardinal hypothesis and no hypothesis on the site's cutoff is used, and the
underlying scheme of `U` is arbitrary.

It does **not** carry `@[stacks 02WW]`: the hypothesis `H` is undischarged. -/
theorem isAlgebraicSpace_quotientSheaf_relation_of_affineBase :
    IsAlgebraicSpace B S hS
      (quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (relation B S hS s t)).obj :=
  isAlgebraicSpace_quotientSheaf_of_affineBase B S hS U (relation B S hS s t) H

include H in
/-- **Stacks 02WW, the presentation**, conditional on the affine-base body `H` alone.

An étale equivalence relation on an object of the big fppf site of `S` whose underlying scheme
is arbitrary presents its quotient sheaf. This is
`AlgebraicGeometry.Space.quotientPresentation_of_diagDescent` with the descent hypothesis
reduced to its affine-base body by the theorem
`isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_locallyOfFiniteType_of_affineBase` of
`StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafChartFromDiagonal`, which is possible
because the property in question lies below the monomorphisms and the glueing step is then
paid for by `AlgebraicGeometry.Scheme.size_le_of_mono`.

It does **not** carry `@[stacks 02WW]`: the hypothesis `H` is undischarged. -/
def quotientPresentation_of_affineBase :
    Presentation B S hS
      (quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (relation B S hS s t)).obj
      (isAlgebraicSpace_quotientSheaf_relation_of_affineBase B S hS s t H) :=
  quotientPresentation B S hS s t
    (isAlgebraicSpace_quotientSheaf_relation_of_affineBase B S hS s t H)

end AffineBase

end AlgebraicGeometry.Space

end
