module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Restriction
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraicGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafChartFromDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictedQuotientOpenImmersion
public import StacksFrontier.CategoryTheory.Sites.Representable.CoproductYonedaDesc

/-!
# The quotient of a scheme by an étale equivalence relation

Let `S` be a scheme, let `U` and `R` be objects of the big fppf site of `S`, and let
`s, t : R ⟶ U` be a pair of morphisms whose associated pre-relation on `U ×_S U` is an étale
equivalence relation. Stacks 02WW asserts that the quotient sheaf `U/R` is an algebraic space
over `S` and that `(U, R, U ⟶ U/R)` is a presentation of it. This file proves that, for an
arbitrary `U` — the affine case being Stacks 0265 — conditional on one effective-descent
hypothesis. That hypothesis is itself a theorem of this development, so the results below are
discharged outright in
`StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional`, which is where
`@[stacks 02WW]` sits.

The algebraic-space property itself is
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_relation_of_diagDescent`, proved by
glueing the affine pieces; this file draws the remaining three conclusions of the source from
it.

## Main results

* `AlgebraicGeometry.Space.quotientMap_surjective_of_coveringSieveDescent`,
  `AlgebraicGeometry.Space.quotientMap_etale_of_coveringSieveDescent` and
  `AlgebraicGeometry.Space.quotientMap_isPullback_of_coveringSieveDescent`: the canonical map
  `U ⟶ U/R` is surjective and étale after every representable base change, and the relation
  is its kernel pair.
* `AlgebraicGeometry.Space.quotientPresentation_of_coveringSieveDescent`: the resulting
  presentation of `U/R`.

## Implementation notes

**The surviving hypothesis, and why nothing here is tagged.** Every result in this file
carries

```
IsEffectiveDescentAlongCoveringSieve B S hS
  (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)
```

effective descent of monomorphisms locally of finite type along the covering sieves of the big
fppf site of `S`. It enters only through
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_relation_of_diagDescent`, which is where
the three conclusions of Stacks 0265 are glued over the affine opens of `U`.

The hypothesis is *not* the standing open assumption of
`StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveDescent`, which is taken at the property of
Stacks 02W8 and is strictly different: the predicate mentions its property both in its
hypothesis and in its conclusion, so it is monotone in neither direction and neither instance
implies the other. The smaller property used here lies below the monomorphisms, where
`AlgebraicGeometry.Scheme.size_le_of_mono` pays for the affine-to-arbitrary passage, and so it
is **proved outright** by
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft`. Nothing
here carries `@[stacks 02WW]` all the same, because these statements are the conditional ones;
the tag sits on the discharged forms in
`StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional`.

## References

* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open Stacks.Groupoids

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
variable {R U : BigFppfOver B S hS} (s t : R ⟶ U)

/-- **Stacks 02WW, surjectivity of the quotient map**, conditional on effective descent along
the covering sieves of the big fppf site of `S` at the monomorphisms locally of finite type and
on nothing else. It does **not** carry `@[stacks 02WW]`: the discharged form is
`AlgebraicGeometry.Space.quotientMap_surjective_unconditional`. -/
theorem quotientMap_surjective_of_coveringSieveDescent
    [IsEtaleEquivalenceRelation (relation B S hS s t)]
    (hdesc : IsEffectiveDescentAlongCoveringSieve B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (quotientMap B S hS s t) :=
  quotientMap_surjective B S hS s t
    (relativelyRepresentable_quotientMap_of_isAlgebraicSpace B S hS s t
      (isAlgebraicSpace_quotientSheaf_relation_of_diagDescent B S hS s t hdesc))

/-- **Stacks 02WW, étaleness of the quotient map**, conditional on effective descent along the
covering sieves of the big fppf site of `S` at the monomorphisms locally of finite type and on
nothing else. It does **not** carry `@[stacks 02WW]`: the discharged form is
`AlgebraicGeometry.Space.quotientMap_etale_unconditional`. -/
theorem quotientMap_etale_of_coveringSieveDescent
    [IsEtaleEquivalenceRelation (relation B S hS s t)]
    (hdesc : IsEffectiveDescentAlongCoveringSieve B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (quotientMap B S hS s t) :=
  quotientMap_etale B S hS s t
    (relativelyRepresentable_quotientMap_of_isAlgebraicSpace B S hS s t
      (isAlgebraicSpace_quotientSheaf_relation_of_diagDescent B S hS s t hdesc))

/-- **Stacks 02WW, the kernel pair.** The relation is the fibre product `U ×_{U/R} U`. It does
**not** carry `@[stacks 02WW]`: the kernel-pair assertion is Stacks 02WV, whose tag sits on
`AlgebraicGeometry.Space.quotientMap_isPullback`.

The effective-descent hypothesis is *not used*: `AlgebraicGeometry.Space.quotientMap_isPullback`
assumes nothing about the quotient, so the kernel-pair assertion of Stacks 02WW is already
unconditional. The hypothesis is retained so that this result is stated uniformly with its two
siblings above and with its consumers. -/
theorem quotientMap_isPullback_of_coveringSieveDescent
    [IsEtaleEquivalenceRelation (relation B S hS s t)]
    (_hdesc : IsEffectiveDescentAlongCoveringSieve B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)) :
    IsPullback (yoneda.map t) (yoneda.map s)
      (quotientMap B S hS s t) (quotientMap B S hS s t) :=
  quotientMap_isPullback B S hS s t

/-- **Stacks 02WW, the presentation.** An étale equivalence relation presents its quotient
sheaf, conditional on effective descent along the covering sieves of the big fppf site of `S`
at the monomorphisms locally of finite type and on nothing else. It does **not** carry
`@[stacks 02WW]`: the discharged form is
`AlgebraicGeometry.Space.quotientPresentation_unconditional`. -/
noncomputable def quotientPresentation_of_coveringSieveDescent
    [IsEtaleEquivalenceRelation (relation B S hS s t)]
    (hdesc : IsEffectiveDescentAlongCoveringSieve B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)) :
    Presentation B S hS _
      (isAlgebraicSpace_quotientSheaf_relation_of_diagDescent B S hS s t hdesc) :=
  quotientPresentation B S hS s t
    (isAlgebraicSpace_quotientSheaf_relation_of_diagDescent B S hS s t hdesc)

end AlgebraicGeometry.Space

end
