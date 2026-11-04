module

public import StacksFrontier.RingTheory.Seminormalization.SeminormalizationInitial.AffineChartGluing
public import StacksFrontier.RingTheory.Seminormalization.SeminormalizationInitial.GluedFactorization
public import StacksFrontier.RingTheory.Seminormalization.SeminormalizationInitial.Initiality
public import StacksFrontier.RingTheory.Seminormalization.SeminormalizationInitial.OpenRestriction

/-!
# The initial subintegral factorization of a dominant morphism

A quasi-compact, quasi-separated, dominant morphism of schemes admits an initial factorization
through a universal homeomorphism which induces isomorphisms on all residue fields. This is the
relative seminormalization of the target in the source.

## Main definitions

* `AlgebraicGeometry.seminormalizationFactorization` is a chosen initial subintegral
  factorization of a quasi-compact, quasi-separated, dominant morphism.
* `AlgebraicGeometry.seminormalizationFactorizationIsInitial` exhibits it as an initial object.

## Main results

* `AlgebraicGeometry.exists_initial_subintegralFactorization` states that the category of
  subintegral factorizations has an initial object.
* `AlgebraicGeometry.existsUnique_isPullback_seminormalizationFactorization_restrict` states
  that formation of that factorization commutes with base change to an open subscheme of the
  target: the intermediate scheme of the factorization of `f ∣_ U` is the preimage of `U` in
  the intermediate scheme of the factorization of `f`, by a unique comparison morphism
  compatible with both legs.

## Implementation notes

The factorization category `AlgebraicGeometry.SubintegralFactorization` is defined in
`StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Factorization`, independently of this
existence theorem, so its reduction to the relative normalization is available here. The category
is oriented so that a morphism is a map between the intermediate schemes compatible with both
legs; an initial object therefore expresses exactly the universal mapping property in the source.
The chosen object is extracted from the existence result to provide a stable object for
subsequent constructions.

The charts are indexed by `Scheme.AffineZariskiSite`, which is a plain `def` wrapping a subtype
of `X.Opens`, so its elements are not visibly subtypes at reducible transparency and a rewrite
inside a goal mentioning such an index does not fire. Every step that needs one is therefore
stated as a separate lemma whose binders are an open of `X` together with a proof that it is
affine, or as an explicitly typed equation composed with `Eq.trans` and `congrArg`; this is why
`pullbackRestrictIsoRestrict_trans_eq_homOfLE`, `pullbackRestrictIsoRestrict_hom_comp_eq` and
`specMap_op_comp` exist.

## References

* [Stacks Project, Tag 0H3N](https://stacks.math.columbia.edu/tag/0H3N)
-/
