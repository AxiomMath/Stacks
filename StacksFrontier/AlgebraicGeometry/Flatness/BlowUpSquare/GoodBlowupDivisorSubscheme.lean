module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.BlowupSubscheme
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupLocallyFree

/-!
# Stacks tag 0F8X at the morphism of tag 0GTY

Let `(X, D, M)` be a triple as in Situation 0F8S, let `b : X' ⟶ X` be the morphism of Stacks tag
0GTY with `D' = b⁻¹D`, let `Q = Lη_{ℐ'}Lb^*M`, and let `W ⊆ X` be the maximal open over which the
cohomology sheaves of `M` are locally free.  Stacks tag 0F8X asserts the existence of a closed
immersion `i : T ⟶ D'` of finite presentation with (1) `D' ∩ b⁻¹(W) ⊆ T` scheme theoretically,
(2) `Li^*Q` has locally free cohomology sheaves, and (3) matching ranks.

`BlowupSubscheme.lean` proves the finite presentation of `i` and part (1) for a morphism `b`
satisfying condition (1) of tag 0GTY whose restriction `b⁻¹W ↪ X' ⟶ X` is flat.  Both hold for
the morphism of tag 0GTY: condition (1) is
`AlgebraicGeometry.ComplexAndDivisorSituation.isGoodOver_goodBlowupToBase`, and the flatness is
`AlgebraicGeometry.ComplexAndDivisorSituation.flat_ι_comp_goodBlowupToBase_locallyFreeLocus`,
which is Stacks tag 0F8W: `b` is an *isomorphism* over `W`.  This file reads the statement off at
that morphism.

## Main results

* `locallyOfFinitePresentation_and_comap_eq_bot_goodBlowupToBase`:
  **Stacks tag 0F8X for the morphism of tag 0GTY**, the finite presentation of `i : T ⟶ D'` and
  part (1), for a closed subscheme `T ⊆ D'` cutting out the total obstruction ideal of More on
  Algebra, tag 0F81 on the good affine charts of the pulled-back triple.

## The closed subscheme `T`

`T` and the prescription `hT` of its ideal on the good charts are the hypotheses, exactly as in
tag 0GTZ, `locallyOfFinitePresentation_and_comap_eq_bot_of_ideal_eq_obstructionIdeal`, of which
this is the instance at the pulled-back triple `(X', D', Lb^*M)`.  Producing `T` is the gluing of
the local closed subschemes cut out by the ideals `J(N^•, g)` along a cover of `D'` by good
charts, and what that gluing needs beyond `AlgebraicGeometry.Scheme.IdealSheafData.ofAffineFamily`
is the agreement of the obstruction ideals of two charts on a common standard open, i.e. Stacks
tag 0GSW (`Stacks.Decalage.DirectSumIdeal.etaDirectSumIdeal_eq_of_derived_iso`) fed with the
derived comparison of their base-changed complexes; see
`StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleSubscheme`.

Parts (2) and (3) of the tag are parts (2) and (3) of tag 0GTZ read at the pulled-back triple.
Stacks tag 08DW, the comparison of a derived pullback with termwise base change on a complex of
finite free modules, is formalized in both of its own parts — part (1) in
`StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback`, part (2) there
and in `StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineSchemePullbackComparison`.  What
parts (2) and (3) of tag 0GTZ need beyond it is the chart-level comparison
`AlgebraicGeometry.ComplexAndDivisorSituation.ChartDecalage`, whose three identifications the
module documentation of
`StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleEtaPerfect` lists individually.

## References

* [Stacks Project, Tag 0F8X](https://stacks.math.columbia.edu/tag/0F8X)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0F8W](https://stacks.math.columbia.edu/tag/0F8W)
* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
* [Stacks Project, Tag 0GTZ](https://stacks.math.columbia.edu/tag/0GTZ)
-/

@[expose] public noncomputable section

open CategoryTheory StrictlyPerfect

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

attribute [local instance] HasDerivedCategory.standard

variable (S : ComplexAndDivisorSituation.{u, d})

/-- **Stacks tag 0F8X for the morphism `b : X' ⟶ X` of Stacks tag 0GTY: the finite presentation
of the closed immersion `i : T ⟶ D'` and part (1).**  Let `b` be the morphism of tag 0GTY, so
that `D' = b⁻¹D` is defined and `(X', D', Lb^*M)` is a good triple, and let `W ⊆ X` be the
maximal open over which the cohomology sheaves of `M` are locally free.  Let `T ⊆ D'` be a closed
subscheme whose ideal over `D' ∩ V` is the total obstruction ideal `J(N^•, g)` of More on
Algebra, tag 0F81 for every affine chart `(V, g, N^•)` of the pulled-back triple with principal
determinantal ideals.  Then

* the closed immersion `i : T ⟶ D'` is locally of finite presentation, and
* `D' ∩ b⁻¹(W) ⊆ T` scheme theoretically.

This is `locallyOfFinitePresentation_and_comap_eq_bot_of_isGoodOver` read at `goodBlowupToBase`:
condition (1) of tag 0GTY holds for it by `isGoodOver_goodBlowupToBase`, and the flatness of
`b⁻¹W ↪ X' ⟶ X` is Stacks tag 0F8W, `flat_ι_comp_goodBlowupToBase_locallyFreeLocus`. -/
@[stacks 0F8X "the finite presentation of `i : T → b^{-1}D` and part (1), stated for the \
morphism `b` of tag 0GTY itself --- namely \
AlgebraicGeometry.ComplexAndDivisorSituation.goodBlowupToBase, whose flatness over `W` is tag \
0F8W --- and for a closed subscheme `T` of `b^{-1}D` given to cut out the obstruction ideal of \
Tag 0F81 on every good chart of the pulled-back triple, as in the formalized Tag 0GTZ. Parts (2) \
and (3) specialize parts (2) and (3) of Tag 0GTZ, which need the chart-level comparison \
AlgebraicGeometry.ComplexAndDivisorSituation.ChartDecalage over and above Tag 08DW --- that tag \
being formalized in both its parts"]
theorem locallyOfFinitePresentation_and_comap_eq_bot_goodBlowupToBase
    (T : (S.pullback S.goodBlowupToBase
      S.isGoodOver_goodBlowupToBase.pullbackDefined).D.subscheme.IdealSheafData)
    (hT : ∀ C : AffineChart (S.pullback S.goodBlowupToBase
        S.isGoodOver_goodBlowupToBase.pullbackDefined),
      (∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) →
        T.ideal C.divisorAffineOpen = C.obstructionIdeal) :
    LocallyOfFinitePresentation T.subschemeι ∧
      T.comap ((S.pullback S.goodBlowupToBase
        S.isGoodOver_goodBlowupToBase.pullbackDefined).D.subschemeι ⁻¹ᵁ
          (S.goodBlowupToBase ⁻¹ᵁ S.locallyFreeLocus)).ι = ⊥ :=
  S.locallyOfFinitePresentation_and_comap_eq_bot_of_isGoodOver S.goodBlowupToBase
    S.isGoodOver_goodBlowupToBase S.flat_ι_comp_goodBlowupToBase_locallyFreeLocus T hT

end AlgebraicGeometry.ComplexAndDivisorSituation

end
