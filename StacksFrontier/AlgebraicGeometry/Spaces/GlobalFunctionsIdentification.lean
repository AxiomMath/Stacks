module

public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas

/-!
# The two names for the global regular functions of a presheaf

The library carries the ring of global regular functions of a presheaf `F` on the big fppf
site of `S` under two names, `AlgebraicGeometry.Space.globalFunctions` and
`AlgebraicGeometry.Space.globalFunctions'`, both built from the structure presheaf
`AlgebraicGeometry.Space.structurePresheaf` (`Spaces/StructureSheaf.lean:258`), the composite
`(SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ` on
`(SmallEtale B S hS F)ᵒᵖ`, so the two rings are the same ring. This file transports across
that identity the results about global functions which are stated for one of the two names
only.

The identity holds by `rfl`, but only at default transparency: the structure presheaf is a
`def`, so unification and `exact` see through it while `simp` and `rw` do not match one
against the other syntactically. That is what makes the transported statements below worth
having, rather than leaving each consumer to rely on the definitional unfolding.

## Main results

* `AlgebraicGeometry.Space.globalFunctionsChartRestriction_apply`: restriction of a global
  regular function to an étale chart is evaluation of the compatible family at that chart.
  This is the rewrite that carries a goal from one name to the other.
* `AlgebraicGeometry.Space.injective_globalFunctions'_val_of_isSurjective` and
  `AlgebraicGeometry.Space.eq_of_globalFunctionsChartRestriction_eq`: restriction of global
  regular functions to an étale chart which is surjective on points is injective, stated for
  `AlgebraicGeometry.Space.globalFunctions'` and in the form which separates two sections.

## Implementation notes

`AlgebraicGeometry.Space.injective_globalFunctions_val_of_isSurjective`
(`StacksFrontier/AlgebraicGeometry/Spaces/ReducedGlobalFunctions.lean`) carries an
`AlgebraicGeometry.IsAlgebraicSpace` hypothesis, used to see the chart as a covering of the
final object of the small étale site and then to appeal to the sheaf condition. That
hypothesis is not needed: an étale chart already bundles representability of its base changes,
and the proof of
`AlgebraicGeometry.Space.exists_reduced_etale_chart_injective_globalSections`
(`StacksFrontier/AlgebraicGeometry/Spaces/Topologies/ReducedEtaleChart.lean`) obtains the same
injectivity from `AlgebraicGeometry.Space.gamma_injective_of_etale_surjection` alone, with no
sheaf condition and no algebraic space hypothesis. The statements below keep the hypothesis,
because their consumers quantify over `AlgebraicGeometry.Space.AlgebraicSpaces` and so supply
it for free.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- Restriction of a global regular function of `X` to an étale chart `V` is evaluation of the
compatible family at `V`.

This is the rewrite which carries a goal stated with
`AlgebraicGeometry.Space.globalFunctionsChartRestriction` to one stated with the underlying
compatible family, and so from either of the two names of the ring of global regular functions
to the other. -/
@[simp]
theorem globalFunctionsChartRestriction_apply (X : AlgebraicSpaces B S hS)
    (V : SmallEtale B S hS X.obj) (s : globalFunctions' B S hS X.obj) :
    globalFunctionsChartRestriction B S hS X V s = s.val (op V) :=
  rfl

/-- Evaluation of global regular functions at an étale chart whose structure morphism is
surjective on points is injective, in the
`AlgebraicGeometry.Space.globalFunctions'` spelling.

This is `AlgebraicGeometry.Space.injective_globalFunctions_val_of_isSurjective`, whose
statement is about `AlgebraicGeometry.Space.globalFunctions`; the two are the same type. -/
theorem injective_globalFunctions'_val_of_isSurjective (hF : IsAlgebraicSpace B S hS F)
    (V : SmallEtale B S hS F) (hV : IsSurjective B S hS V.obj.hom) :
    Function.Injective fun s : globalFunctions' B S hS F => s.val (op V) :=
  injective_globalFunctions_val_of_isSurjective B S hS F hF V hV

variable {B S hS}

/-- Two global regular functions on an algebraic space which agree on one étale chart whose
structure morphism is surjective on points are equal.

The separating form of
`AlgebraicGeometry.Space.injective_globalFunctionsChartRestriction_of_isSurjective`, stated so
that it applies to sections of `AlgebraicGeometry.Space.globalFunctions'`. -/
theorem eq_of_globalFunctionsChartRestriction_eq (X : AlgebraicSpaces B S hS)
    (V : SmallEtale B S hS X.obj) (hV : IsSurjective B S hS V.obj.hom)
    {s s' : globalFunctions' B S hS X.obj}
    (h : globalFunctionsChartRestriction B S hS X V s
      = globalFunctionsChartRestriction B S hS X V s') :
    s = s' :=
  injective_globalFunctionsChartRestriction_of_isSurjective B S hS X V hV h

/-- Two global regular functions on an algebraic space whose compatible families agree at one
étale chart which is surjective on points are equal. -/
theorem eq_of_val_eq_of_isSurjective (X : AlgebraicSpaces B S hS)
    (V : SmallEtale B S hS X.obj) (hV : IsSurjective B S hS V.obj.hom)
    {s s' : globalFunctions' B S hS X.obj} (h : s.val (op V) = s'.val (op V)) :
    s = s' :=
  injective_globalFunctions'_val_of_isSurjective B S hS X.obj X.property V hV h

end AlgebraicGeometry.Space

end
