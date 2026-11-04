module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSchemeClosedInFiniteFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSchemeCoverInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverEtaleRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverExistence

/-!
# Stacks 09YC: a finite scheme cover of finite presentation, refining an étale cover

Stacks 09YC asserts, for a quasi-compact and quasi-separated algebraic space `X` over a scheme
`S`, that

1. there is a surjective finite morphism `Y ⟶ X` of finite presentation with `Y` a scheme, and
2. given a surjective étale `U ⟶ X`, `Y` may be chosen so that every point of `Y` has an open
   neighbourhood `V ⊆ Y` with `V ⟶ X` factoring through `U`.

Both clauses are proved here, under exactly those hypotheses.

## Main results

* `AlgebraicGeometry.Space.existsFiniteSurjectiveSchemeCover_and_refining`: **Stacks 09YC**, both
  clauses. This is the declaration carrying `@[stacks 09YC]`.

## Implementation notes

*Clause (1) does not follow the source's route.* The source takes the integral cover `Y ⟶ X` of
Stacks 09YB, writes it as a directed limit `Y = lim Y_i` of spaces finite and of finite
presentation over `X` (Stacks 09YA), and makes some `Y_i` a scheme by Stacks 07SR. In this
library Stacks 07SR
(`AlgebraicGeometry.Space.DescentSituation.exists_isRepresentable_system_obj`) is proved for an
index set of cardinality below the cofinality of the site's size cutoff, and the system of
Stacks 09YA cannot be taken that small in general. Let `λ` be the cofinality of the cutoff, which
may be smaller than the cutoff (the cutoff is only a strong prelimit cardinal of uncountable
cofinality), let `k` be a field and `R = k[x_α : α < λ]`, a ring of the site, and consider the
closed immersion `Spec(k) ⟶ Spec(R)` cut out by all the `x_α`. In a directed system of finite
`R`-algebras of finite presentation with colimit `R/(x_α)_α = k`, each stage is a nonzero algebra
whose relations involve only finitely many of the variables, so it kills only finitely many
`x_α`, while every `x_α` is killed at some stage; there are therefore at least `λ` stages. (An
integral algebra such as `k[y_α]/(y_α²)_{α < λ}` over `k` behaves the same way, by counting
dimensions.) No bound on the index can be proved for the system of an arbitrary integral cover,
and the statement of Stacks 09YB does not control the cover it produces.

Clause (1) is instead proved without any limit of algebraic spaces. A quasi-compact
quasi-separated `X` has a finite surjective cover `h_{Y₀} ⟶ X` by a scheme
(`AlgebraicGeometry.Space.existsFiniteSurjectiveSchemeCover_of_isQuasiCompactSpace`, the degree
induction of Stacks 09YB with finite replacements). Over an affine surjective étale chart
`p : h_V ⟶ X`, Stacks 0CP0 refines it to a finite surjective cover `h_Y ⟶ X` which factors
through `p` Zariski locally on `Y`
(`AlgebraicGeometry.Space.exists_finite_surjective_refinement_over`). Such a cover is a closed
subscheme of a scheme `T` finite and of finite presentation over `X`
(`exists_isClosedImmersion_isFinite_isFinitePresentation_of_factorsZariskiLocallyThrough`),
and `h_T ⟶ X` is surjective because `h_Y ⟶ X` factors through it.

*Clause (2)* is deduced from clause (1) rather than by repeating the limit argument with the
source's Stacks 0827 and 04AK:
`AlgebraicGeometry.Space.exists_finiteSurjectiveSchemeCover_refining_of_clause_one` refines any
surjective finite cover of finite presentation by a scheme through a prescribed surjective étale
`p` by Stacks 0CP0, applied to the quasi-compact quasi-separated scheme `Y`. The neighbourhoods
of the local clause are representable open subspaces, in the form
`AlgebraicGeometry.Space.FactorsZariskiLocallyThrough` shared with Stacks 09YB (2).

## References

* [Stacks Project, Tag 09YC](https://stacks.math.columbia.edu/tag/09YC)
* [Stacks Project, Tag 09YB](https://stacks.math.columbia.edu/tag/09YB)
* [Stacks Project, Tag 0GUP](https://stacks.math.columbia.edu/tag/0GUP)
* [Stacks Project, Tag 07SR](https://stacks.math.columbia.edu/tag/07SR)
* [Stacks Project, Tag 0CP0](https://stacks.math.columbia.edu/tag/0CP0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks Project, Tag 09YC.** Let `X` be a quasi-compact and quasi-separated algebraic space
over a scheme `S`. Then

1. there is a surjective finite morphism of finite presentation to `X` from the presheaf
   represented by an object of the big fppf site — a scheme over `S` — and
2. given a surjective étale morphism `p : U ⟶ X` from an algebraic space, such a cover can be
   chosen so that it factors through `p` on a representable open subspace neighbourhood of every
   one of its points.

Clause (1) is a finite surjective scheme cover refined through an affine étale chart by Stacks
0CP0 and embedded in a finite cover of finite presentation; clause (2) is clause (1) refined by
Stacks 0CP0. -/
@[stacks 09YC]
theorem existsFiniteSurjectiveSchemeCover_and_refining
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (hXqc : IsQuasiCompactSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X) :
    (∃ (Y : BigFppfOver B S hS) (f : yoneda.obj Y ⟶ X),
        IsSurjective B S hS f ∧ IsFinite B S hS f ∧ IsFinitePresentation B S hS f) ∧
      ∀ (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS U →
        ∀ p : U ⟶ X, IsSurjective B S hS p → IsEtale B S hS p →
          ∃ (Y : BigFppfOver B S hS) (f : yoneda.obj Y ⟶ X),
            IsSurjective B S hS f ∧ IsFinite B S hS f ∧ IsFinitePresentation B S hS f ∧
              FactorsZariskiLocallyThrough B S hS p Y f := by
  have hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  have h1 : ∃ (Y : BigFppfOver B S hS) (f : yoneda.obj Y ⟶ X),
      IsSurjective B S hS f ∧ IsFinite B S hS f ∧ IsFinitePresentation B S hS f := by
    -- a finite surjective cover by a scheme
    obtain ⟨Y₀, f₀, hf₀surj, hf₀fin⟩ :=
      existsFiniteSurjectiveSchemeCover_of_isQuasiCompactSpace B S hS hZ X hX hXqc hXqs
    obtain ⟨hY₀c, hY₀qs⟩ := compactSpace_and_quasiSeparatedSpace_of_isIntegralHom B S hS hZ Y₀ f₀
      hX hXqc hXqs (IsFinite.isIntegralHom B S hS hf₀fin)
    -- an affine surjective étale chart
    obtain ⟨V, c, hVaff, hcsurj, hcet⟩ :=
      (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X hX).1 hXqc
    have hcs : IsSurjective B S hS c := isSurjective_of_presheafSurjective B S hS c hcsurj
    have hc : IsEtale B S hS c := hcet
    -- the cover refined through the chart, Zariski locally, by Stacks 0CP0
    obtain ⟨Y, r, hrfin, hrsurj, -, hloc⟩ := exists_finite_surjective_refinement_over B S hS hX
      (isAlgebraicSpace_yoneda B S hS V) Y₀ f₀ hY₀c hY₀qs c hcs hc
    have hfsurj : IsSurjective B S hS (yoneda.map r ≫ f₀) := by
      show Function.Surjective (pointsMap B S hS (yoneda.obj Y) (yoneda.map r ≫ f₀))
      rw [pointsMap_comp B S hS (yoneda.obj Y) (yoneda.map r) f₀]
      exact hf₀surj.comp (isSurjective_yoneda_map B S hS r hrsurj)
    have _ : (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
      ⟨fun h hf => MorphismProperty.of_isPullback
        (P := @_root_.AlgebraicGeometry.IsFinite.{u}) (h.map _) hf⟩
    have hrfin' : IsFinite B S hS (yoneda.map r) :=
      isFinite_of_presheaf_isFinite _ (MorphismProperty.relative_map hrfin)
    have hffin : IsFinite B S hS (yoneda.map r ≫ f₀) := isFinite_comp B S hS hrfin' hf₀fin
    -- the refined cover is closed in a finite cover of finite presentation
    obtain ⟨T, g, i, hgfin, hgfp, -, hig⟩ :=
      exists_isClosedImmersion_isFinite_isFinitePresentation_of_factorsZariskiLocallyThrough B S hS
        hZ X hX hXqc hXqs V hVaff c hc Y (yoneda.map r ≫ f₀) hffin hloc
    refine ⟨T, g, ?_, hgfin, hgfp⟩
    intro x
    obtain ⟨y, hy⟩ := hfsurj x
    exact ⟨pointsMap B S hS _ i y, by rw [← pointsMap_comp_apply, hig]; exact hy⟩
  exact ⟨h1, fun U hU p hpsurj hpet =>
    exists_finiteSurjectiveSchemeCover_refining_of_clause_one B S hS hZ hX hU hXqc hXqs p
      hpsurj hpet h1⟩

end AlgebraicGeometry.Space

end
