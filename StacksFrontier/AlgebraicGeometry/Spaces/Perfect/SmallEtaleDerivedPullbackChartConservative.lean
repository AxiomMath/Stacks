module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedIsoLocal

/-!
# Étale charts detect isomorphisms of `D(𝒪_X)` locally on every chart

Let `X` be an algebraic space and `φ : M ⟶ N` a morphism of `D(𝒪_X)`. If every étale chart `U`
of `X` has an étale covering `{V → U}` such that the derived pullback of `φ` to each chart space
`V` is an isomorphism, then `φ` is an isomorphism.

This is `AlgebraicGeometry.Space.isIso_of_isIso_smallEtaleDerivedModulePullback_chartToSpace`,
which asks for one family of charts covering the final object, read with a covering of every
chart, the form in which perfectness (Stacks 08G5) hands out its local strictly perfect models
(`AlgebraicGeometry.Space.exists_hasStrictlyPerfectModel_chart_of_isPerfect`). The family is the
one indexed by the pairs of a chart and an arrow of its covering; it covers the final object
because each chosen covering consists of arrows out of members of the family.

## Main results

* `isIso_of_forall_covering_isIso_smallEtaleDerivedModulePullback_chartToSpace`: a morphism of
  `D(𝒪_X)` whose derived pullback to every member of an étale covering of every chart is an
  isomorphism is an isomorphism.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- **Étale charts detect isomorphisms of `D(𝒪_X)` locally on every chart.** If every étale chart
`U` of `X` has an étale covering `{V → U}` such that the derived pullback of `φ` to each chart
space `V` is an isomorphism, then `φ` is an isomorphism. -/
theorem isIso_of_forall_covering_isIso_smallEtaleDerivedModulePullback_chartToSpace
    {M N : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (φ : M ⟶ N)
    (h : ∀ U : SmallEtale B S hS X.1,
      ∃ R : Presieve U, Sieve.generate R ∈ SmallEtale.topology B S hS X.1 U ∧
        ∀ ⦃V : SmallEtale B S hS X.1⦄ (g : V ⟶ U), R g →
          IsIso ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).map φ)) :
    IsIso φ := by
  classical
  choose R hR hφ using h
  refine isIso_of_isIso_smallEtaleDerivedModulePullback_chartToSpace B S hS
    (V := fun k : Σ U : SmallEtale B S hS X.1, Σ V : SmallEtale B S hS X.1,
      { g : V ⟶ U // R U g } => k.2.1) (fun W => ?_) φ fun k => hφ k.1 k.2.2.1 k.2.2.2
  refine (SmallEtale.topology B S hS X.1).superset_covering ?_ (hR W)
  rintro Z g ⟨V, a, f, hf, rfl⟩
  exact ⟨⟨W, V, f, hf⟩, ⟨a⟩⟩

end AlgebraicGeometry.Space

end
