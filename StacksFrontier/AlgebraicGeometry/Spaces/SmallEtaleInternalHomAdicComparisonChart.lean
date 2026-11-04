module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomAffineChartSections

/-!
# The adic comparison of Stacks 08B6, pinned on the components at a chart

Let `F` be an algebraic space over a scheme `S` of a big fppf site `B`, let `𝓘 ⊆ 𝒪_F` be a sheaf
of ideals and let `M`, `N` be `𝒪_F`-modules.  Write `𝓗 = 𝓗om_{𝒪_F}(M, N)`.  The comparison
`AlgebraicGeometry.Space.smallEtaleInternalHomAdicComparisonApp` carries `𝓗 / 𝓘 ^ n 𝓗` to
`𝓗om_{𝒪_F}(M, N / 𝓘 ^ n N)`, and this file says what it does to the reading of a section as a
map of sections over a chart:

`[α] ↦ (x ↦ [α(x)])`,

which is exactly the characterisation the comparison of Stacks 09BB is given by in
`Stacks.AdicSystem.HomComparison.hom_isom_quotient_systems_mittagLeffler_and_completion` — its
third clause, `comparison n (mk f) (mk m) = mk (f m)`.  Pinning the two comparisons against each
other is what lets the commutative-algebra statement be read as the chartwise hypothesis `h0882`
of `AlgebraicGeometry.Space.smallEtaleInternalHomAdicEquiv`.

Both identities are `rfl` up to the one morphism equation
`AlgebraicGeometry.Space.smallEtaleAdicQuotientProjection_comp_comparisonApp`, which is how the
comparison is defined out of the cokernel: the comparison precomposed with the projection is
postcomposition with the projection of `N`.  Taking components at a chart and evaluating at the
terminal object of the slice turns that into the displayed formula, because postcomposition on
the internal Hom is postcomposition on each component.

## Main results

* `AlgebraicGeometry.Space.smallEtaleInternalHomChartEvaluation_smallEtaleInternalHomMapRight` —
  **the chart reading of a postcomposed section is the postcomposed chart reading.**
* `AlgebraicGeometry.Space.smallEtaleInternalHomChartEvaluation_comparisonApp` — **the
  comparison, pinned on the components at a chart.**

## Implementation notes

The two `HasCokernels` hypotheses are supplied explicitly rather than left to instance search.
The adic quotient of `N` lives in `Modules.{u, u}` and the adic quotient of `𝓗` in
`Modules.{u, u + 1}`, so two instances at two module universes are wanted at once; with either
left to search the universe-polymorphic `Abelian` instance for the modules is tried at
`max (u + 1) ?w` and elaboration stops at the stuck constraint `u =?= max (u + 1) ?w` rather than
backtracking.

## References

* [Stacks Project, Tag 08B6](https://stacks.math.columbia.edu/tag/08B6)
* [Stacks Project, Tag 09BB](https://stacks.math.columbia.edu/tag/09BB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (M N : Modules.{u, u} B S hS F hF)

/-- **The chart reading of a postcomposed section is the postcomposed chart reading.**

`AlgebraicGeometry.Space.smallEtaleInternalHomMapRight` is postcomposition with `f` on the slice,
so its component at a chart is postcomposition with the component of `f` there; evaluating at the
terminal object of the slice gives the formula.  By `rfl`. -/
theorem smallEtaleInternalHomChartEvaluation_smallEtaleInternalHomMapRight
    {N' : Modules.{u, u} B S hS F hF} (f : N ⟶ N') (V : SmallEtale B S hS F)
    (α : (smallEtaleInternalHom B S hS F hF M N).val.obj (op V))
    (x : M.val.obj (op V)) :
    smallEtaleInternalHomChartEvaluation B S hS F hF M N' V
        ((smallEtaleInternalHomMapRight B S hS F hF M f).val.app (op V) α) x =
      (f.val.app (op V)).hom
        (smallEtaleInternalHomChartEvaluation B S hS F hF M N V α x) :=
  rfl

/-- **The adic comparison of Stacks 08B6, pinned on the components at a chart.**

The comparison applied to the class of a section `α` of `𝓗om_{𝒪_F}(M, N)` over a chart, read as a
map of the sections there, sends `x` to the class of `α(x)`:

`[α] ↦ (x ↦ [α(x)])`.

This is the third clause of
`Stacks.AdicSystem.HomComparison.hom_isom_quotient_systems_mittagLeffler_and_completion`,
`comparison n (mk f) (mk m) = mk (f m)`, read on the chart; it is what identifies the
sheaf-theoretic comparison with the module-theoretic one of Stacks 09BB.  No hypothesis on `F`,
`𝓘`, `M` or `N` is used, and no affineness of the chart: those enter only where the
identification of the sections with the ordinary quotients does. -/
theorem smallEtaleInternalHomChartEvaluation_comparisonApp
    [HasCokernels (Modules.{u, u} B S hS F hF)]
    [HasCokernels (Modules.{u, u + 1} B S hS F hF)] (n : ℕ) (V : SmallEtale B S hS F)
    (α : (smallEtaleInternalHom B S hS F hF M N).val.obj (op V))
    (x : M.val.obj (op V)) :
    smallEtaleInternalHomChartEvaluation B S hS F hF M
        (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N) V
        ((smallEtaleInternalHomAdicComparisonApp B S hS F hF 𝓘 M N n).val.app (op V)
          ((smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1)
            (smallEtaleInternalHom B S hS F hF M N)).val.app (op V) α)) x =
      ((smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1) N).val.app (op V)).hom
        (smallEtaleInternalHomChartEvaluation B S hS F hF M N V α x) :=
  (congrArg
      (fun k : smallEtaleInternalHom B S hS F hF M N ⟶
          smallEtaleInternalHom B S hS F hF M
            (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N) =>
        smallEtaleInternalHomChartEvaluation B S hS F hF M
          (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N) V (k.val.app (op V) α) x)
    (smallEtaleAdicQuotientProjection_comp_comparisonApp B S hS F hF 𝓘 M N n)).trans
    (smallEtaleInternalHomChartEvaluation_smallEtaleInternalHomMapRight B S hS F hF M N
      (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1) N) V α x)

end AlgebraicGeometry.Space

end
