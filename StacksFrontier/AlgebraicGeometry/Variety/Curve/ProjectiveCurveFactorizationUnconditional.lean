module

public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.SchemeTheoreticClosure
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCurveFactorization
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RegularCompactification
import StacksCore.Tactic.StacksAttribute

/-!
# Factoring a morphism from a curve through a projective curve

[Stacks, Tag 0BY0] says that a morphism `X ⟶ Y` of varieties over a field `k`, with `Y` proper
and `X` a curve, factors as `X ⟶ X̄ ⟶ Y` with `X ⟶ X̄` an open immersion and `X̄` a projective
curve.

## Main results

* `AlgebraicGeometry.exists_isOpenImmersion_isCurve_isProjectiveMorphism_factorization_of_isCurve`:
  **[Stacks, Tag 0BY0]**.

## Implementation notes

The projective completion `j : X ⟶ X̄` with discrete valuation boundary is [Stacks, Tag 0BXW] in
the form
`Stacks.CurveProjectiveCompletion.exists_projective_completion_discreteValuation_of_isReduced`,
which asks only that `X` be reduced; a curve is integral, hence reduced.

The morphism `g` is extended across the finitely many boundary points by
`AlgebraicGeometry.exists_extension_of_finite_compl_valuationRing_stalk`, the finite iteration of
[Stacks, Tag 0BX7]. That extension needs valuation rings, not discrete valuation rings, so the
discrete valuation rings of [Stacks, Tag 0BXW] are converted at the point of use. Following
[Stacks, Tag 0BXW], the hypothesis is spelled `∃ _ : IsDomain _, ValuationRing _`, because
`ValuationRing` cannot be stated without an `IsDomain` instance.

The completion is again a curve: it is reduced by [Stacks, Tag 056E],
`AlgebraicGeometry.isReduced_of_isSchemeTheoreticallyDense`, because the dense open `j(X)` is
scheme-theoretically dense and is reduced, being isomorphic to `X`; it is irreducible by
`AlgebraicGeometry.irreducibleSpace_of_isDominant`, because `j` is dominant with irreducible
source; and its dimension is one, bounded above by
`Stacks.CurveProjectiveCompletion.topologicalKrullDim_le_of_dense_isOpenImmersion` and below by
`Topology.IsInducing.topologicalKrullDim_le` for the open embedding `j`. Separatedness, finite
type and quasi-compactness of its structure morphism come from properness, which H-projectivity
supplies.

## References

* [Stacks Project, Tag 0BY0](https://stacks.math.columbia.edu/tag/0BY0)
* [Stacks Project, Tag 0BXW](https://stacks.math.columbia.edu/tag/0BXW)
* [Stacks Project, Tag 0BX7](https://stacks.math.columbia.edu/tag/0BX7)
* [Stacks Project, Tag 056E](https://stacks.math.columbia.edu/tag/056E)
* [Stacks Project, Tag 0A23](https://stacks.math.columbia.edu/tag/0A23)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Stacks Tag 0BY0 -/

/-- **[Stacks, Tag 0BY0].** Let `k` be a field, let `X` be a curve over `k` and `Y` a proper
variety over `k`, and let `g : X ⟶ Y` be a morphism over `k`. Then there is a factorization
`X ⟶ X̄ ⟶ Y` of `g` in which `X ⟶ X̄` is an open immersion and `X̄` is a projective curve over
`k`, that is, a curve whose structure morphism is H-projective. -/
@[stacks 0BY0 "the full statement with nothing assumed. Both clauses are proved of the scheme \
constructed: `j` is an open immersion and `q` makes `Xbar` a curve (Tag 0A23) which is \
H-projective over `k` (Tag 01W8). The factorization `j ≫ G = g` is part of the conclusion, \
together with `j ≫ q = pX` and `G ≫ pY = q`, so both halves are morphisms of `k`-schemes. \
Tag 09NZ is not assumed: a curve is integral, hence reduced, and the library's Tag 0BXW, \
`Stacks.CurveProjectiveCompletion.exists_projective_completion_discreteValuation_of_isReduced`, \
carries nothing for a reduced source"]
theorem exists_isOpenImmersion_isCurve_isProjectiveMorphism_factorization_of_isCurve
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (CommRingCat.of k)) (pY : Y ⟶ Spec (CommRingCat.of k))
    [IsCurve k pX] [IsProperVariety k pY] (g : X ⟶ Y) (hg : g ≫ pY = pX) :
    ∃ (Xbar : Scheme.{u}) (q : Xbar ⟶ Spec (CommRingCat.of k)) (j : X ⟶ Xbar) (G : Xbar ⟶ Y),
      IsOpenImmersion j ∧ IsCurve k q ∧ IsProjectiveMorphism q ∧
        j ≫ q = pX ∧ G ≫ pY = q ∧ j ≫ G = g := by
  have hdimX : topologicalKrullDim (X : Type u) = 1 :=
    IsCurve.topologicalKrullDim_eq_one (k := k) (f := pX)
  obtain ⟨Xbar, q, j, hj, hjq, hproj, hdom, hsdense, hfin, hbdry⟩ :=
    Stacks.CurveProjectiveCompletion.exists_projective_completion_discreteValuation_of_isReduced
      k pX hdimX.le
  have _ : IsOpenImmersion j := hj
  have _ : IsDominant j := hdom
  have _ : IsProper q := isProper_of_isProjectiveMorphism q hproj
  have _ : IsLocallyNoetherian Xbar := LocallyOfFiniteType.isLocallyNoetherian q
  have _ : CompactSpace Xbar := QuasiCompact.compactSpace_of_compactSpace q
  have _ : AlgebraicGeometry.IsNoetherian Xbar := AlgebraicGeometry.IsNoetherian.mk
  have hUdense : Dense ((j.opensRange : Xbar.Opens) : Set Xbar) := by
    rw [Scheme.Hom.coe_opensRange]
    exact hdom.denseRange
  have hUfin : (((j.opensRange : Xbar.Opens) : Set Xbar)ᶜ).Finite := by
    simpa only [Scheme.Hom.coe_opensRange] using hfin
  have hUstalk : ∀ z : Xbar, z ∉ ((j.opensRange : Xbar.Opens) : Set Xbar) →
      ∃ _ : IsDomain (Xbar.presheaf.stalk z), ValuationRing (Xbar.presheaf.stalk z) := by
    intro z hz
    obtain ⟨-, hzdom, hzdvr⟩ := hbdry z (by simpa only [Scheme.Hom.coe_opensRange] using hz)
    refine ⟨hzdom, ?_⟩
    have _ : IsDomain (Xbar.presheaf.stalk z) := hzdom
    have _ : IsDiscreteValuationRing (Xbar.presheaf.stalk z) := hzdvr
    infer_instance
  have hfV : (j.isoOpensRange.inv ≫ g) ≫ pY = j.opensRange.ι ≫ q := by
    rw [Category.assoc, hg, ← hjq, ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
  obtain ⟨G, hGq, hGU⟩ :=
    exists_extension_of_finite_compl_valuationRing_stalk q pY j.opensRange hUdense hUfin
      hUstalk (j.isoOpensRange.inv ≫ g) hfV
  have hjG : j ≫ G = g := by
    rw [← Scheme.Hom.isoOpensRange_hom_ι j, Category.assoc, hGU, Iso.hom_inv_id_assoc]
  have _ : IsReduced j.opensRange.toScheme := isReduced_of_isOpenImmersion j.isoOpensRange.inv
  have _ : AlgebraicGeometry.IsReduced Xbar :=
    isReduced_of_isSchemeTheoreticallyDense j.opensRange hsdense
  have _ : IrreducibleSpace Xbar := irreducibleSpace_of_isDominant j
  have _ : AlgebraicGeometry.IsIntegral Xbar := isIntegral_of_irreducibleSpace_of_isReduced Xbar
  have hdimXbar : topologicalKrullDim (Xbar : Type u) = 1 :=
    le_antisymm
      ((Stacks.CurveProjectiveCompletion.topologicalKrullDim_le_of_dense_isOpenImmersion
        k j pX q hjq hdom.denseRange).trans hdimX.le)
      (hdimX ▸ Topology.IsInducing.topologicalKrullDim_le
        (f := (j.base : X → Xbar)) j.isOpenEmbedding.isEmbedding.isInducing)
  have _ : IsCurve k q :=
    { toIsVariety := { }
      topologicalKrullDim_eq_one := hdimXbar }
  exact ⟨Xbar, q, j, G, hj, inferInstance, hproj, hjq, hGq, hjG⟩

end AlgebraicGeometry

end
