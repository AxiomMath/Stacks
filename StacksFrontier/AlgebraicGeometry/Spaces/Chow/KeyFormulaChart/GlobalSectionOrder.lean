module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaChart.SectionOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionOfGlobalSectionChartLocal

/-!
# The order of vanishing of a global section along a prime divisor

Let `X` be a decent, locally Noetherian, integral algebraic space satisfying the two hypotheses
of Stacks 0EN6, let `Z ⊂ X` be a prime divisor, let `ℒ` be an invertible `𝒪_X`-module and let
`s ∈ Γ(X, ℒ)` be a nonzero global section.  The divisor `div_ℒ(s)` of Stacks 0EPU is a function
of a *meromorphic* section, so its coefficient at `Z` is the order of vanishing of the canonical
meromorphic section `AlgebraicGeometry.Space.toMeromorphicSection` of `s`.  This file computes
that coefficient as the order of vanishing of a **regular function**:

`ord_{Z, ℒ}(s) = ord_{𝒪_{V, v}}(l₀(s|_V))`,

for an affine étale chart `V` over which `ℒ` is free, a point `v` of `V` over the generic point
of `Z`, and the coordinate `l₀(s|_V)` of `s` in that trivialization, read in `𝒪_{V, v}`.

The right-hand side is the content of Stacks 0846: `l₀(s|_V)` generates the defining ideal of the
zero scheme `Z(s)` on `V` (`AlgebraicGeometry.Space.sectionEvaluationIdealAt_eq_span_singleton`
with Stacks 0846), and `Ring.ord` is by definition the length of the quotient by the principal
ideal it generates.  So this is the left-hand side of the first identity of Stacks 0EQF brought
to the ring in which the right-hand side also lives.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.orderOfVanishingSection_toMeromorphicSection_eq_ord`:
  `ord_{Z, ℒ}(s) = (ord_{𝒪_{V, v}}(l₀(s|_V))).toNat` for a nonzero global section `s`.

## Implementation notes

The hypothesis carried on the coordinate is that it is a **nonzerodivisor** of `𝒪_{V, v}`, which
is the form `Ring.ordTotalFracInt_algebraMap` consumes and which the right-hand side of Stacks
0EQF needs as well (a length of a quotient by a principal ideal is finite exactly there).  It is
*not* an extra assumption about the conclusion: it replaces the hypothesis `hc` of
`PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_eq_ordTotalFracInt` (in the namespace
`AlgebraicGeometry.Space`), namely that the chart ratio is a unit of `Q(𝒪_{V, v})`, which is
derived from it here by `IsLocalization.map_units`.

The proof is three rewrites.  The chart ratio of the canonical meromorphic section of `s` is the
image of the coordinate under `𝒪_X(V) → 𝒦_X(V)`
(`AlgebraicGeometry.Space.chartRatio_toMeromorphicSection_dual`); reading that in `Q(𝒪_{V, v})`
is taking the germ at `v` and pushing it into the fraction ring
(`AlgebraicGeometry.Space.chartPointMeromorphicMap_algebraMap`); and the order of vanishing of
the image of a nonzerodivisor is `Ring.ord` of that nonzerodivisor
(`Ring.ordTotalFracInt_algebraMap`).

## References

* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPU](https://stacks.math.columbia.edu/tag/0EPU)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 0846](https://stacks.math.columbia.edu/tag/0846)
* [Stacks Project, Tag 0EQF](https://stacks.math.columbia.edu/tag/0EQF)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : AlgebraicSpaces B S hS} (hdec : IsDecentSpace B S hS X.1) (Z : PrimeDivisor B S hS X.1)
    (hInt : IsIntegralSpace B S hS X.1)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

include hInt hN in
/-- **The order of vanishing of a nonzero global section along a prime divisor is the order of
vanishing of its coordinate in a trivialization.**  Let `X` be decent, locally Noetherian and
integral, satisfying the two hypotheses of Stacks 0EN6, let `Z ⊂ X` be a prime divisor with
generic point `ξ`, let `ℒ` be invertible and let `s ∈ Γ(X, ℒ)` be nonzero.  Let `V` be an affine
étale chart over which `ℒ` is free on the compatible family `e`, let `v` be a point of `V` over
`ξ`, and let `l₀` be the coordinate functional of the generator `e` over `V`
(`AlgebraicGeometry.Space.chartDual`).  Then

`ord_{Z, ℒ}(s) = ord_{𝒪_{V, v}}(l₀(s|_V))`,

the coefficient of `div_ℒ(s)` at `Z` being read at the canonical ratio of Stacks 0EPR and the
meromorphic section of `s` being `AlgebraicGeometry.Space.toMeromorphicSection`.

The regular function `l₀(s|_V)` is, by Stacks 0846, a local equation for the zero scheme `Z(s)`
on `V`, and `Ring.ord` of it is by definition the length of `𝒪_{V, v}` modulo the ideal it
generates — which is the multiplicity of `Z` in `Z(s)`.  So this identity is the left-hand side
of the first conclusion of Stacks 0EQF brought into the ring where the right-hand side lives. -/
theorem PrimeDivisor.orderOfVanishingSection_toMeromorphicSection_eq_ord
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (L : Modules.{u, u} B S hS X.1 X.2) (hL : IsInvertibleModule (B := B) X L)
    (s : L.sections) (hs : s ≠ 0)
    (V : SmallEtale B S hS X.1) (hV : IsAffine (chartScheme V))
    (e : (W : SmallEtale B S hS X.1) → (W ⟶ V) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale B S hS X.1) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦ r • e W k)
    (v : chartScheme V) (hv : chartSchemeToPoints B S hS X.1 V v = Z.genericPoint B S hS X.1)
    [IsNoetherianRing ((chartScheme V).presheaf.stalk v)]
    [Ring.KrullDimLE 1 ((chartScheme V).presheaf.stalk v)]
    (hr : ((chartScheme V).presheaf.germ ⊤ v trivial).hom
        (chartDual B S hS X.1 X.2 L V (e V (𝟙 V)) (hebij V (𝟙 V)) (s.eval (op V))) ∈
      ((chartScheme V).presheaf.stalk v)⁰) :
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS X.2 hdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS X.2 hdec hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS X.2 hdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS X.2 hdec hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS X.2 hdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS X.2 hdec hInt hN
    orderOfVanishingSection.{u, u} B S hS X.2 hdec Z L
        (toMeromorphicSection B S hS X.1 X.2 L s)
        (Z.canonicalLocalRatio B S hS X.2 hdec L hL hInt hN) =
      ((Ring.ord ((chartScheme V).presheaf.stalk v)
        (((chartScheme V).presheaf.germ ⊤ v trivial).hom
          (chartDual B S hS X.1 X.2 L V (e V (𝟙 V)) (hebij V (𝟙 V))
            (s.eval (op V))))).toNat : ℤ) := by
  set g := ((chartScheme V).presheaf.germ ⊤ v trivial).hom
    (chartDual B S hS X.1 X.2 L V (e V (𝟙 V)) (hebij V (𝟙 V)) (s.eval (op V))) with hg
  have hu : IsUnit (algebraMap ((chartScheme V).presheaf.stalk v)
      (FractionRing ((chartScheme V).presheaf.stalk v)) g) :=
    IsLocalization.map_units _ ⟨g, hr⟩
  have hcr : chartPointMeromorphicMap B S hS X V hV
        (isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin V hV) v
        (chartRatio B S hS X.1 X.2 L V e hecompat hebij
          (toMeromorphicSection B S hS X.1 X.2 L s)) =
      algebraMap ((chartScheme V).presheaf.stalk v)
        (FractionRing ((chartScheme V).presheaf.stalk v)) g := by
    rw [chartRatio_toMeromorphicSection_dual B S hS X.1 X.2 L V e hecompat hebij s]
    exact chartPointMeromorphicMap_algebraMap B S hS X V hV
      (isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin V hV) v _
  rw [Z.orderOfVanishingSection_canonicalLocalRatio_eq_ordTotalFracInt B S hS hdec hInt hN hwa
      hfin L hL (toMeromorphicSection B S hS X.1 X.2 L s)
      (isRegularMeromorphicSection_toMeromorphicSection B S hS X.2 hInt hN L hL s hs)
      V hV e hecompat hebij v hv (hcr ▸ hu),
    Ring.ordTotalFracInt_congr _ (hcr ▸ hu) hu hcr]
  exact Ring.ordTotalFracInt_algebraMap _ g hr

end AlgebraicGeometry.Space

end
