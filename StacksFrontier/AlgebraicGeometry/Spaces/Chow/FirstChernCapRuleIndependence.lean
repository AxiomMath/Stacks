module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalFirstChernCapAdditive

/-!
# The cap product of Stacks 0EQJ does not depend on the component rule

In Situation 0EDT let `X/B` be good and let `k ∈ ℤ`.  The cap product with the first Chern
class is built in `StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernClassCap` out of a
component rule `AlgebraicGeometry.Space.FirstChernComponentCycleRule`, a `k`-cycle
`c₁(ℒ|_W) ∩ [W]` on each integral closed subspace `W ⊆ X` of δ-dimension `k + 1`; Stacks 0EQE
produces such a cycle as the Weil divisor `div_{ℒ|_W}(s_W)` of *a chosen* nonzero meromorphic
section of `ℒ|_W`, so the rule is not determined by `ℒ`.

This file shows that the choice does not matter once classes are taken in `CH_k(X)`: two
component rules whose values differ, on every integral closed subspace of δ-dimension `k + 1`
and after every integer rescaling, by a principal divisor on that subspace define the same map
`Z_{k+1}(X) ⟶ CH_k(X)`.  In particular any rule given by the Weil divisors of chosen regular
meromorphic sections induces the cap product of Stacks 0EQJ at the canonical choices,
`AlgebraicGeometry.Space.canonicalFirstChernCap`.

## Main results

* `AlgebraicGeometry.Space.chowClass_firstChernCapCycleMap_congr`: two component rules differing
  by principal divisors subspace by subspace induce the same map `Z_{k+1}(X) ⟶ CH_k(X)`.
* `AlgebraicGeometry.Space.chowClass_firstChernCapCycleMap_eq_canonicalFirstChernCap`: the rule
  `W ↦ div_{𝒩|_W}(t_W)` of an arbitrary family of regular meromorphic sections induces
  `AlgebraicGeometry.Space.canonicalFirstChernCap`, which is Stacks 0EQJ.

## Implementation notes

Stacks 0EQJ is `AlgebraicGeometry.Space.canonicalFirstChernCap` and Stacks 0EQE part (2) is
`AlgebraicGeometry.Space.chowClass_sectionWeilDivisor`; the statements below are the
independence of the *cap product on a general cycle* from the sections chosen on the subspaces
occurring in it, which is the step between those two.  The scheme-side counterpart is
`Stacks.Chow.firstChernClassCap_congr` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernCapRuleIndependence`.

**Why the hypothesis quantifies over the rescaling.**  The cap product of `α = ∑ n_W [W]` is the
locally finite sum `∑_W n_W · (i_W)_*(c₁(ℒ|_W) ∩ [W])` of Stacks 0EQ6, part (1), so what has to
be a principal divisor on `W` is `n_W • (chern W - chern' W)` and not merely the difference.
That is the form in which Stacks 0EPT is available here,
`AlgebraicGeometry.Space.isPrincipalDivisorCycle_zsmul_canonicalDivisorCycleAt_sub`: two regular
meromorphic sections of one invertible module differ by an invertible rational function `g`, and
the `a`-th multiple of the difference of their Weil divisors is the principal divisor of `gᵃ`.

**The index universe.**  The presenting family is indexed by the integral closed subspaces at
which `α` has a nonzero coefficient, a subtype of
`AlgebraicGeometry.Space.IntegralClosedSubspace … X`, which lives one universe above `u`.  So
the Chow group is `AlgebraicGeometry.Space.chowGroup.{u + 1}`, as it is for
`AlgebraicGeometry.Space.canonicalFirstChernCap_picardTensorModule` and
`AlgebraicGeometry.Space.canonicalFirstChernCap_congr_iso`.

**Related constructions.**  For a good algebraic space, Stacks 0EQE is
`AlgebraicGeometry.Space.sectionWeilDivisor` and
`AlgebraicGeometry.Space.weilDivisorOfInvertibleSheaf` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.WeilDivisorOfInvertibleSheaf`, with its
well-definedness `AlgebraicGeometry.Space.chowClass_sectionWeilDivisor`; the flat pullback of
cycles of Stacks 0EP8 is `AlgebraicGeometry.Space.flatCyclePullback`
(`StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOfCycles`); the pullback of a sheaf of
modules and of a meromorphic section along a morphism of algebraic spaces are
`AlgebraicGeometry.Space.modulePullback` and `AlgebraicGeometry.Space.pullbackMeromorphicSection`,
the latter with its regularity
`AlgebraicGeometry.Space.isRegularMeromorphicSection_pullbackMeromorphicSection`
(`StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionPullbackRegular`).

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQR](https://stacks.math.columbia.edu/tag/0EQR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section RuleIndependence

variable {D : BaseSpaceDimensionSituation.{u}}
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sX : X ⟶ D.space}
    (hX : D.IsGood sX)

/-- **The cap product of Stacks 0EQJ depends on its component rule only up to rational
equivalence on each subspace.**  Let `chern` and `chern'` be component rules such that, for every
integral closed subspace `W ⊆ X` of δ-dimension `k + 1` and every `a : ℤ`, the cycle
`a • (chern W - chern' W)` is a principal divisor on `W`.  Then the two induced maps
`Z_{k+1}(X) ⟶ CH_k(X)` agree.

Both cap products are the locally finite sum `∑_W α(W) · (i_W)_*(…)` of Stacks 0EQ6, part (1),
over the integral closed subspaces at which `α` has a nonzero coefficient
(`AlgebraicGeometry.Space.firstChernCapCycleMap_eq_cycleFamilySum`); their difference is the sum
over that same family of the cycles `α(W) • (chern W - chern' W)`, each a principal divisor on
its subspace, so the difference is rationally equivalent to zero by Stacks 0EQ6, part (2). -/
theorem chowClass_firstChernCapCycleMap_congr (k : ℤ)
    (chern chern' : FirstChernComponentCycleRule D sX k)
    (h : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D sX W = k + 1) (a : ℤ),
      IsPrincipalDivisorCycle D (W.subspace.ι ≫ sX) k (a • (chern W hW - chern' W hW)))
    (α : CycleGroup D sX (k + 1)) :
    chowClass.{u + 1} D sX hX k (firstChernCapCycleMap D sX hX k chern α) =
      chowClass.{u + 1} D sX hX k (firstChernCapCycleMap D sX hX k chern' α) := by
  have key := fun c : FirstChernComponentCycleRule D sX k =>
    firstChernCapCycleMap_eq_cycleFamilySum D sX hX k c α Subtype.val
      Subtype.val_injective (locallyFinite_cycleSupport α)
      (fun i : {W : IntegralClosedSubspace D.site D.base D.base_mem X // α.1 W ≠ 0} =>
        α.2.2 i.1 i.2) (fun W hW => ⟨⟨W, hW⟩, rfl⟩)
  rw [key chern, key chern',
    ← sub_eq_zero, ← map_sub, ← cycleFamilySum_sub]
  refine chowClass_cycleFamilySum_eq_zero.{u + 1} D sX hX k Subtype.val
    (locallyFinite_cycleSupport α) _
    (fun i : {W : IntegralClosedSubspace D.site D.base D.base_mem X // α.1 W ≠ 0} =>
      α.2.2 i.1 i.2) fun i => ?_
  rw [← smul_sub]
  exact h i.1 (α.2.2 i.1 i.2) (α.1 i.1)

/-- **Stacks 0EQJ is computed by any family of regular meromorphic sections.**  Let `𝒩` be an
invertible `𝒪_X`-module and let `t_W` be a regular meromorphic section of `𝒩|_W` for every
integral closed subspace `W ⊆ X` of δ-dimension `k + 1` — an arbitrary family, not the chosen one
of `AlgebraicGeometry.Space.componentMeromorphicSection`.  Then the component rule
`W ↦ div_{𝒩|_W}(t_W)` of Stacks 0EQE, part (1), induces the cap product of Stacks 0EQJ,
`AlgebraicGeometry.Space.canonicalFirstChernCap`, on every `(k+1)`-cycle.

This is `AlgebraicGeometry.Space.chowClass_firstChernCapCycleMap_congr` against
`AlgebraicGeometry.Space.canonicalFirstChernRule`, whose hypothesis is supplied by Stacks 0EPT in
the form `AlgebraicGeometry.Space.isPrincipalDivisorCycle_zsmul_canonicalDivisorCycleAt_sub`. -/
theorem chowClass_firstChernCapCycleMap_eq_canonicalFirstChernCap (k : ℤ)
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (t : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X),
      deltaDimension D sX W = k + 1 →
      MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
        (isGood_integralClosedSubspace D sX hX W).1
        (integralClosedSubspaceRestrict D sX hX N W))
    (ht : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D sX W = k + 1),
      IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
        (isGood_integralClosedSubspace D sX hX W).1
        (integralClosedSubspaceRestrict D sX hX N W) (t W hW))
    (α : CycleGroup D sX (k + 1)) :
    chowClass.{u + 1} D sX hX k (firstChernCapCycleMap D sX hX k
        (fun W hW => canonicalDivisorCycleAt D (W.subspace.ι ≫ sX)
          (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace
          (integralClosedSubspaceRestrict D sX hX N W)
          (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W)
          (t W hW) (ht W hW)
          (by rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX W, hW])) α) =
      canonicalFirstChernCap.{u, u + 1} D sX hX N hN k α := by
  rw [canonicalFirstChernCap, AddMonoidHom.comp_apply]
  refine chowClass_firstChernCapCycleMap_congr hX k _ (canonicalFirstChernRule D sX hX N hN k)
    (fun W hW a => ?_) α
  exact isPrincipalDivisorCycle_zsmul_canonicalDivisorCycleAt_sub D (W.subspace.ι ≫ sX)
    (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace _
    (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W) _ _ (ht W hW)
    (isRegularMeromorphicSection_componentMeromorphicSection sX hX
      (subspaceDivisorSetupOfIsGood D sX hX) N hN W) _ a

end RuleIndependence

end AlgebraicGeometry.Space

end

