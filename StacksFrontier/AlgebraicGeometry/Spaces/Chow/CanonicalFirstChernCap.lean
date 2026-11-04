module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalDivisorCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaComponentDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalence

/-!
# The cap product with the first Chern class at the canonical choices

In Situation 0EDT let `X/B` be good and let `𝒩` be an invertible `𝒪_X`-module.  Stacks 0EQJ
defines `c₁(𝒩) ∩ - : Z_{k+1}(X) → CH_k(X)` by `[W] ↦ i_*(c₁(𝒩|_W) ∩ [W])` on an integral closed
subspace `i : W → X` of δ-dimension `k + 1`, where `c₁(𝒩|_W) ∩ [W]` is the class of the Weil
divisor `div_{𝒩|_W}(t_W)` of any nonzero meromorphic section `t_W` of `𝒩|_W` (Stacks 0EQE).

Here the component cycle at `W` is `AlgebraicGeometry.Space.canonicalDivisorCycle` on `W`, for
the regular meromorphic section `AlgebraicGeometry.Space.componentMeromorphicSection` of `𝒩|_W`
given by Stacks 0EPQ, with the canonical ratios, Stacks 0EPS and Stacks 0EDN on `W`; the target
is the Chow group `CH_k(X) = Z_k(X)/∼_rat` of Stacks 0EQ6, part (4).

## Main definitions

* `AlgebraicGeometry.Space.canonicalFirstChernRule`: the component rule
  `W ↦ div_{𝒩|_W}(t_W)` of Stacks 0EQJ.
* `AlgebraicGeometry.Space.canonicalFirstChernCap`: the cap product
  `c₁(𝒩) ∩ - : Z_{k+1}(X) → CH_k(X)` of Stacks 0EQJ, cases (1) and (2).

## Main results

* `AlgebraicGeometry.Space.subspaceDivisorSetupOfIsGood`: the hypotheses bundled by
  `AlgebraicGeometry.Space.SubspaceDivisorSetup` hold on the integral closed subspaces of a good
  space.
* `AlgebraicGeometry.Space.canonicalFirstChernCap_integralCycle`: case (1) of Stacks 0EQJ, the
  value of the cap product on the fundamental cycle of an integral closed subspace of
  δ-dimension `k + 1`.

## References

* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EPQ](https://stacks.math.columbia.edu/tag/0EPQ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX)

include hX in
/-- The hypotheses `AlgebraicGeometry.Space.SubspaceDivisorSetup` bundles on the integral closed
subspaces of `X` hold on a good algebraic space `X`: each integral closed subspace is a decent
algebraic space, and the generic henselian local ring at each of its prime divisors is a
nontrivial Noetherian ring of Krull dimension at most one. -/
theorem subspaceDivisorSetupOfIsGood : SubspaceDivisorSetup D X where
  isSpace W := (isGood_integralClosedSubspace D sX hX W).1
  isDecent W := isDecentSpace_of_isGood D _ (isGood_integralClosedSubspace D sX hX W)
  nontrivial W P := P.nontrivial_genericHenselianLocalRing D.site D.base D.base_mem _ _
    W.isIntegralSpace
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _
      (isGood_integralClosedSubspace D sX hX W))
  noetherian W P := P.isNoetherianRing_genericHenselianLocalRing D.site D.base D.base_mem _ _
    W.isIntegralSpace
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _
      (isGood_integralClosedSubspace D sX hX W))
  krullDimLE W P := P.krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem _ _
    W.isIntegralSpace
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _
      (isGood_integralClosedSubspace D sX hX W))

variable (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)

include hN in
/-- The restriction `𝒩|_W` of an invertible module to an integral closed subspace is
invertible, Stacks 0B8P. -/
theorem isInvertibleModule_integralClosedSubspaceRestrict
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    IsInvertibleModule (⟨W.subspace.toFunctor, (isGood_integralClosedSubspace D sX hX W).1⟩ :
      AlgebraicSpaces D.site D.base D.base_mem) (integralClosedSubspaceRestrict D sX hX N W) :=
  modulePullbackInvertible
    (closedSubspaceHom D.site D.base D.base_mem hX.1 W.subspace W.isClosedSubspace) N hN

/-- **The component cycle `c₁(𝒩|_W) ∩ [W]` of Stacks 0EQJ, at the canonical choices.**  On an
integral closed subspace `W ⊆ X` of δ-dimension `k + 1` it is the Weil divisor
`div_{𝒩|_W}(t_W) ∈ Z_k(W)` of Stacks 0EQE, part (1), of the regular meromorphic section `t_W` of
`𝒩|_W` given by Stacks 0EPQ, at the canonical ratios. -/
def canonicalFirstChernRule (k : ℤ) : FirstChernComponentCycleRule D sX k := fun W hW =>
  canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
    W.isIntegralSpace (integralClosedSubspaceRestrict D sX hX N W)
    (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W)
    (componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX) N hN W)
    (isRegularMeromorphicSection_componentMeromorphicSection sX hX
      (subspaceDivisorSetupOfIsGood D sX hX) N hN W)
    (by rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX W, hW])

/-- *Intersection with the first Chern class of an invertible sheaf*: the cap product
`c₁(𝒩) ∩ - : Z_{k+1}(X) → CH_k(X)` attached to an invertible `𝒪_X`-module `𝒩` on a good
algebraic space `X/B`. It sends `α = ∑ n_W [W]` to the class of `∑_W n_W i_*(c₁(𝒩|_W) ∩ [W])`,
where `i : W → X` is the inclusion and the component cycle `c₁(𝒩|_W) ∩ [W]` is
`AlgebraicGeometry.Space.canonicalFirstChernRule`, the Weil divisor `div_{𝒩|_W}(t_W)` of
Stacks 0EQE, part (1), at the canonical ratios of Stacks 0EPR for the regular meromorphic section
of `𝒩|_W` given by Stacks 0EPQ. The target is the Chow group `CH_k(X) = Z_k(X)/∼_rat` of
Stacks 0EQ6, part (4); the pushforward `i_*` is applied to the cycle and the class is taken in
`CH_k(X)` afterwards. -/
@[stacks 0EQJ "the cap product c_1(N) ∩ - : Z_{k+1}(X) → CH_k(X) with the first Chern class of
an invertible O_X-module N on a good algebraic space X/B, cases (1) and (2): the component cycle
c_1(N|_W) ∩ [W] is the Weil divisor div_{N|_W}(t_W) of Stacks 0EQE at the canonical ratios of
Stacks 0EPR for a regular meromorphic section given by Stacks 0EPQ (canonicalFirstChernRule),
the target is the Chow group of Stacks 0EQ6 part (4), and the pushforward i_* and the
fundamental cycle [W] are the genuine ones; nothing is a parameter. Case (1) is
canonicalFirstChernCap_integralCycle and case (2) is the coefficientwise additive extension
firstChernCapCycleMap. The source pushes the class of div_{N|_W}(t_W) forward, this pushes the
cycle forward and takes the class afterwards"]
def canonicalFirstChernCap (k : ℤ) : CycleGroup D sX (k + 1) →+ chowGroup.{v} D sX hX k :=
  (chowClass.{v} D sX hX k).comp
    (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k))

/-- On the fundamental cycle `[W]` of an integral closed subspace `i : W → X` of δ-dimension
`k + 1` the cap product `AlgebraicGeometry.Space.canonicalFirstChernCap` is the class of
`i_*(c₁(𝒩|_W) ∩ [W])`, the inner cycle being the Weil divisor `div_{𝒩|_W}(t_W)` of Stacks 0EQE at
the canonical choices. -/
@[stacks 0EQJ "case (1): the value of the cap product on the fundamental cycle [W] of an
integral closed subspace W of δ-dimension k+1 is the class of i_*(c_1(N|_W) ∩ [W]), with the
component cycle c_1(N|_W) ∩ [W] the Weil divisor div_{N|_W}(t_W) of Stacks 0EQE at the
canonical ratios and the class taken in the Chow group of Stacks 0EQ6; i_* is applied to the
cycle and the class taken afterwards, the source applying it to the class"]
theorem canonicalFirstChernCap_integralCycle (k : ℤ)
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D sX W = k + 1) :
    canonicalFirstChernCap.{u, v} D sX hX N hN k (integralCycle D sX (k + 1) W hW) =
      chowClass.{v} D sX hX k (integralClosedSubspacePushforward D sX hX W k
        (canonicalFirstChernRule D sX hX N hN k W hW)) := by
  rw [canonicalFirstChernCap, AddMonoidHom.comp_apply,
    firstChernCapCycleMap_integralCycle D sX hX k _ hW]

end AlgebraicGeometry.Space

end
