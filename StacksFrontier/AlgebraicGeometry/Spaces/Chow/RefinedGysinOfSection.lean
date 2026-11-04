module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalGysinRule
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralGoodSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InvertibleSheafDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaComponentDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFibreSum
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.TrivialRestrictionGysin
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGenericStalkGeneratingChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorHenselianLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.InducedDimensionFunction
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGeneratingOrderZero
public import StacksFrontier.AlgebraicGeometry.Spaces.PicardWeilDivisorClassIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints

/-!
# The refined Gysin homomorphism of a section of an invertible sheaf

Let `X/B` be a good algebraic space, let `ℒ` be an invertible `𝒪_X`-module with a global section
`s`, let `E = Z(s)` be the vanishing locus of `s` and let `i : E → X` be the closed immersion. The
refined Gysin homomorphism

  `i^* : Z_{k+1}(X) ⟶ CH_k(E)`

is given by `i^*[W] = [E ∩ W]_k` for an integral closed subspace `W ⊆ X` of δ-dimension `k + 1`
not contained in `E`, by `i^*[W] = i'_*(c₁(ℒ|_W) ∩ [W])` for one contained in `E`, and by
linearity on a `(k+1)`-cycle; when `E` is an effective Cartier divisor, `E · α = i_* i^* α`.
The letter `D` denotes the dimension situation, so the vanishing locus is written `E`.

## Main definitions

* `AlgebraicGeometry.Space.restrictedDivisorCycle`: the `k`-cycle `c₁(ℒ|_W) ∩ [W]` on an
  integral closed subspace `W ⊆ X` of δ-dimension `k + 1`, the Weil divisor `div_{ℒ|_W}(t_W)` of
  the regular meromorphic section `t_W` of the invertible module `ℒ|_W`.
* `AlgebraicGeometry.Space.sectionGysinRule`: the component rule of the refined Gysin
  homomorphism, with the cycle `[E ∩ W]_k` for `W ⊄ E` and the cycle above for `W ⊆ E`.
* `AlgebraicGeometry.Space.sectionRefinedGysin`: the refined Gysin homomorphism
  `i^* : Z_{k+1}(X) ⟶ CH_k(E)`.
* `AlgebraicGeometry.Space.sectionCartierIntersection`: the operation `E · α = i_* i^* α` of an
  effective Cartier divisor, with values in `CH_k(X)`.

## Main results

* `AlgebraicGeometry.Space.exists_dimensionFunction_deltaValue_of_isGood`: for a good space,
  `δ_{X/B}` is a dimension function on `|X|`.
* `AlgebraicGeometry.Space.isInvertibleModule_integralClosedSubspaceRestrict_of_isInvertibleSheaf`:
  the restriction `ℒ|_W` of an invertible module to an integral closed subspace is invertible.
* `AlgebraicGeometry.Space.sectionRefinedGysin_integralCycle_of_not_le`,
  `AlgebraicGeometry.Space.sectionRefinedGysin_integralCycle_of_le` and
  `AlgebraicGeometry.Space.sectionRefinedGysin_apply`: the values of `i^*` on `[W]` for `W ⊄ E`
  and for `W ⊆ E`, and on a general cycle.

## References

* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EPQ](https://stacks.math.columbia.edu/tag/0EPQ)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-! ### The dimension function and the grading -/

/-- The function `δ_{X/B}` on the points of a good algebraic space `X/B` is a dimension
function. -/
alias exists_dimensionFunction_deltaValue_of_isGood :=
  AlgebraicGeometry.Space.exists_dimensionFunction_deltaValue

/-! ### The restriction of an invertible sheaf to an integral closed subspace -/

section Restriction

variable (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (k : ℤ)

/-- The restriction `ℒ|_W` of an invertible `𝒪_X`-module to an integral closed subspace
`W ⊆ X`, its inverse image along the closed immersion `W → X`, is an invertible `𝒪_W`-module. -/
theorem isInvertibleModule_integralClosedSubspaceRestrict_of_isInvertibleSheaf
    (hL : IsInvertibleSheaf D p hp L)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    IsInvertibleModule (B := D.site)
      ⟨W.subspace.toFunctor, (isGood_integralClosedSubspace D p hp W).1⟩
      (integralClosedSubspaceRestrict D p hp L W) :=
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
    (isInvertibleSheaf_pullbackSheaf D p hp (W.subspace.ι ≫ p)
      (isGood_integralClosedSubspace D p hp W)
      (closedSubspaceHom D.site D.base D.base_mem hp.1 W.subspace W.isClosedSubspace) L hL)

/-! ### The Weil divisor of the regular meromorphic section of `ℒ|_W` -/

/-- The regular meromorphic section `t_W` of the invertible module `ℒ|_W` on an integral closed
subspace `W ⊆ X`. -/
abbrev restrictedSectionOfIntegralClosedSubspace (hL : IsInvertibleSheaf D p hp L)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (isGood_integralClosedSubspace D p hp W).1 (integralClosedSubspaceRestrict D p hp L W) :=
  regularMeromorphicSection D.site D.base D.base_mem (isGood_integralClosedSubspace D p hp W).1
    W.isIntegralSpace
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D (W.subspace.ι ≫ p)
      (isGood_integralClosedSubspace D p hp W))
    _ (isInvertibleModule_integralClosedSubspaceRestrict_of_isInvertibleSheaf D p hp L hL W)

/-- The ratios `t_W / t_ξ` at the generic points of the prime divisors of an
integral closed subspace `W ⊆ X`, for the invertible module `ℒ|_W`. -/
abbrev restrictedRatio (hL : IsInvertibleSheaf D p hp L)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    LocalRatioFamily.{u, u} D.site D.base D.base_mem (isGood_integralClosedSubspace D p hp W).1
      W.isIntegralSpace.2.1 (integralClosedSubspaceRestrict D p hp L W) :=
  canonicalLocalRatioFamily D.site D.base D.base_mem (isGood_integralClosedSubspace D p hp W).1
    W.isIntegralSpace.2.1 _
    (isInvertibleModule_integralClosedSubspaceRestrict_of_isInvertibleSheaf D p hp L hL W)
    W.isIntegralSpace
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D (W.subspace.ι ≫ p)
      (isGood_integralClosedSubspace D p hp W))

/-- The henselian local ring of an integral closed subspace `W ⊆ X` at the generic point of a
prime divisor of `W` is nontrivial, Noetherian and of Krull dimension at most one. -/
theorem genericHenselianLocalRing_integralClosedSubspace
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor) :
    Nontrivial ↥(P.genericHenselianLocalRing D.site D.base D.base_mem
        (isGood_integralClosedSubspace D p hp W).1 W.isIntegralSpace.2.1) ∧
      IsNoetherianRing ↥(P.genericHenselianLocalRing D.site D.base D.base_mem
        (isGood_integralClosedSubspace D p hp W).1 W.isIntegralSpace.2.1) ∧
      Ring.KrullDimLE 1 ↥(P.genericHenselianLocalRing D.site D.base D.base_mem
        (isGood_integralClosedSubspace D p hp W).1 W.isIntegralSpace.2.1) :=
  have hN := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D (W.subspace.ι ≫ p)
    (isGood_integralClosedSubspace D p hp W)
  ⟨P.nontrivial_genericHenselianLocalRing D.site D.base D.base_mem _ _ W.isIntegralSpace hN,
    P.isNoetherianRing_genericHenselianLocalRing D.site D.base D.base_mem _ _ W.isIntegralSpace hN,
    P.krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem _ _ W.isIntegralSpace hN⟩

/-- The coefficients of the Weil divisor `div_{ℒ|_W}(t_W) = ∑_Z ord_{Z, ℒ|_W}(t_W) [Z]` of the
regular meromorphic section of `ℒ|_W`, indexed by the integral closed subspaces of `W`. -/
def restrictedDivisorCoefficients (hL : IsInvertibleSheaf D p hp L)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor → ℤ :=
  letI := fun P ↦ (genericHenselianLocalRing_integralClosedSubspace D p hp W P).1
  letI := fun P ↦ (genericHenselianLocalRing_integralClosedSubspace D p hp W P).2.1
  letI := fun P ↦ (genericHenselianLocalRing_integralClosedSubspace D p hp W P).2.2
  divisorCycleCoefficients D (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
    W.isIntegralSpace.2.1 (integralClosedSubspaceRestrict D p hp L W)
    (restrictedSectionOfIntegralClosedSubspace D p hp L hL W) (restrictedRatio D p hp L hL W)

/-- The coefficients of `div_{ℒ|_W}(t_W)` form a `k`-cycle on an integral closed subspace
`W ⊆ X` of δ-dimension `k + 1`. -/
theorem restrictedDivisorCoefficients_mem_cyclesOfDimension (hL : IsInvertibleSheaf D p hp L)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) (hW : deltaDimension D p W = k + 1) :
    restrictedDivisorCoefficients D p hp L hL W ∈ cyclesOfDimension D (W.subspace.ι ≫ p) k := by
  let := fun P ↦ (genericHenselianLocalRing_integralClosedSubspace D p hp W P).1
  let := fun P ↦ (genericHenselianLocalRing_integralClosedSubspace D p hp W P).2.1
  let := fun P ↦ (genericHenselianLocalRing_integralClosedSubspace D p hp W P).2.2
  have hWg := isGood_integralClosedSubspace D p hp W
  have hN := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D (W.subspace.ι ≫ p) hWg
  have hLW :=
    isInvertibleModule_integralClosedSubspaceRestrict_of_isInvertibleSheaf D p hp L hL W
  obtain ⟨U, hUopen, hUne, hU⟩ := exists_isOpen_nonempty_genericPoint_mem_compl_of_isUnit
    D.site D.base D.base_mem hWg.1 W.isIntegralSpace.2.1 W.isIntegralSpace hN
    (integralClosedSubspaceRestrict D p hp L W) hLW
    (canonicalRatioIsUnitOnGeneratingChart D.site D.base D.base_mem hWg.1 W.isIntegralSpace.2.1
      W.isIntegralSpace hN _ hLW)
  have hfin := locallyFinite_divisorCoefficients_ne_zero D.site D.base D.base_mem hWg.1
    W.isIntegralSpace.2.1 hN W.isIntegralSpace.irreducibleSpace
    (integralClosedSubspaceRestrict D p hp L W)
    (restrictedSectionOfIntegralClosedSubspace D p hp L hL W)
    (restrictedRatio D p hp L hL W) U hUopen hUne hU
  obtain ⟨d, hd⟩ := exists_dimensionFunction_deltaValue_of_isGood D (W.subspace.ι ≫ p) hWg
  have hn : deltaDimensionClosed D (W.subspace.ι ≫ p) hWg Set.univ isClosed_univ =
      ((k + 1 : ℤ) : EInt) := by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D p hp W, hW]
  rw [restrictedDivisorCoefficients]
  simpa only [add_sub_cancel_right] using
    divisorCycleCoefficients_mem_cyclesOfDimension D (W.subspace.ι ≫ p) hWg
      W.isIntegralSpace.2.1 (integralClosedSubspaceRestrict D p hp L W)
      (restrictedSectionOfIntegralClosedSubspace D p hp L hL W) (restrictedRatio D p hp L hL W)
      hfin W.isIntegralSpace d hd hn

/-- The `k`-cycle `c₁(ℒ|_W) ∩ [W]` on an integral closed subspace `W ⊆ X` of δ-dimension
`k + 1`: the Weil divisor `div_{ℒ|_W}(t_W)` of the regular meromorphic section `t_W` of
`ℒ|_W`. -/
def restrictedDivisorCycle (hL : IsInvertibleSheaf D p hp L)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) (hW : deltaDimension D p W = k + 1) :
    CycleGroup D (W.subspace.ι ≫ p) k :=
  ⟨restrictedDivisorCoefficients D p hp L hL W,
    restrictedDivisorCoefficients_mem_cyclesOfDimension D p hp L k hL W hW⟩

/-- The coefficients of `restrictedDivisorCycle` are `restrictedDivisorCoefficients`. -/
@[simp]
theorem restrictedDivisorCycle_coe (hL : IsInvertibleSheaf D p hp L)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) (hW : deltaDimension D p W = k + 1) :
    (restrictedDivisorCycle D p hp L k hL W hW).1 = restrictedDivisorCoefficients D p hp L hL W :=
  rfl

end Restriction

/-! ### The refined Gysin homomorphism -/

section Gysin

variable (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections) (k : ℤ)

/-- The component rule of the refined Gysin homomorphism of `(ℒ, s)`: the cycle `[E ∩ W]_k` of the
scheme-theoretic intersection for `W ⊄ E`, and the cycle `c₁(ℒ|_W) ∩ [W] = div_{ℒ|_W}(t_W)` on
`W` for `W ⊆ E`. -/
def sectionGysinRule (hL : IsInvertibleSheaf D p hp L) :
    GysinComponentRule D p (vanishingLocus D p hp L s) k :=
  canonicalGysinComponentRule D p hp (vanishingLocus D p hp L s)
    (isGood_vanishingLocus D p hp L s) k (restrictedDivisorCycle D p hp L k hL)

/-- The *refined Gysin homomorphism* `i^* : Z_{k+1}(X) ⟶ CH_k(E)` of the vanishing locus
`E = Z(s)` of a global section `s` of an invertible sheaf `ℒ` on a good algebraic space `X/B`,
`i : E → X` the closed immersion, with values in the Chow group `CH_k(E) = Z_k(E)/∼_rat`.

On the cycle `[W]` of an integral closed subspace `W ⊆ X` of δ-dimension `k + 1` it is the class
of `[E ∩ W]_k` when `W ⊄ E` (`AlgebraicGeometry.Space.sectionRefinedGysin_integralCycle_of_not_le`)
and the class of `i'_*(c₁(ℒ|_W) ∩ [W])` when `W ⊆ E`
(`AlgebraicGeometry.Space.sectionRefinedGysin_integralCycle_of_le`); on a general cycle
`α = ∑ n_W [W]` it is the class of `∑ n_W i^*[W]`
(`AlgebraicGeometry.Space.sectionRefinedGysin_apply`). -/
@[stacks 0ER1 "parts (1)(a), (1)(b) and (2): the refined Gysin homomorphism \
i^* : Z_{k+1}(X) → CH_k(D) of the vanishing locus D = Z(s) of a global section of an invertible \
sheaf, with values in CH_k(D) = Z_k(D)/∼_rat of Stacks 0EQ6, clause (1)(a) the cycle [D ∩ W]_k \
of Stacks 0EE9 of the scheme-theoretic intersection and clause (1)(b) the pushforward of \
div_{L|_W}(t_W) for the regular meromorphic section of Stacks 0EPQ, every ingredient constructed"]
def sectionRefinedGysin (hL : IsInvertibleSheaf D p hp L) :
    CycleGroup D p (k + 1) →+
      chowGroup.{v} D ((vanishingLocus D p hp L s).1.ι ≫ p)
        (isGood_vanishingLocus D p hp L s) k :=
  refinedGysin D p hp L s k (isGood_vanishingLocus D p hp L s) hL
    (sectionGysinRule D p hp L s k hL)
    (chowTarget.{v} D ((vanishingLocus D p hp L s).1.ι ≫ p)
      (isGood_vanishingLocus D p hp L s) k)

/-- For an integral closed subspace `W ⊆ X` of δ-dimension `k + 1` with `W ⊄ E`, `i^*[W]` is the
class of the cycle `[E ∩ W]_k` of the scheme-theoretic intersection `E ∩ W`. -/
theorem sectionRefinedGysin_integralCycle_of_not_le (hL : IsInvertibleSheaf D p hp L)
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1)
    (hWE : ¬ W.subspace ≤ (vanishingLocus D p hp L s).1) :
    sectionRefinedGysin.{v} D p hp L s k hL (integralCycle D p (k + 1) W hW) =
      chowClass.{v} D ((vanishingLocus D p hp L s).1.ι ≫ p)
        (isGood_vanishingLocus D p hp L s) k
        (gysinIntersectionCycle D p hp (vanishingLocus D p hp L s)
          (isGood_vanishingLocus D p hp L s) k W hW hWE) :=
  refinedGysin_integralCycle_of_not_le D p hp L s k (isGood_vanishingLocus D p hp L s) hL _ _
    hW hWE

/-- For an integral closed subspace `W ⊆ E` of δ-dimension `k + 1`, `i^*[W]` is the class of
`i'_*(c₁(ℒ|_W) ∩ [W])`, for the induced closed immersion `i' : W → E`, the inner cycle being the
Weil divisor `div_{ℒ|_W}(t_W)`. -/
theorem sectionRefinedGysin_integralCycle_of_le (hL : IsInvertibleSheaf D p hp L)
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1)
    (hWE : W.subspace ≤ (vanishingLocus D p hp L s).1) :
    sectionRefinedGysin.{v} D p hp L s k hL (integralCycle D p (k + 1) W hW) =
      chowClass.{v} D ((vanishingLocus D p hp L s).1.ι ≫ p)
        (isGood_vanishingLocus D p hp L s) k
        (containedPushforward D p (vanishingLocus D p hp L s)
          (isGood_vanishingLocus D p hp L s) k hWE (restrictedDivisorCycle D p hp L k hL W hW)) :=
  refinedGysin_integralCycle_of_le D p hp L s k (isGood_vanishingLocus D p hp L s) hL _ _ hW hWE

/-- For a general `(k+1)`-cycle `α = ∑ n_W [W]`, `i^* α` is the class of the
cycle `∑ n_W i^*[W]`, whose coefficient at an integral closed subspace `Z ⊆ E` is the (finite)
sum `∑_W n_W · (i^*[W])_Z` of the coefficients of the component cycles. -/
theorem sectionRefinedGysin_apply (hL : IsInvertibleSheaf D p hp L)
    (α : CycleGroup D p (k + 1)) :
    sectionRefinedGysin.{v} D p hp L s k hL α =
      chowClass.{v} D ((vanishingLocus D p hp L s).1.ι ≫ p)
        (isGood_vanishingLocus D p hp L s) k
        (gysinCycleMap D p (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s) k
          (sectionGysinRule D p hp L s k hL) α) ∧
    ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem (vanishingLocus D p hp L s).1.toFunctor,
      (gysinCycleMap D p (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s) k
          (sectionGysinRule D p hp L s k hL) α).1 Z =
        ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X,
          α.1 W * (gysinComponentCycle D p (vanishingLocus D p hp L s)
            (isGood_vanishingLocus D p hp L s) k (sectionGysinRule D p hp L s k hL) W).1 Z :=
  ⟨rfl, fun Z ↦ gysinCycleMap_apply D p (vanishingLocus D p hp L s)
    (isGood_vanishingLocus D p hp L s) k (sectionGysinRule D p hp L s k hL) α Z⟩

/-- Intersecting with an effective Cartier divisor: when `E = Z(s)` is an effective Cartier
divisor on `X`, the operation `E · α = i_* i^* α` with values in the Chow group `CH_k(X)`, `i_*`
being the pushforward along the closed immersion
`i : E → X` of the cycle `∑ n_W i^*[W]` representing `i^* α`. -/
@[stacks 0ER1 "part (3): the operation D · α = i_* i^* α of an effective Cartier divisor \
D = Z(s), with values in CH_k(X) = Z_k(X)/∼_rat of Stacks 0EQ6, i^* the refined Gysin \
homomorphism of parts (1) and (2) with every ingredient constructed, and i_* the pushforward \
along the closed immersion i : D → X of the cycle representing i^* α"]
def sectionCartierIntersection (hL : IsInvertibleSheaf D p hp L)
    (hCartier : IsEffectiveCartierDivisor D.site D.base D.base_mem ⟨X, hp.1⟩
      (vanishingLocus D p hp L s)) :
    CycleGroup D p (k + 1) →+ chowGroup.{v} D p hp k :=
  effectiveCartierIntersection D p hp L s k (isGood_vanishingLocus D p hp L s) hL hCartier
    (sectionGysinRule D p hp L s k hL) (chowTarget.{v} D p hp k)

/-- `E · α` is the class in `CH_k(X)` of the pushforward along
`i : E → X` of the cycle `∑ n_W i^*[W]` whose class is `i^* α`. -/
theorem sectionCartierIntersection_apply (hL : IsInvertibleSheaf D p hp L)
    (hCartier : IsEffectiveCartierDivisor D.site D.base D.base_mem ⟨X, hp.1⟩
      (vanishingLocus D p hp L s))
    (α : CycleGroup D p (k + 1)) :
    sectionCartierIntersection.{v} D p hp L s k hL hCartier α =
      chowClass.{v} D p hp k
        (cycleGroupClosedPushforward D hp.1 (vanishingLocus D p hp L s).2.1
          (D.isDecentSpace_of_isGood p hp) (vanishingLocus D p hp L s).2.2 p hp.2.2
          ((vanishingLocus D p hp L s).1.ι ≫ p) rfl k
          (gysinCycleMap D p (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s) k
            (sectionGysinRule D p hp L s k hL) α)) :=
  rfl

end Gysin

end AlgebraicGeometry.Space

end
