module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernClassCapAdditive
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.JacobsonDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaCycleIdentities
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralCodimensionZeroHypotheses
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularMeromorphicSectionExistence

/-!
# The component cycle of Section 0EQU is the restricted divisor `div_{𝒩|W}(t_W)`

In Situation 0EDT let `X/B` be good and integral with `dim_δ(X) = n`, let `ℒ` and `𝒩` be
`𝒪_X`-modules, let `s` be a nonzero meromorphic section of `ℒ` and let `{Z_i}`, `i ∈ I`, be a
locally finite family of prime divisors of `X` containing every prime divisor along which `s` has
nonzero order of vanishing.  Section 0EQU displays the identity

`c₁(𝒩) ∩ div_ℒ(s) = ∑_i ord_{Z_i,ℒ}(s) · (Z_i → X)_* div_{𝒩|Z_i}(t_i|Z_i)`

in `Z_{n-2}(X)`, where `t_i|Z_i` is the reduction of a chosen generator of `𝒩_{ξ_i}` to the fibre
at the generic point `ξ_i` of `Z_i`.

`AlgebraicGeometry.Space.firstChernCapCycleMap_divisorCycleAt_eq_cycleFamilySum` proves that
identity with the component cycle `c₁(𝒩|_{Z_i}) ∩ [Z_i]` an arbitrary
`AlgebraicGeometry.Space.FirstChernComponentCycleRule`, that is as the carried parameter of
Stacks 0EQJ.  This module removes that parameter: it builds the component rule, at every integral
closed subspace `W ⊆ X` of δ-dimension `k + 1`, as the Weil divisor `div_{𝒩|_W}(t_W)` of a
meromorphic section `t_W` of the restriction `𝒩|_W` — Stacks 0EQE part (1) applied on `W` — and
restates the identity for that rule.

## Main definitions

* `AlgebraicGeometry.Space.componentDivisorCycleRule`: the component rule of Stacks 0EQJ whose
  value at `W` is the cycle `div_{𝒩|_W}(t_W)` of Stacks 0EQE part (1) on `W`.
* `AlgebraicGeometry.Space.componentMeromorphicSection`: the meromorphic section `t_W` of `𝒩|_W`
  that rule takes, for `𝒩` invertible, constructed as a regular meromorphic section by Stacks
  0EPQ on `W`.
* `AlgebraicGeometry.Space.divisorSupport`: the prime divisors of `X` along which `s` has nonzero
  order of vanishing, indexing the smallest family Section 0EQU may be taken over.

## Main results

* `AlgebraicGeometry.Space.deltaDimensionClosed_univ_integralClosedSubspace`: the δ-dimension of
  an integral closed subspace `W ⊆ X`, computed on `W` as a good algebraic space over the base,
  is its δ-dimension as a subspace of `X`.  This is what lets Stacks 0EQE be applied on `W` with
  the grading the cap product of Stacks 0EQJ demands.
* `AlgebraicGeometry.Space.isDivisorPresentation_componentDivisorCycleRule`: that rule is
  presented by Weil divisors in the sense of
  `AlgebraicGeometry.Space.IsDivisorPresentation`, so Stacks 0EQK applies to it.
* `AlgebraicGeometry.Space.firstChernCapCycleMap_divisorCycleAt_eq_componentDivisorSum`:
  **Stacks 0EQU**, either cycle identity of the section preceding the key formula, with the
  component cycle `div_{𝒩|Z_i}(t_i|Z_i)` constructed rather than assumed.
* `AlgebraicGeometry.Space.locallyFinite_subspacePointSet_divisorSupport`: the point sets of the
  prime divisors of nonzero order are locally finite, from Stacks 0EPS.
* `firstChernCapCycleMap_divisorCycleAt_eq_componentDivisorSum_divisorSupport`:
  the same identity for the family of *all* prime divisors of nonzero order, where injectivity of
  the family, its covering property and the δ-dimension of its members are theorems, so that the
  only local finiteness left on `X` is the one of Stacks 0EPS for `(ℒ, s)`.
* `AlgebraicGeometry.Space.exists_isRegularMeromorphicSection_integralClosedSubspaceRestrict`:
  Stacks 0EPQ on an integral closed subspace `W ⊆ X`, at the hypotheses of Situation 0EDT: the
  restriction `𝒩|_W` of an invertible module has a regular meromorphic section.
* `firstChernCapCycleMap_divisorCycleAt_eq_componentDivisorSum_of_isInvertible`
  and
  `firstChernCapCycleMap_divisorCycleAt_eq_componentDivisorSum_divisorSupport_of_isInvertible`:
  **Stacks 0EQU for an invertible `𝒩`**, with the meromorphic section `t_W` and the dimension
  function on each `W` produced rather than carried.

## What is carried, and what is not

The component cycle is no longer a parameter: it is the Weil divisor of Stacks 0EQE part (1) of
the meromorphic section `t_W` of `𝒩|_W`, where `𝒩|_W` is the inverse image of `𝒩` of Stacks 03LU
along the closed immersion `W → X`, that is
`AlgebraicGeometry.Space.integralClosedSubspaceRestrict`.  What the construction takes instead is
the input Stacks 0EQE itself takes, on `W` rather than on `X`:

* the meromorphic section `t_W` of `𝒩|_W`;
* the choice of a generator at the generic point of each prime divisor of `W`, read off as the
  ratio family `ratioN` of Stacks 0EPR, exactly as Stacks 0EQE carries it on `X`;
* local finiteness of the prime divisors of `W` with nonzero order, Stacks 0EPS on `W`, exactly
  as Stacks 0EQE carries it on `X`;
* the dimension function of Situation 0EDT on `W`, Stacks 0EDN, exactly as Stacks 0EQE carries it
  on `X`.

For `𝒩` **invertible**, which is Section 0EQU's own hypothesis on `𝒩`, the first and the last of
those four are discharged here, so that only the pair `ratioN`, `hfinN` of Stacks 0EPR and 0EPS
remains:

* `t_W` is `AlgebraicGeometry.Space.componentMeromorphicSection`, a regular meromorphic section
  of `𝒩|_W` produced by Stacks 0EPQ on `W`.  Its three hypotheses are conditions (a), (b) and
  (c) of Stacks 0ENA, all theorems at the hypotheses of Situation 0EDT: (a) and (c) because `W`
  is integral, hence reduced and decent, and (b) because `W`, being locally of finite type over a
  locally Noetherian base, is locally Noetherian by Stacks 04ZK.  The source's own value at
  `W = Z_i` is the reduction `t_i|Z_i` of a chosen generator of `𝒩_{ξ_i}` to the fibre
  `𝒩_{ξ_i} ⊗_{B_i} κ(ξ_i)`, which `AlgebraicGeometry.Space.PrimeDivisor.genericFibreReduction`
  constructs and `AlgebraicGeometry.Space.PrimeDivisor.genericFibreReduction_ne_zero` shows to be
  nonzero; reading *that* element as a meromorphic section of `𝒩|_{Z_i}` is the sheaf-level half
  of Stacks 0EN0, which this library does not have — but the identity does not need it, since the
  component cycle is a parameter of Stacks 0EQJ on both of its sides and any nonzero meromorphic
  section of `𝒩|_W` will do;
* the dimension function on `W` is
  `AlgebraicGeometry.Space.subspaceDeltaDimensionFunction`, the one on `X` pulled back along the
  closed embedding `|W| → |X|`, which is a dimension function because
  an intermediate point of a specialization starting in a closed set lies in that closed set.
  So Stacks 0EDN is carried once, on `X`, instead of once for every `W`.

The pair that remains is blocked by the same thing: `AlgebraicGeometry.Space.LocalRatio` is an
unconstrained function type, so a ratio family is not required to be `s ↦ s / s_ξ` for a
generator `s_ξ`, the order of vanishing it computes is arbitrary, and the set of prime divisors
of `W` of nonzero order is uncontrolled.  The *first* set of Stacks 0EPS, which does not mention
the ratio, is proved and does apply to `t_W`, which is regular:
`AlgebraicGeometry.Space.locallyFinite_primeDivisor_not_memGenericModuleStalk_of_isIntegral`.

The hypotheses of Stacks 0ENK on the henselian local rings at the generic points of the prime
divisors of each `W` are the ones `AlgebraicGeometry.Space.SubspaceDivisorSetup` already bundles.

## References

* [Stacks Project, Section 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
* [Stacks Project, Tag 0EN0](https://stacks.math.columbia.edu/tag/0EN0)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0EPQ](https://stacks.math.columbia.edu/tag/0EPQ)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
* [Stacks Project, Tag 0EPZ](https://stacks.math.columbia.edu/tag/0EPZ)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u z v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The δ-dimension of an integral closed subspace, computed on the subspace -/

section DeltaDimension

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)

/-- The δ-dimension of an integral closed subspace `W ⊆ X`, computed on `W` itself as a good
integral algebraic space over the base, is its δ-dimension as a subspace of `X`.

Both are the value of `δ` at a generic point: on `W` because `|W|` is irreducible, and on `X` by
definition of the δ-dimension of an integral closed subspace.  The two values agree because the
closed immersion `W → X` is an immersion, hence locally quasi-finite by Stacks 03XM, and the
dimension function of Situation 0EDT does not change along a locally quasi-finite morphism. -/
theorem deltaDimensionClosed_univ_integralClosedSubspace
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    deltaDimensionClosed D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
        Set.univ isClosed_univ = ((deltaDimension D sX W : ℤ) : EInt) := by
  rw [deltaDimensionClosed_univ_eq_deltaValue_genericPoint D (W.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace,
    D.deltaValue_comp_of_isLocallyQuasiFinite (isGood_integralClosedSubspace D sX hX W).1 hX.1
      W.subspace.ι sX
      (isLocallyQuasiFinite_of_isImmersion D.site D.base D.base_mem W.subspace.ι
        (isImmersion_of_isClosedImmersion D.site D.base D.base_mem W.isClosedSubspace.2))
      hX.2.2]
  rfl

end DeltaDimension

/-! ### The component rule given by the restricted divisors -/

section ComponentRule

variable {D : BaseSpaceDimensionSituation.{u}}
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (setup : SubspaceDivisorSetup D X)
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1) (k : ℤ)

/-- **Stacks 0EQE part (1) as the component rule of Stacks 0EQJ.** The `k`-cycle attached to an
integral closed subspace `W ⊆ X` of δ-dimension `k + 1` is the Weil divisor
`div_{𝒩|_W}(t_W) = ∑_P ord_{P,𝒩|_W}(t_W) [P]` of a meromorphic section `t_W` of the restriction
`𝒩|_W`, read in `Z_k(W)`.

This is the component cycle `c₁(𝒩|_W) ∩ [W]` of Stacks 0EQJ, *constructed* and not carried: at
`W = Z_i` it is the source's `div_{𝒩|Z_i}(t_i|Z_i)`.  The grading is right because the
δ-dimension of `W` computed on `W` is `k + 1` by
`AlgebraicGeometry.Space.deltaDimensionClosed_univ_integralClosedSubspace`, so Stacks 0EQE part
(1) on `W` lands in `Z_{(k+1)-1}(W) = Z_k(W)`.

The inputs are the ones Stacks 0EQE takes on `X`, here on each `W`: the section `t_W`, the ratio
family `ratio W` of Stacks 0EPR, the local finiteness `hfin W` of Stacks 0EPS and the dimension
function `dim W` of Stacks 0EDN. -/
def componentDivisorCycleRule
    (t : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
        (setup.isSpace W) (integralClosedSubspaceRestrict D sX hX N W))
    (ratio : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      LocalRatioFamily.{u, u} D.site D.base D.base_mem (setup.isSpace W) (setup.isDecent W)
        (integralClosedSubspaceRestrict D sX hX N W))
    (dim : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      DimensionFunction (points D.site D.base D.base_mem W.subspace.toFunctor))
    (hdim : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (x : points D.site D.base D.base_mem W.subspace.toFunctor),
      dim W x = D.deltaValue (W.subspace.ι ≫ sX) x)
    (hfin : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      LocallyFinite fun P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor =>
        if setup.sectionOrder W (integralClosedSubspaceRestrict D sX hX N W) (t W) (ratio W) P = 0
          then ∅ else P.support D.site D.base D.base_mem W.subspace.toFunctor) :
    FirstChernComponentCycleRule D sX k := fun W hW =>
  haveI := setup.nontrivial W
  haveI := setup.noetherian W
  haveI := setup.krullDimLE W
  ⟨divisorCycleCoefficients D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
      (setup.isDecent W) (integralClosedSubspaceRestrict D sX hX N W) (t W) (ratio W), by
    have hn : deltaDimensionClosed D (W.subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX W) Set.univ isClosed_univ =
        ((k + 1 : ℤ) : EInt) := by
      rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX W, hW]
    have hmem := divisorCycleCoefficients_mem_cyclesOfDimension D (W.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX W) (setup.isDecent W)
      (integralClosedSubspaceRestrict D sX hX N W) (t W) (ratio W) (hfin W)
      W.isIntegralSpace (dim W) (hdim W) hn
    simpa only [add_sub_cancel_right] using hmem⟩

variable (t : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
        (setup.isSpace W) (integralClosedSubspaceRestrict D sX hX N W))
    (ratio : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      LocalRatioFamily.{u, u} D.site D.base D.base_mem (setup.isSpace W) (setup.isDecent W)
        (integralClosedSubspaceRestrict D sX hX N W))
    (dim : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      DimensionFunction (points D.site D.base D.base_mem W.subspace.toFunctor))
    (hdim : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (x : points D.site D.base D.base_mem W.subspace.toFunctor),
      dim W x = D.deltaValue (W.subspace.ι ≫ sX) x)
    (hfin : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      LocallyFinite fun P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor =>
        if setup.sectionOrder W (integralClosedSubspaceRestrict D sX hX N W) (t W) (ratio W) P = 0
          then ∅ else P.support D.site D.base D.base_mem W.subspace.toFunctor)

/-- **Stacks 0EQE part (1) presents the component rule above.** The cycle attached to `W` has
coefficient `ord_{P,𝒩|_W}(t_W)` at a prime divisor `P` of `W` and vanishes at an integral closed
subspace of `W` underlying no prime divisor.

This is `AlgebraicGeometry.Space.IsDivisorPresentation`, the property Stacks 0EQK assumes of a
component rule; for this rule it is a theorem. -/
theorem isDivisorPresentation_componentDivisorCycleRule
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D sX W = k + 1) :
    IsDivisorPresentation sX k setup W
      (componentDivisorCycleRule sX hX setup N k t ratio dim hdim hfin W hW)
      (integralClosedSubspaceRestrict D sX hX N W) (t W) (ratio W) := by
  have := setup.nontrivial W
  have := setup.noetherian W
  have := setup.krullDimLE W
  refine ⟨fun P => ?_, fun Z hZ => ?_⟩
  · exact divisorCycleCoefficients_toIntegralClosedSubspace D (W.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX W) (setup.isDecent W)
      (integralClosedSubspaceRestrict D sX hX N W) (t W) (ratio W) P
  · by_cases hcod : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem
        (isGood_integralClosedSubspace D sX hX W).1 Z) = 1
    · exact absurd (IntegralClosedSubspace.toIntegralClosedSubspace_toPrimeDivisor
        D.site D.base D.base_mem (isGood_integralClosedSubspace D sX hX W).1 Z hcod)
        (hZ (Z.toPrimeDivisor D.site D.base D.base_mem
          (isGood_integralClosedSubspace D sX hX W).1 hcod))
    · exact divisorCycleCoefficients_of_codimension_ne_one D (W.subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX W) (setup.isDecent W)
        (integralClosedSubspaceRestrict D sX hX N W) (t W) (ratio W) hcod

end ComponentRule

/-! ### The meromorphic section on each component, produced rather than carried -/

section ComponentSection

variable {D : BaseSpaceDimensionSituation.{u}}
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (setup : SubspaceDivisorSetup D X)
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)

include hX in
/-- **An integral closed subspace of a good algebraic space over the base is locally
Noetherian.**  It is locally of finite type over the base, which is locally Noetherian by
Situation 0EDT, so Stacks 04ZK applies. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_integralClosedSubspace
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    HasEtaleLocalProperty D.site D.base D.base_mem W.subspace.toFunctor
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
  isLocallyNoetherian_of_isLocallyOfFiniteType D.site D.base D.base_mem
    (isGood_integralClosedSubspace D sX hX W).1 D.isAlgebraicSpace (W.subspace.ι ≫ sX)
    (isGood_integralClosedSubspace D sX hX W).2.2 D.locallyNoetherian

/-- **The restriction `𝒩|_W` of an invertible module to an integral closed subspace has a
regular meromorphic section.**  This is Stacks 0EPQ on `W`, whose three hypotheses — conditions
(a), (b) and (c) of Stacks 0ENA — are theorems here: (a) and (c) because `W` is integral, hence
reduced and decent, and (b) because `W` is locally Noetherian, being locally of finite type over
the base of Situation 0EDT.  Invertibility of `𝒩|_W` is invertibility of `𝒩` by Stacks 0B8P.

This is the meromorphic section `t_W` of `𝒩|_W` that Stacks 0EQE takes on `W`, *produced*
instead of assumed.  The source's value at `W = Z_i` is the reduction `t_i|Z_i` of a chosen
generator of `𝒩_{ξ_i}`, which is one such section; the cycle identity of Section 0EQU holds for
any of them, the component cycle being a parameter of Stacks 0EQJ on both of its sides. -/
theorem exists_isRegularMeromorphicSection_integralClosedSubspaceRestrict
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    ∃ t : MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
        (setup.isSpace W) (integralClosedSubspaceRestrict D sX hX N W),
      IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
        (setup.isSpace W) (integralClosedSubspaceRestrict D sX hX N W) t :=
  exists_isRegularMeromorphicSection_of_isTrivialAtCodimensionZeroPoints
    (setup.isSpace W)
    (forall_localRingDimension_eq_zero_of_isIntegralSpace D.site D.base D.base_mem
      ⟨W.subspace.toFunctor, setup.isSpace W⟩ W.isIntegralSpace)
    (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian D.site D.base D.base_mem
      (hF := setup.isSpace W)
      (hN := hasEtaleLocalProperty_isLocallyNoetherian_integralClosedSubspace sX hX W))
    (hasMonomorphicCodimensionZeroPoints_of_isIntegralSpace D.site D.base D.base_mem
      W.isIntegralSpace)
    (integralClosedSubspaceRestrict D sX hX N W)
    (modulePullbackInvertible
      (closedSubspaceHom D.site D.base D.base_mem hX.1 W.subspace W.isClosedSubspace) N hN)

/-- **The meromorphic section `t_W` of `𝒩|_W` that Stacks 0EQE takes on each integral closed
subspace `W ⊆ X`**, chosen among the regular ones produced by Stacks 0EPQ on `W`.  With it the
component rule of Stacks 0EQJ carries no meromorphic section; see
`AlgebraicGeometry.Space.exists_isRegularMeromorphicSection_integralClosedSubspaceRestrict`. -/
def componentMeromorphicSection
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (setup.isSpace W) (integralClosedSubspaceRestrict D sX hX N W) :=
  (exists_isRegularMeromorphicSection_integralClosedSubspaceRestrict sX hX setup N hN W).choose

/-- The chosen meromorphic section of `𝒩|_W` is regular, which is Stacks 0ENB for it. -/
theorem isRegularMeromorphicSection_componentMeromorphicSection
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (setup.isSpace W) (integralClosedSubspaceRestrict D sX hX N W)
      (componentMeromorphicSection sX hX setup N hN W) :=
  (exists_isRegularMeromorphicSection_integralClosedSubspaceRestrict sX hX setup N
    hN W).choose_spec

end ComponentSection

/-! ### The cycle identity of Section 0EQU with the component cycle constructed -/

section CycleIdentity

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (hdec : IsDecentSpace D.site D.base D.base_mem X)
variable [∀ W : PrimeDivisor D.site D.base D.base_mem X,
  Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdec)]
variable [∀ W : PrimeDivisor D.site D.base D.base_mem X,
  IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdec)]
variable [∀ W : PrimeDivisor D.site D.base D.base_mem X,
  Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdec)]
variable (setup : SubspaceDivisorSetup D X)
    (L : Modules.{u, max u z} D.site D.base D.base_mem X hX.1)
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)

/-- **Stacks 0EQU: either cycle identity of the section preceding the key formula, with the
component cycle `div_{𝒩|Z_i}(t_i|Z_i)` constructed and not assumed.**  In Situation 0EDT let
`X/B` be good and integral with `dim_δ(X) = n`, let `ℒ` and `𝒩` be `𝒪_X`-modules, let `s` be a
nonzero meromorphic section of `ℒ`, and let `{Z_i}`, `i ∈ I`, be an injective locally finite
family of prime divisors of `X` containing every prime divisor along which `s` has nonzero order
of vanishing.  Then

`c₁(𝒩) ∩ div_ℒ(s) = ∑_i ord_{Z_i,ℒ}(s) · (Z_i → X)_* div_{𝒩|Z_i}(t_i|Z_i)`

in `Z_{n-2}(X)`, the component cycle `c₁(𝒩|_{Z_i}) ∩ [Z_i]` being the Weil divisor
`div_{𝒩|Z_i}(t_i|Z_i)` of Stacks 0EQE part (1) on `Z_i`, that is
`AlgebraicGeometry.Space.componentDivisorCycleRule`.  The two identities displayed in Section
0EQU before the key formula are the two instances of this statement, exchanging `(ℒ, s)` with
`(𝒩, t)` and `𝒩` with `ℒ`.

The orders `ord_{Z_i,ℒ}(s)` are those of Stacks 0EPR, which the source identifies with its
`ord_{B_i}(f_i)`; the δ-dimension hypothesis `hdim` is Stacks 0EPZ, proved as
`AlgebraicGeometry.Space.deltaDimension_toIntegralClosedSubspace`.

This statement takes, as inputs on each `W`, exactly what Stacks 0EQE takes on `X`: the
meromorphic section `t W` of `𝒩|_W`, which at `W = Z_i` is the source's reduction `t_i|Z_i`
(`AlgebraicGeometry.Space.PrimeDivisor.genericFibreReduction`, read through Stacks 0EN0); the
ratio family `ratioN` of Stacks 0EPR; the local finiteness `hfinN` of Stacks 0EPS; and the
dimension function `dimN` of Stacks 0EDN.  The same four, on `X`, are `ratio`, `hfin`, `d` and
`hd` here.  Two of those four are no longer needed once `𝒩` is invertible, which is Section
0EQU's own hypothesis on `𝒩`:
`firstChernCapCycleMap_divisorCycleAt_eq_componentDivisorSum_of_isInvertible`
is this identity with `t` produced by Stacks 0EPQ on `W` and with `dimN` derived from `d`.  This
version is kept because it needs no hypothesis on `𝒩` at all.

The key formula itself, Stacks 0EQV, **is** proved, unconditionally and axiom-clean:
`AlgebraicGeometry.Space.keyFormula_of_ne_zero` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Headline`, at the canonical choices and
for the constructed tame-symbol sum, from which Stacks 0EQX follows there as
`AlgebraicGeometry.Space.canonicalFirstChernCap_divisor_comm`.  What is still open is only the
*predicate* `AlgebraicGeometry.Space.KeyFormula` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaCycleIdentities`, which quantifies the
component rules of Stacks 0EQJ and the principal divisors of the tame symbols; at that generality
it is not a theorem of this library. -/
@[stacks 0EQU "either cycle identity of the section, \
c_1(N) ∩ div_L(s) = ∑ ord_{B_i}(f_i) (Z_i → X)_* div_{N|Z_i}(t_i|Z_i) in Z_{n-2}(X), with the \
component cycle no longer a parameter: it is the Weil divisor div_{N|W}(t_W) of Stacks 0EQE \
part (1) on W, for the restriction N|W of Stacks 03LU. N is arbitrary here, and what is then \
carried on W is what Stacks 0EQE carries on X: the meromorphic section t W, the Stacks 0EPR \
ratio family, the Stacks 0EPS local finiteness and the Stacks 0EDN dimension function. For N \
invertible, which is the section's own hypothesis, t W and the dimension function are produced \
and not carried, see \
firstChernCapCycleMap_divisorCycleAt_eq_componentDivisorSum_of_isInvertible. hdim is Stacks \
0EPZ. The key formula 0EQV IS proved, unconditionally and axiom-clean, as keyFormula_of_ne_zero \
of StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Headline, and 0EQX follows there as \
canonicalFirstChernCap_divisor_comm; what is still open is only the quantified predicate \
KeyFormula of KeyFormulaCycleIdentities, which ranges over the component rules of 0EQJ and the \
tame-symbol divisors"]
theorem firstChernCapCycleMap_divisorCycleAt_eq_componentDivisorSum
    {k : ℤ} {I : Type v}
    (t : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
        (setup.isSpace W) (integralClosedSubspaceRestrict D sX hX N W))
    (ratioN : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      LocalRatioFamily.{u, u} D.site D.base D.base_mem (setup.isSpace W) (setup.isDecent W)
        (integralClosedSubspaceRestrict D sX hX N W))
    (dimN : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      DimensionFunction (points D.site D.base D.base_mem W.subspace.toFunctor))
    (hdimN : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (x : points D.site D.base D.base_mem W.subspace.toFunctor),
      dimN W x = D.deltaValue (W.subspace.ι ≫ sX) x)
    (hfinN : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      LocallyFinite fun P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor =>
        if setup.sectionOrder W (integralClosedSubspaceRestrict D sX hX N W) (t W) (ratioN W) P = 0
          then ∅ else P.support D.site D.base D.base_mem W.subspace.toFunctor)
    (s : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 L)
    (ratio : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec L)
    (hfin : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec L s ratio W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (d : DimensionFunction (points D.site D.base D.base_mem X))
    (hd : ∀ x, d x = D.deltaValue sX x) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (hk : k + 1 = n - 1)
    (Z : I → PrimeDivisor D.site D.base D.base_mem X)
    (hZinj : Function.Injective Z)
    (hZfin : LocallyFinite fun i : I =>
      subspacePointSet D.site D.base D.base_mem X (Z i).subspace)
    (hdim : ∀ i, deltaDimension D sX
      ((Z i).toIntegralClosedSubspace D.site D.base D.base_mem) = k + 1)
    (hcover : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
      divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec L s ratio W ≠ 0 →
        ∃ i, Z i = W) :
    firstChernCapCycleMap D sX hX k
        (componentDivisorCycleRule sX hX setup N k t ratioN dimN hdimN hfinN)
        (divisorCycleAt.{u, z} D sX hX hdec L s ratio hfin hint d hd hn hk) =
      cycleFamilySum D sX hX
        (fun i => (Z i).toIntegralClosedSubspace D.site D.base D.base_mem) hZfin k
        (fun i => orderOfVanishingSection.{u, z} D.site D.base D.base_mem hX.1 hdec (Z i) L s
          (ratio (Z i)) •
            componentDivisorCycleRule sX hX setup N k t ratioN dimN hdimN hfinN
              ((Z i).toIntegralClosedSubspace D.site D.base D.base_mem) (hdim i)) :=
  firstChernCapCycleMap_divisorCycleAt_eq_cycleFamilySum.{u, z} D sX hX hdec L
    (componentDivisorCycleRule sX hX setup N k t ratioN dimN hdimN hfinN) s ratio hfin hint d hd
    hn hk Z hZinj hZfin hdim hcover

/-! ### The identity over the prime divisors of nonzero order -/

/-- The prime divisors of `X` along which `s` has nonzero order of vanishing, indexing the
smallest family Section 0EQU may be taken over. -/
abbrev divisorSupport (s : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 L)
    (ratio : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec L) : Type (u + 1) :=
  {W : PrimeDivisor D.site D.base D.base_mem X //
    divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec L s ratio W ≠ 0}

/-- The point sets of the prime divisors along which `s` has nonzero order of vanishing are
locally finite, that being exactly what Stacks 0EPS says of them: the collection indexed by all
prime divisors, with the empty set at those of zero order, is locally finite, and the subfamily
indexed by those of nonzero order has the same members. -/
theorem locallyFinite_subspacePointSet_divisorSupport
    (s : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 L)
    (ratio : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec L)
    (hfin : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec L s ratio W = 0 then ∅
      else W.support D.site D.base D.base_mem X) :
    LocallyFinite fun i : divisorSupport.{u, z} D sX hX hdec L s ratio =>
      subspacePointSet D.site D.base D.base_mem X (i.1).subspace := by
  refine (hfin.comp_injective Subtype.val_injective).subset fun i => ?_
  simp [i.2]

/-- **Stacks 0EQU over the prime divisors of nonzero order.**  The cycle identity of Section 0EQU
for the smallest family it may be taken over: the prime divisors along which `s` has nonzero order
of vanishing.  For that family the hypotheses that it be injective, that it cover every prime
divisor of nonzero order, and that its members have δ-dimension `k + 1` are all theorems — the
last by Stacks 0EPZ — so the only remaining local finiteness on `X` is `hfin`, which is Stacks
0EPS for `(ℒ, s)`. -/
theorem firstChernCapCycleMap_divisorCycleAt_eq_componentDivisorSum_divisorSupport
    {k : ℤ}
    (t : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
        (setup.isSpace W) (integralClosedSubspaceRestrict D sX hX N W))
    (ratioN : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      LocalRatioFamily.{u, u} D.site D.base D.base_mem (setup.isSpace W) (setup.isDecent W)
        (integralClosedSubspaceRestrict D sX hX N W))
    (dimN : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      DimensionFunction (points D.site D.base D.base_mem W.subspace.toFunctor))
    (hdimN : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (x : points D.site D.base D.base_mem W.subspace.toFunctor),
      dimN W x = D.deltaValue (W.subspace.ι ≫ sX) x)
    (hfinN : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      LocallyFinite fun P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor =>
        if setup.sectionOrder W (integralClosedSubspaceRestrict D sX hX N W) (t W) (ratioN W) P = 0
          then ∅ else P.support D.site D.base D.base_mem W.subspace.toFunctor)
    (s : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 L)
    (ratio : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec L)
    (hfin : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec L s ratio W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (d : DimensionFunction (points D.site D.base D.base_mem X))
    (hd : ∀ x, d x = D.deltaValue sX x) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (hk : k + 1 = n - 1) :
    firstChernCapCycleMap D sX hX k
        (componentDivisorCycleRule sX hX setup N k t ratioN dimN hdimN hfinN)
        (divisorCycleAt.{u, z} D sX hX hdec L s ratio hfin hint d hd hn hk) =
      cycleFamilySum D sX hX
        (fun i : divisorSupport.{u, z} D sX hX hdec L s ratio =>
          (i.1).toIntegralClosedSubspace D.site D.base D.base_mem)
        (locallyFinite_subspacePointSet_divisorSupport.{u, z} D sX hX hdec L s ratio hfin) k
        (fun i => orderOfVanishingSection.{u, z} D.site D.base D.base_mem hX.1 hdec i.1 L s
          (ratio i.1) •
            componentDivisorCycleRule sX hX setup N k t ratioN dimN hdimN hfinN
              ((i.1).toIntegralClosedSubspace D.site D.base D.base_mem)
              ((deltaDimension_toIntegralClosedSubspace D sX hX hint d hd hn i.1).trans
                hk.symm)) :=
  firstChernCapCycleMap_divisorCycleAt_eq_componentDivisorSum D sX hX hdec setup L N t
    ratioN dimN hdimN hfinN s ratio hfin hint d hd hn hk Subtype.val Subtype.val_injective
    (locallyFinite_subspacePointSet_divisorSupport.{u, z} D sX hX hdec L s ratio hfin)
    (fun i => (deltaDimension_toIntegralClosedSubspace D sX hX hint d hd hn i.1).trans hk.symm)
    fun W hW => ⟨⟨W, hW⟩, rfl⟩

/-! ### The identity with the component section and dimension function produced -/

/-- **Stacks 0EQU for an invertible `𝒩`, with the component cycle's meromorphic section and
dimension function produced and not assumed.**  Section 0EQU's cycle identity

`c₁(𝒩) ∩ div_ℒ(s) = ∑_i ord_{Z_i,ℒ}(s) · (Z_i → X)_* div_{𝒩|Z_i}(t_i|Z_i)`

in `Z_{n-2}(X)`, where the component cycle at an integral closed subspace `W ⊆ X` is the Weil
divisor `div_{𝒩|_W}(t_W)` of Stacks 0EQE part (1) on `W` **of a meromorphic section `t_W` this
statement constructs**: `AlgebraicGeometry.Space.componentMeromorphicSection`, a regular
meromorphic section of `𝒩|_W` produced by Stacks 0EPQ on `W`, whose hypotheses (a), (b), (c) of
Stacks 0ENA hold because `W` is integral and locally Noetherian.  The source's `t_i|Z_i` — the
reduction of a chosen generator of `𝒩_{ξ_i}`,
`AlgebraicGeometry.Space.PrimeDivisor.genericFibreReduction` — is one such section, and the
identity holds for any of them: the component cycle is a parameter of Stacks 0EQJ occurring on
both of its sides.

The dimension function of Stacks 0EDN on each `W` is likewise no longer carried: it is
`AlgebraicGeometry.Space.subspaceDeltaDimensionFunction`, the dimension function `d` on `|X|`
pulled back along the closed embedding `|W| → |X|`, which is a dimension function because an
intermediate point of a specialization starting in a closed set lies in that closed set.

Invertibility of `𝒩` is Section 0EQU's own hypothesis on `𝒩`.  What is still carried on each
`W` is the pair Stacks 0EQE carries on `X`: the ratio family `ratioN` of Stacks 0EPR and the
local finiteness `hfinN` of the prime divisors of `W` along which `t_W` has nonzero order,
Stacks 0EPS.  Neither can be discharged while
`AlgebraicGeometry.Space.LocalRatio` is an unconstrained function type — a ratio family not
required to be `s ↦ s / s_ξ` for a generator `s_ξ` makes `ord` arbitrary, so the set of prime
divisors of nonzero order is not controlled; the *first* set of Stacks 0EPS, which does not
mention the ratio, is proved and applies to `t_W` because `t_W` is regular, by
`AlgebraicGeometry.Space.locallyFinite_primeDivisor_not_memGenericModuleStalk_of_isIntegral`.

The key formula itself, Stacks 0EQV, **is** proved, unconditionally and axiom-clean:
`AlgebraicGeometry.Space.keyFormula_of_ne_zero` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Headline`, at the canonical choices and
for the constructed tame-symbol sum, from which Stacks 0EQX follows there as
`AlgebraicGeometry.Space.canonicalFirstChernCap_divisor_comm`.  What is still open is only the
*predicate* `AlgebraicGeometry.Space.KeyFormula` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaCycleIdentities`, which quantifies the
component rules of Stacks 0EQJ and the principal divisors of the tame symbols; at that generality
it is not a theorem of this library. -/
@[stacks 0EQU "either cycle identity of the section for an invertible N, with the component \
cycle div_{N|W}(t_W) of Stacks 0EQE part (1) on W and its meromorphic section t_W no longer a \
parameter: t_W is a regular meromorphic section of N|W produced by Stacks 0EPQ on W, and the \
Stacks 0EDN dimension function on W is the one on X pulled back along the closed embedding. \
What is carried on W is the Stacks 0EPR ratio family and the Stacks 0EPS local finiteness of \
the prime divisors of nonzero order, both blocked by LocalRatio being an unconstrained function \
type. hdim is Stacks 0EPZ. The key formula 0EQV IS proved, unconditionally and axiom-clean, as \
keyFormula_of_ne_zero of StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Headline, and \
0EQX follows there as canonicalFirstChernCap_divisor_comm; what is still open is only the \
quantified predicate KeyFormula of KeyFormulaCycleIdentities, which ranges over the component \
rules of 0EQJ and the tame-symbol divisors"]
theorem firstChernCapCycleMap_divisorCycleAt_eq_componentDivisorSum_of_isInvertible
    {k : ℤ} {I : Type v}
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (ratioN : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      LocalRatioFamily.{u, u} D.site D.base D.base_mem (setup.isSpace W) (setup.isDecent W)
        (integralClosedSubspaceRestrict D sX hX N W))
    (d : DimensionFunction (points D.site D.base D.base_mem X))
    (hd : ∀ x, d x = D.deltaValue sX x)
    (hfinN : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      LocallyFinite fun P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor =>
        if setup.sectionOrder W (integralClosedSubspaceRestrict D sX hX N W)
            (componentMeromorphicSection sX hX setup N hN W) (ratioN W) P = 0
          then ∅ else P.support D.site D.base D.base_mem W.subspace.toFunctor)
    (s : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 L)
    (ratio : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec L)
    (hfin : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec L s ratio W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hint : IsIntegralSpace D.site D.base D.base_mem X) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (hk : k + 1 = n - 1)
    (Z : I → PrimeDivisor D.site D.base D.base_mem X)
    (hZinj : Function.Injective Z)
    (hZfin : LocallyFinite fun i : I =>
      subspacePointSet D.site D.base D.base_mem X (Z i).subspace)
    (hdim : ∀ i, deltaDimension D sX
      ((Z i).toIntegralClosedSubspace D.site D.base D.base_mem) = k + 1)
    (hcover : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
      divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec L s ratio W ≠ 0 →
        ∃ i, Z i = W) :
    firstChernCapCycleMap D sX hX k
        (componentDivisorCycleRule sX hX setup N k
          (componentMeromorphicSection sX hX setup N hN) ratioN
          (fun W => subspaceDeltaDimensionFunction D sX hX d W)
          (fun W => subspaceDeltaDimensionFunction_eq_deltaValue D sX hX d hd W) hfinN)
        (divisorCycleAt.{u, z} D sX hX hdec L s ratio hfin hint d hd hn hk) =
      cycleFamilySum D sX hX
        (fun i => (Z i).toIntegralClosedSubspace D.site D.base D.base_mem) hZfin k
        (fun i => orderOfVanishingSection.{u, z} D.site D.base D.base_mem hX.1 hdec (Z i) L s
          (ratio (Z i)) •
            componentDivisorCycleRule sX hX setup N k
              (componentMeromorphicSection sX hX setup N hN) ratioN
              (fun W => subspaceDeltaDimensionFunction D sX hX d W)
              (fun W => subspaceDeltaDimensionFunction_eq_deltaValue D sX hX d hd W) hfinN
              ((Z i).toIntegralClosedSubspace D.site D.base D.base_mem) (hdim i)) :=
  firstChernCapCycleMap_divisorCycleAt_eq_componentDivisorSum.{u, z, v} D sX hX hdec setup L N
    (componentMeromorphicSection sX hX setup N hN) ratioN
    (fun W => subspaceDeltaDimensionFunction D sX hX d W)
    (fun W => subspaceDeltaDimensionFunction_eq_deltaValue D sX hX d hd W) hfinN s ratio hfin
    hint d hd
    hn hk Z hZinj hZfin hdim hcover

/-- **Stacks 0EQU over the prime divisors of nonzero order, for an invertible `𝒩`, with the
component cycle's meromorphic section and dimension function produced.**  The statement of
`firstChernCapCycleMap_divisorCycleAt_eq_componentDivisorSum_of_isInvertible`
for the smallest family Section 0EQU may be taken over, the prime divisors of `X` along which
`s` has nonzero order of vanishing, for which injectivity, the covering property and the
δ-dimension of the members are theorems. -/
theorem firstChernCapCycleMap_divisorCycleAt_eq_componentDivisorSum_divisorSupport_of_isInvertible
    {k : ℤ}
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (ratioN : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      LocalRatioFamily.{u, u} D.site D.base D.base_mem (setup.isSpace W) (setup.isDecent W)
        (integralClosedSubspaceRestrict D sX hX N W))
    (d : DimensionFunction (points D.site D.base D.base_mem X))
    (hd : ∀ x, d x = D.deltaValue sX x)
    (hfinN : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      LocallyFinite fun P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor =>
        if setup.sectionOrder W (integralClosedSubspaceRestrict D sX hX N W)
            (componentMeromorphicSection sX hX setup N hN W) (ratioN W) P = 0
          then ∅ else P.support D.site D.base D.base_mem W.subspace.toFunctor)
    (s : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 L)
    (ratio : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec L)
    (hfin : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec L s ratio W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hint : IsIntegralSpace D.site D.base D.base_mem X) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (hk : k + 1 = n - 1) :
    firstChernCapCycleMap D sX hX k
        (componentDivisorCycleRule sX hX setup N k
          (componentMeromorphicSection sX hX setup N hN) ratioN
          (fun W => subspaceDeltaDimensionFunction D sX hX d W)
          (fun W => subspaceDeltaDimensionFunction_eq_deltaValue D sX hX d hd W) hfinN)
        (divisorCycleAt.{u, z} D sX hX hdec L s ratio hfin hint d hd hn hk) =
      cycleFamilySum D sX hX
        (fun i : divisorSupport.{u, z} D sX hX hdec L s ratio =>
          (i.1).toIntegralClosedSubspace D.site D.base D.base_mem)
        (locallyFinite_subspacePointSet_divisorSupport.{u, z} D sX hX hdec L s ratio hfin) k
        (fun i => orderOfVanishingSection.{u, z} D.site D.base D.base_mem hX.1 hdec i.1 L s
          (ratio i.1) •
            componentDivisorCycleRule sX hX setup N k
              (componentMeromorphicSection sX hX setup N hN) ratioN
              (fun W => subspaceDeltaDimensionFunction D sX hX d W)
              (fun W => subspaceDeltaDimensionFunction_eq_deltaValue D sX hX d hd W) hfinN
              ((i.1).toIntegralClosedSubspace D.site D.base D.base_mem)
              ((deltaDimension_toIntegralClosedSubspace D sX hX hint d hd hn i.1).trans
                hk.symm)) :=
  firstChernCapCycleMap_divisorCycleAt_eq_componentDivisorSum_divisorSupport.{u, z} D sX hX hdec
    setup L N (componentMeromorphicSection sX hX setup N hN) ratioN
    (fun W => subspaceDeltaDimensionFunction D sX hX d W)
    (fun W => subspaceDeltaDimensionFunction_eq_deltaValue D sX hX d hd W) hfinN s ratio hfin
    hint d hd
    hn hk

end CycleIdentity

end AlgebraicGeometry.Space

end
