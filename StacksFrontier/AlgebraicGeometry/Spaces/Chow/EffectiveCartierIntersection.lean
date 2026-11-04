module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceFamilySums
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroScheme

/-!
# Intersecting with effective Cartier divisors on an algebraic space

In the situation of Stacks 0EDT let `X/B` be good, let `ℒ` be an invertible sheaf on `X` with a
global section `s`, let `E = Z(s) ⊆ X` be the vanishing locus of `s` and let `i : E → X` be the
closed immersion.  Stacks 0ER1 defines, for every `k ∈ ℤ`, the *refined Gysin homomorphism*

  `i^* : Z_{k+1}(X) ⟶ CH_k(E)`

by prescribing it on an integral closed subspace `W ⊆ X` with `dim_δ(W) = k + 1`: it is the
`k`-cycle `[E ∩ W]_k` on `E` when `W ⊄ E`, and it is `i'_*(c₁(ℒ|_W) ∩ [W])` for the induced
closed immersion `i' : W → E` when `W ⊆ E`; the rule is then extended additively over a cycle.
When `E` is an effective Cartier divisor one writes `E · α = i_* i^* α`.

The letter `D` is taken by the dimension situation of Stacks 0EDT, so the closed subspace which
the source calls `D` is called `E` throughout this file.

## Main definitions

* `AlgebraicGeometry.Space.ChowTarget`: the Chow group `CH_k(Y)` of a good algebraic space,
  taken as an explicit parameter; see the implementation notes.
* `AlgebraicGeometry.Space.integralCycle`: the cycle `[W]` of a single integral closed subspace
  of δ-dimension `k`.
* `AlgebraicGeometry.Space.containedPushforward`: the pushforward `i'_*` of `k`-cycles along the
  closed immersion `W → E` of an integral closed subspace of `X` contained in `E`.
* `AlgebraicGeometry.Space.GysinComponentRule`: the two component inputs of Stacks 0ER1(1),
  namely `[E ∩ W]_k` for `W ⊄ E` and `c₁(ℒ|_W) ∩ [W]` for `W ⊆ E`.
* `AlgebraicGeometry.Space.gysinComponentCycle`: the component `k`-cycle on `E` attached to an
  integral closed subspace of `X`, by the dichotomy of Stacks 0ER1(1).
* `AlgebraicGeometry.Space.gysinCycleMap`: the additive extension of the component rule,
  `Z_{k+1}(X) ⟶ Z_k(E)`, which is Stacks 0ER1(2) at the level of cycles.
* `AlgebraicGeometry.Space.refinedGysin`: **Stacks 0ER1**, parts (1) and (2), the refined Gysin
  homomorphism of the vanishing locus of a global section of an invertible sheaf.
* `AlgebraicGeometry.Space.effectiveCartierIntersection`: **Stacks 0ER1**, part (3), the
  operation `E · α = i_* i^* α` of an effective Cartier divisor.

## Main results

* `AlgebraicGeometry.Space.gysinComponentCycle_of_not_le`,
  `AlgebraicGeometry.Space.gysinComponentCycle_of_le`: the two cases (1)(a) and (1)(b) of the
  source.
* `AlgebraicGeometry.Space.gysinCoeff_mem_cyclesOfDimension`: the coefficientwise extension of
  the component rule over a `(k+1)`-cycle is a `k`-cycle on `E`.  This is the content of
  part (2): the sum defining it is finite at every integral closed subspace of `E`, its support
  is locally finite, and every subspace in that support has δ-dimension `k`.
* `AlgebraicGeometry.Space.refinedGysin_integralCycle_of_not_le`,
  `AlgebraicGeometry.Space.refinedGysin_integralCycle_of_le`: the value of the refined Gysin
  homomorphism on the cycle of a single integral closed subspace, in the two cases.

## Implementation notes

### The Chow group of `E` is an explicit parameter

The target of the Gysin homomorphism is the Chow group `CH_k(E)` of Stacks 0EQ6.  All four parts
of that tag are available in this repository: part (1) is the cycle `∑ (i_j)_* div(f_j)`
attached to a locally finite family, `AlgebraicGeometry.Space.cycleFamilySum`, and in
`StacksFrontier/AlgebraicGeometry/Spaces/Chow/RationalEquivalence.lean` part (2) is
`AlgebraicGeometry.Space.IsRationallyEquivalentToZero` (line 288) with the subgroup
`AlgebraicGeometry.Space.rationalEquivalences` (line 364), part (3) is
`AlgebraicGeometry.Space.RationallyEquivalent` (line 382) and part (4) is the quotient
`AlgebraicGeometry.Space.chowGroup` (line 422) with its class map
`AlgebraicGeometry.Space.chowClass` (line 427).  The principal divisor `div(f)` of a rational
function on an integral algebraic space, which part (2) is stated through, is
`AlgebraicGeometry.Space.IsPrincipalDivisorCycle` (line 217), taken at the canonical embeddings
`R(W) → Q(𝒪^h_{W,ξ})` of Stacks 0ENK — `AlgebraicGeometry.Space.genericFractionEmbedding`
(`StacksFrontier/AlgebraicGeometry/Spaces/Decent/PrimeDivisorFunctionFieldEmbedding.lean:288`).

`AlgebraicGeometry.Space.ChowTarget` nevertheless takes `CH_k(Y)` as a parameter: an abelian
group together with a class map `Z_k(Y) → CH_k(Y)` and, for each integral closed subspace
`W ⊆ Y`, the set of principal divisors on `W` that part (1) consumes, subject to the requirement
that the class map kill every cycle `∑ (i_j)_* div(f_j)` built from them.  That requirement is
phrased through part (1), so an instance of this structure is exactly a group receiving `Z_k(Y)`
and killing rational equivalence in the sense of the source.  The quotient of part (4) is such
an instance — `AlgebraicGeometry.Space.chowTarget`
(`StacksFrontier/AlgebraicGeometry/Spaces/Chow/RationalEquivalence.lean:474`) — so substituting it
for the parameter recovers the statement of the source verbatim, and nothing below needs any
property of the parameter.

### The component cycles are explicit parameters, but `i'_*` and the extension are not

Both inputs of Stacks 0ER1(1) exist for algebraic spaces: `[Z]_k`, the cycle associated to a
closed subspace, is Stacks 0EE9 and is `AlgebraicGeometry.Space.closedSubspaceCycle`
(`StacksFrontier/AlgebraicGeometry/Spaces/Chow/ClosedSubspaceCycle.lean:258`, carrying
`@[stacks 0EE9]` for part (2)), and the cap product `c₁(ℒ) ∩ -` is Stacks 0EQJ, whose component
rule at the canonical choices is `AlgebraicGeometry.Space.canonicalFirstChernRule`
(`StacksFrontier/AlgebraicGeometry/Spaces/Chow/CanonicalFirstChernCap.lean:89`).  They are kept as
the two fields of `AlgebraicGeometry.Space.GysinComponentRule`,
which asks for the `k`-cycle `[E ∩ W]_k` on `E` in case (1)(a) — together with the support
property that the source's `E ∩ W` gives it, namely that it is carried by `i⁻¹(W)` — and for the
`k`-cycle `c₁(ℒ|_W) ∩ [W]` on `W` in case (1)(b).

The remainder of the definition is constructed and proved here.  In case (1)(b) the pushforward
`i'_*` along the induced closed immersion `i' : W → E` is the genuine pushforward of cycles
along a closed immersion, `AlgebraicGeometry.Space.cycleGroupClosedPushforward`, whose support
property is proved rather than assumed; `W → E` is a closed immersion because `W → X` is one and
`W ≤ E`.  The dichotomy of part (1) is a case distinction on `W ≤ E`, and part (2) is the
coefficientwise extension `AlgebraicGeometry.Space.gysinCycleMap`, whose well-definedness — the
two clauses of `AlgebraicGeometry.Space.gysinCoeff_mem_cyclesOfDimension` — is the mathematical
content of this file.  Local finiteness is where the hypotheses earn their keep: a neighbourhood
of a point of `|E|` meeting only finitely many of the subspaces carrying `α` is intersected with
the finitely many neighbourhoods supplied by the component cycles of those subspaces, exactly as
in `AlgebraicGeometry.Space.cycleFamilySumCoeff_mem_cyclesOfDimension`.

Part (2) is formalized as the coefficientwise identity rather than as finite additivity, because
a cycle is an infinite formal sum: `∑ n_j i^*[W_j]` is not a finite sum of elements of
`CH_k(E)`, and the source's `∑` is meaningful only because the family is locally finite.  This
is also why `AlgebraicGeometry.Space.gysinCycleMap` is built at the level of cycles and the
parameter `CH_k(E)` is applied afterwards: the cycle-level map is finer than the source's, and
composing it with the class map gives the source's map.  Part (3) is read the same way: `i_*` is
the honest pushforward of cycles along the closed immersion `i : E → X`, and the class map of a
Chow group for `X` is applied to the result.

## References

* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u w v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] Classical.propDecidable

/-! ### The Chow group as a parameter -/

/-- The Chow group `CH_k(Y)` of a good algebraic space `Y/B`, taken as an explicit parameter: an
abelian group `CH` together with a class map from `Z_k(Y)` which kills the cycles that Stacks
0EQ6 part (1) declares rationally equivalent to zero.

The field `principalDivisors` is the input of part (1): the set of principal divisors `div(f)`,
`f ∈ R(W)^*`, on an integral closed subspace `W ⊆ Y`.  It is inhabited by the honest principal
divisors, `AlgebraicGeometry.Space.principalDivisorsOfIntegralClosedSubspaces`
(`StacksFrontier/AlgebraicGeometry/Spaces/Chow/PrincipalDivisor.lean:757`), built from
`AlgebraicGeometry.Space.principalDivisorCycleSet` (line 717 of that file); the underlying
predicate is `AlgebraicGeometry.Space.IsPrincipalDivisorCycle`
(`StacksFrontier/AlgebraicGeometry/Spaces/Chow/RationalEquivalence.lean:217`).  See the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierIntersection` for why the Chow group
is a parameter at all. -/
structure ChowTarget (D : BaseSpaceDimensionSituation.{u})
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (k : ℤ) (CH : Type w) [AddCommGroup CH] where
  /-- The class map `Z_k(Y) → CH_k(Y)`. -/
  cls : CycleGroup D sY k →+ CH
  /-- For an integral closed subspace `W ⊆ Y`, the principal divisors `div(f)` of the nonzero
  rational functions `f ∈ R(W)^*`, as `k`-cycles on `W`.  This is the input of Stacks 0EQ6
  part (1) which this repository does not have. -/
  principalDivisors : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
    Set (CycleGroup D (W.subspace.ι ≫ sY) k)
  /-- **Stacks 0EQ6, parts (2) and (4).** The class map kills a cycle rationally equivalent to
  zero, that is, one of the form `∑ (i_j)_* div(f_j)` of part (1). -/
  cls_cycleFamilySum_eq_zero : ∀ {J : Type v}
    (W : J → IntegralClosedSubspace D.site D.base D.base_mem Y)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem Y (W j).subspace)
    (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sY) k)
    (_hc : ∀ j, c j ∈ principalDivisors (W j)),
    cls (cycleFamilySum D sY hY W hWfin k c) = 0

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-! ### The cycle of a single integral closed subspace

The source evaluates the Gysin homomorphism on `[W]` for a single integral closed subspace `W`
of δ-dimension `k + 1`.  For an *integral closed* subspace of δ-dimension exactly `k` the cycle
`[W]_k` of Stacks 0EE9 is the coefficient family taking the value `1` at `W`, which needs none
of the multiplicity theory that the general case of Stacks 0EE9 does. -/

section IntegralCycle

variable (sX : X ⟶ D.space) (k : ℤ) (W : IntegralClosedSubspace D.site D.base D.base_mem X)

/-- The coefficient family of the cycle `[W]` of a single integral closed subspace: the value is
`1` at `W` and `0` elsewhere. -/
def integralCycleCoeff : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ :=
  fun Z => if Z = W then 1 else 0

/-- The coefficient of `[W]` at `W` itself is `1`. -/
@[simp]
theorem integralCycleCoeff_self : integralCycleCoeff D W W = 1 := by
  simp [integralCycleCoeff]

/-- The coefficient of `[W]` at an integral closed subspace other than `W` is `0`. -/
theorem integralCycleCoeff_eq_zero {Z : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hZ : Z ≠ W) : integralCycleCoeff D W Z = 0 := by
  simp [integralCycleCoeff, hZ]

/-- The only integral closed subspace at which `[W]` has a nonzero coefficient is `W`. -/
theorem eq_of_integralCycleCoeff_ne_zero {Z : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hZ : integralCycleCoeff D W Z ≠ 0) : Z = W := by
  by_contra h
  exact hZ (integralCycleCoeff_eq_zero D W h)

/-- The cycle `[W]` of a single integral closed subspace of δ-dimension `k` is a `k`-cycle: only
`W` itself carries a nonzero coefficient, so the support is a single point set. -/
theorem integralCycleCoeff_mem_cyclesOfDimension (hW : deltaDimension D sX W = k) :
    integralCycleCoeff D W ∈ cyclesOfDimension D sX k := by
  refine ⟨fun x => ⟨Set.univ, Filter.univ_mem, (Set.finite_singleton W).subset ?_⟩,
    fun Z hZ => ?_⟩
  · rintro Z ⟨q, hq, -⟩
    by_cases hZW : Z = W
    · exact Set.mem_singleton_iff.2 hZW
    · simp [integralCycleCoeff_eq_zero D W hZW] at hq
  · rw [eq_of_integralCycleCoeff_ne_zero D W hZ]
    exact hW

/-- The cycle `[W]` of a single integral closed subspace of δ-dimension `k`, as an element of
`Z_k(X)`. -/
def integralCycle (hW : deltaDimension D sX W = k) : CycleGroup D sX k :=
  ⟨integralCycleCoeff D W, integralCycleCoeff_mem_cyclesOfDimension D sX k W hW⟩

/-- The coefficient family of the cycle `integralCycle` is `integralCycleCoeff`. -/
@[simp]
theorem integralCycle_coe (hW : deltaDimension D sX W = k) :
    (integralCycle D sX k W hW).1 = integralCycleCoeff D W :=
  rfl

end IntegralCycle

/-! ### Pushforward along the inclusion of a subspace of the divisor

This is the `i'_*` of case (1)(b) of the source: `W ⊆ E` are both closed subspaces of `X`, so
`W → E` is a closed immersion and `k`-cycles push forward along it. -/

section ContainedPushforward

variable (p : X ⟶ D.space) (E : ClosedSubspaces D.site D.base D.base_mem X)
    (hE : D.IsGood (E.1.ι ≫ p)) (k : ℤ)
    {W : IntegralClosedSubspace D.site D.base D.base_mem X} (hWE : W.subspace ≤ E.1)

/-- The inclusion `W → E` of an integral closed subspace of `X` contained in the closed subspace
`E` is a closed immersion: the inclusion of `W` in `X` is one, and `W ≤ E`. -/
theorem isClosedImmersion_homOfLe_of_le :
    IsClosedImmersion D.site D.base D.base_mem (Subfunctor.homOfLe hWE) :=
  isClosedImmersion_homOfLe' D.site D.base D.base_mem W.isClosedSubspace.2 hWE

/-- The inclusion `W → E` followed by the structure morphism of `E` is the structure morphism
of `W`. -/
theorem homOfLe_comp_structure :
    Subfunctor.homOfLe hWE ≫ E.1.ι ≫ p = W.subspace.ι ≫ p := by
  rw [← Category.assoc, Subfunctor.homOfLe_ι]

/-- **The `i'_*` of Stacks 0ER1(1)(b).** Pushforward of `k`-cycles along the closed immersion
`W → E` of an integral closed subspace of `X` contained in `E`, both viewed over the base
through `X`. -/
def containedPushforward :
    CycleGroup D (W.subspace.ι ≫ p) k →+ CycleGroup D (E.1.ι ≫ p) k :=
  cycleGroupClosedPushforward D E.2.1 W.isClosedSubspace.1
    (D.isDecentSpace_of_isGood (E.1.ι ≫ p) hE)
    (isClosedImmersion_homOfLe_of_le D E hWE) (E.1.ι ≫ p) hE.2.2 (W.subspace.ι ≫ p)
    (homOfLe_comp_structure D p E hWE) k

/-- An integral closed subspace of `E` at which a pushforward from `W ⊆ E` has a nonzero
coefficient has its point set inside the inverse image of the point set of `W`: the coefficient
is nonzero only at the image of an integral closed subspace of `W`, and the inclusion of `W` in
`E` followed by the inclusion of `E` in `X` is the inclusion of `W` in `X`. -/
theorem subspacePointSet_subset_of_containedPushforward_ne_zero
    (c : CycleGroup D (W.subspace.ι ≫ p) k)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor)
    (hZ : (containedPushforward D p E hE k hWE c).1 Z ≠ 0) :
    subspacePointSet D.site D.base D.base_mem E.1.toFunctor Z.subspace ⊆
      pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι ⁻¹'
        subspacePointSet D.site D.base D.base_mem X W.subspace := by
  by_cases hex : ∃ Z', IntegralClosedSubspace.pushforward D.site D.base D.base_mem E.2.1
      W.isClosedSubspace.1 (D.isDecentSpace_of_isGood (E.1.ι ≫ p) hE)
      (isClosedImmersion_homOfLe_of_le D E hWE) Z' = Z
  · obtain ⟨Z', rfl⟩ := hex
    rw [IntegralClosedSubspace.subspacePointSet_pushforward]
    rintro q ⟨r, -, rfl⟩
    refine ⟨r, ?_⟩
    rw [← Subfunctor.homOfLe_ι hWE, pointsMap_comp]
    rfl
  · exact absurd (cycleClosedPushforward_apply_of_forall_ne D E.2.1 W.isClosedSubspace.1
      (D.isDecentSpace_of_isGood (E.1.ι ≫ p) hE) (isClosedImmersion_homOfLe_of_le D E hWE)
      c.1 Z fun Z' hZ' => hex ⟨Z', hZ'⟩) hZ

end ContainedPushforward

/-! ### The component rule and its additive extension -/

section Gysin

variable (p : X ⟶ D.space) (E : ClosedSubspaces D.site D.base D.base_mem X)
    (hE : D.IsGood (E.1.ι ≫ p)) (k : ℤ)

/-- The two component inputs of Stacks 0ER1(1) for a closed subspace `E ⊆ X`, neither of which
exists for algebraic spaces in this repository.

`intersectionCycle` is case (1)(a): the `k`-cycle `[E ∩ W]_k` on `E` of Stacks 0EE9, for an
integral closed subspace `W ⊆ X` of δ-dimension `k + 1` not contained in `E`.  Its support
property `intersectionCycle_support` records that `E ∩ W` is carried by `i⁻¹(W)`, which is what
makes the additive extension below a cycle.

`chernCycle` is case (1)(b): the `k`-cycle `c₁(ℒ|_W) ∩ [W]` on `W` of Stacks 0EQJ, for an
integral closed subspace `W ⊆ E` of δ-dimension `k + 1`.  No support property is asked of it:
the source pushes it forward along `W → E`, and `AlgebraicGeometry.Space.containedPushforward`
does so here, which gives the support property for free. -/
structure GysinComponentRule where
  /-- Case (1)(a) of the source: the `k`-cycle `[E ∩ W]_k` on `E`, for `W ⊄ E`. -/
  intersectionCycle : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
    deltaDimension D p W = k + 1 → ¬ W.subspace ≤ E.1 → CycleGroup D (E.1.ι ≫ p) k
  /-- The cycle `[E ∩ W]_k` is carried by `i⁻¹(W)`. -/
  intersectionCycle_support : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D p W = k + 1) (hWE : ¬ W.subspace ≤ E.1)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor),
    (intersectionCycle W hW hWE).1 Z ≠ 0 →
      subspacePointSet D.site D.base D.base_mem E.1.toFunctor Z.subspace ⊆
        pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι ⁻¹'
          subspacePointSet D.site D.base D.base_mem X W.subspace
  /-- Case (1)(b) of the source: the `k`-cycle `c₁(ℒ|_W) ∩ [W]` on `W`, for `W ⊆ E`. -/
  chernCycle : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
    deltaDimension D p W = k + 1 → W.subspace ≤ E.1 → CycleGroup D (W.subspace.ι ≫ p) k

variable (rule : GysinComponentRule D p E k)

/-- **Stacks 0ER1(1).** The component `k`-cycle on `E` attached to an integral closed subspace
`W ⊆ X`: it is `i'_*(c₁(ℒ|_W) ∩ [W])` when `W ⊆ E`, it is `[E ∩ W]_k` when `W ⊄ E`, and it is
zero when `dim_δ(W) ≠ k + 1`, in which case `W` does not occur in a `(k+1)`-cycle. -/
def gysinComponentCycle (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    CycleGroup D (E.1.ι ≫ p) k :=
  if hW : deltaDimension D p W = k + 1 then
    if hWE : W.subspace ≤ E.1 then
      containedPushforward D p E hE k hWE (rule.chernCycle W hW hWE)
    else rule.intersectionCycle W hW hWE
  else 0

/-- **Stacks 0ER1(1)(a).** For `W ⊄ E` of δ-dimension `k + 1` the component cycle is
`[E ∩ W]_k`. -/
theorem gysinComponentCycle_of_not_le
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1) (hWE : ¬ W.subspace ≤ E.1) :
    gysinComponentCycle D p E hE k rule W = rule.intersectionCycle W hW hWE := by
  rw [gysinComponentCycle, dite_eq_left hW, dite_eq_right hWE]

/-- **Stacks 0ER1(1)(b).** For `W ⊆ E` of δ-dimension `k + 1` the component cycle is
`i'_*(c₁(ℒ|_W) ∩ [W])`, for the induced closed immersion `i' : W → E`. -/
theorem gysinComponentCycle_of_le {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1) (hWE : W.subspace ≤ E.1) :
    gysinComponentCycle D p E hE k rule W =
      containedPushforward D p E hE k hWE (rule.chernCycle W hW hWE) := by
  rw [gysinComponentCycle, dite_eq_left hW, dite_eq_left hWE]

/-- A subspace of δ-dimension other than `k + 1` does not occur in a `(k+1)`-cycle, and its
component cycle is zero. -/
theorem gysinComponentCycle_of_deltaDimension_ne
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W ≠ k + 1) : gysinComponentCycle D p E hE k rule W = 0 := by
  rw [gysinComponentCycle, dite_eq_right hW]

/-- The component cycle of `W` is carried by `i⁻¹(W)`.  In case (1)(a) this is the support
property asked of the input, and in case (1)(b) it is proved: a pushforward along `W → E` is
carried by the image of `W`. -/
theorem subspacePointSet_subset_of_gysinComponentCycle_ne_zero
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor)
    (hZ : (gysinComponentCycle D p E hE k rule W).1 Z ≠ 0) :
    subspacePointSet D.site D.base D.base_mem E.1.toFunctor Z.subspace ⊆
      pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι ⁻¹'
        subspacePointSet D.site D.base D.base_mem X W.subspace := by
  by_cases hW : deltaDimension D p W = k + 1
  · by_cases hWE : W.subspace ≤ E.1
    · rw [gysinComponentCycle_of_le D p E hE k rule hW hWE] at hZ
      exact subspacePointSet_subset_of_containedPushforward_ne_zero D p E hE k hWE _ Z hZ
    · rw [gysinComponentCycle_of_not_le D p E hE k rule hW hWE] at hZ
      exact rule.intersectionCycle_support W hW hWE Z hZ
  · rw [gysinComponentCycle_of_deltaDimension_ne D p E hE k rule hW] at hZ
    exact absurd rfl hZ

/-- **Stacks 0ER1(2).** The coefficient at an integral closed subspace `Z ⊆ E` of the additive
extension of the component rule over a `(k+1)`-cycle `α = ∑ n_W [W]` on `X`: the sum of `n_W`
times the coefficient of the component cycle of `W` at `Z`. -/
def gysinCoeff (α : CycleGroup D p (k + 1))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor) : ℤ :=
  ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X,
    α.1 W * (gysinComponentCycle D p E hE k rule W).1 Z

/-- The defining formula of `gysinCoeff`: the coefficient at `Z` is the sum over `W` of the
coefficient of `α` at `W` times the coefficient at `Z` of the component cycle of `W`. -/
theorem gysinCoeff_def (α : CycleGroup D p (k + 1))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor) :
    gysinCoeff D p E hE k rule α Z =
      ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X,
        α.1 W * (gysinComponentCycle D p E hE k rule W).1 Z :=
  rfl

/-- A nonzero coefficient of the extension comes from a subspace occurring in `α` whose
component cycle has a nonzero coefficient there. -/
theorem exists_ne_zero_of_gysinCoeff_ne_zero (α : CycleGroup D p (k + 1))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor)
    (hZ : gysinCoeff D p E hE k rule α Z ≠ 0) :
    ∃ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      α.1 W ≠ 0 ∧ (gysinComponentCycle D p E hE k rule W).1 Z ≠ 0 := by
  by_contra hall
  refine hZ ?_
  rw [gysinCoeff_def]
  refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
  rcases not_and_or.1 (not_exists.1 hall W) with h | h
  · rw [not_not.1 h, zero_mul]
  · rw [not_not.1 h, mul_zero]

/-- A point of `E` in a subspace `Z` at which the component cycle of `W` is nonzero maps into
`W`, provided `α` has a nonzero coefficient at `W`. -/
private theorem ite_point_mem_of_ne_zero (α : CycleGroup D p (k + 1))
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    {Z : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor}
    {q : points D.site D.base D.base_mem E.1.toFunctor} (hWne : α.1 W ≠ 0)
    (hcomp : (gysinComponentCycle D p E hE k rule W).1 Z ≠ 0)
    (hq : q ∈ subspacePointSet D.site D.base D.base_mem E.1.toFunctor Z.subspace) :
    pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι q ∈
      if α.1 W = 0 then (∅ : Set (points D.site D.base D.base_mem X))
        else subspacePointSet D.site D.base D.base_mem X W.subspace := by
  simpa [hWne] using
    subspacePointSet_subset_of_gysinComponentCycle_ne_zero D p E hE k rule W Z hcomp hq

/-- At a fixed integral closed subspace of `E` only finitely many subspaces of `X` contribute to
the extension, so the sum defining the extension is a finite sum: a contributing `W` contains
the image of the generic point of `Z`, because the component cycle of `W` is carried by
`i⁻¹(W)`, and only finitely many subspaces occurring in `α` meet a neighbourhood of that
point. -/
theorem hasFiniteSupport_gysinCoeff (α : CycleGroup D p (k + 1))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor) :
    Function.HasFiniteSupport fun W : IntegralClosedSubspace D.site D.base D.base_mem X =>
      α.1 W * (gysinComponentCycle D p E hE k rule W).1 Z := by
  set z : points D.site D.base D.base_mem E.1.toFunctor :=
    pointsMap D.site D.base D.base_mem Z.subspace.toFunctor Z.subspace.ι
      (Z.genericPoint D.site D.base D.base_mem)
  have hzZ : z ∈ subspacePointSet D.site D.base D.base_mem E.1.toFunctor Z.subspace := ⟨_, rfl⟩
  obtain ⟨V, hV, hVfin⟩ := α.2.1 (pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι z)
  refine hVfin.subset fun W hW => ?_
  have hprod := Function.mem_support.1 hW
  exact ⟨_, ite_point_mem_of_ne_zero D p E hE k rule α (left_ne_zero_of_mul hprod)
    (right_ne_zero_of_mul hprod) hzZ, mem_of_mem_nhds hV⟩

/-- **Stacks 0ER1(2).** The coefficientwise extension of the component rule over a `(k+1)`-cycle
on `X` is a `k`-cycle on `E`.

Local finiteness: a point of `|E|` has a neighbourhood `V` in `|X|` meeting only finitely many of
the subspaces occurring in `α`; intersecting the inverse image of `V` with the finitely many
neighbourhoods supplied by the component cycles of those subspaces gives a neighbourhood meeting
the point sets of only finitely many subspaces of `E` with a nonzero coefficient, because a
subspace with a nonzero coefficient is carried by `i⁻¹(W)` for one of them.  The δ-dimension of
such a subspace is `k` because that holds for the component cycle it comes from. -/
theorem gysinCoeff_mem_cyclesOfDimension (α : CycleGroup D p (k + 1)) :
    gysinCoeff D p E hE k rule α ∈ cyclesOfDimension D (E.1.ι ≫ p) k := by
  refine ⟨fun x => ?_, fun Z hZ => ?_⟩
  · obtain ⟨V, hV, hVfin⟩ := α.2.1 (pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι x)
    choose U hU hUfin using fun W : IntegralClosedSubspace D.site D.base D.base_mem X =>
      (gysinComponentCycle D p E hE k rule W).2.1 x
    set F : Set (IntegralClosedSubspace D.site D.base D.base_mem X) :=
      {W | ((if α.1 W = 0 then (∅ : Set (points D.site D.base D.base_mem X))
        else subspacePointSet D.site D.base D.base_mem X W.subspace) ∩ V).Nonempty}
    refine ⟨(pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι ⁻¹' V) ∩ (⋂ W ∈ F, U W),
      Filter.inter_mem
        ((continuous_pointsMap D.site D.base D.base_mem E.1.ι).continuousAt.preimage_mem_nhds hV)
        ((Filter.biInter_mem hVfin).2 fun W _ => hU W), ?_⟩
    refine (hVfin.biUnion fun W _ => hUfin W).subset ?_
    intro Z hZ
    obtain ⟨q, hqZ, hqN⟩ := hZ
    by_cases hne : gysinCoeff D p E hE k rule α Z = 0
    · simp [hne] at hqZ
    have hqZ' : q ∈ subspacePointSet D.site D.base D.base_mem E.1.toFunctor Z.subspace := by
      simpa [hne] using hqZ
    obtain ⟨W, hWne, hcomp⟩ := exists_ne_zero_of_gysinCoeff_ne_zero D p E hE k rule α Z hne
    have hWF : W ∈ F :=
      ⟨_, ite_point_mem_of_ne_zero D p E hE k rule α hWne hcomp hqZ', hqN.1⟩
    refine Set.mem_iUnion₂.2 ⟨W, hWF, q, ?_, Set.mem_iInter₂.1 hqN.2 W hWF⟩
    simpa [hcomp] using hqZ'
  · obtain ⟨W, -, hcomp⟩ := exists_ne_zero_of_gysinCoeff_ne_zero D p E hE k rule α Z hZ
    exact (gysinComponentCycle D p E hE k rule W).2.2 Z hcomp

/-- The extension of the component rule over the zero cycle is zero. -/
theorem gysinCoeff_zero : gysinCoeff D p E hE k rule 0 = 0 := by
  funext Z
  simp only [Pi.zero_apply]
  rw [gysinCoeff_def]
  refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
  have hzero : (0 : CycleGroup D p (k + 1)).1 W = 0 := rfl
  rw [hzero, zero_mul]

/-- **Stacks 0ER1(2).** The extension of the component rule is additive in the cycle: this is
the coefficientwise form of `i^*(α + β) = i^* α + i^* β`, and it is where the finiteness of the
defining sum is used. -/
theorem gysinCoeff_add (α β : CycleGroup D p (k + 1)) :
    gysinCoeff D p E hE k rule (α + β) =
      gysinCoeff D p E hE k rule α + gysinCoeff D p E hE k rule β := by
  funext Z
  rw [Pi.add_apply, gysinCoeff_def, gysinCoeff_def, gysinCoeff_def,
    ← finsum_add_distrib (hasFiniteSupport_gysinCoeff D p E hE k rule α Z)
      (hasFiniteSupport_gysinCoeff D p E hE k rule β Z)]
  refine finsum_congr fun W => ?_
  have hadd : (α + β).1 W = α.1 W + β.1 W := rfl
  rw [hadd, add_mul]

/-- **Stacks 0ER1, parts (1) and (2).** The refined Gysin homomorphism at the level of cycles:
the additive extension of the component rule, `Z_{k+1}(X) ⟶ Z_k(E)`.  Composing it with the
class map of an `AlgebraicGeometry.Space.ChowTarget` for `E` gives the homomorphism of the
source. -/
def gysinCycleMap : CycleGroup D p (k + 1) →+ CycleGroup D (E.1.ι ≫ p) k where
  toFun α := ⟨gysinCoeff D p E hE k rule α, gysinCoeff_mem_cyclesOfDimension D p E hE k rule α⟩
  map_zero' := Subtype.ext (gysinCoeff_zero D p E hE k rule)
  map_add' α β := Subtype.ext (gysinCoeff_add D p E hE k rule α β)

/-- The coefficient of `gysinCycleMap α` at `Z` is the sum over `W` of the coefficient of `α` at
`W` times the coefficient at `Z` of the component cycle of `W`. -/
@[simp]
theorem gysinCycleMap_apply (α : CycleGroup D p (k + 1))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor) :
    (gysinCycleMap D p E hE k rule α).1 Z =
      ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X,
        α.1 W * (gysinComponentCycle D p E hE k rule W).1 Z :=
  rfl

/-- **Stacks 0ER1(1).** On the cycle `[W]` of a single integral closed subspace of δ-dimension
`k + 1` the extension is the component cycle of `W`. -/
theorem gysinCycleMap_integralCycle
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1) :
    gysinCycleMap D p E hE k rule (integralCycle D p (k + 1) W hW) =
      gysinComponentCycle D p E hE k rule W := by
  refine Subtype.ext (funext fun Z => ?_)
  rw [gysinCycleMap_apply, finsum_eq_single _ W fun W' hW' => by
    rw [integralCycle_coe, integralCycleCoeff_eq_zero D W hW', zero_mul],
    integralCycle_coe, integralCycleCoeff_self, one_mul]

end Gysin

/-! ### The refined Gysin homomorphism of a section of an invertible sheaf -/

section ZeroScheme

variable (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections) (k : ℤ)

/-- The vanishing locus `E = Z(s)` of a global section of a sheaf of modules on `X`, as a closed
subspace of `X`.  This is the `D` of Stacks 0ER1, and it is Stacks 0845. -/
abbrev vanishingLocus : ClosedSubspaces D.site D.base D.base_mem X :=
  zeroScheme D.site D.base D.base_mem ⟨X, hp.1⟩ L s

/-- The hypothesis that `ℒ` is invertible, which is the setting of Stacks 0ER1.  The
construction does not use it: the vanishing locus of Stacks 0845 is defined for a section of any
sheaf of modules, and the first Chern class of `ℒ` enters only through the parameter
`AlgebraicGeometry.Space.GysinComponentRule.chernCycle`. -/
abbrev IsInvertibleSheaf : Prop :=
  AlgebraicGeometry.SheafOfModules.IsInvertible
    (smallEtaleRingedSite D.site D.base D.base_mem X hp.1).O.obj
    (structureRingSheaf D.site D.base D.base_mem ⟨X, hp.1⟩).property L

variable (hE : D.IsGood ((vanishingLocus D p hp L s).1.ι ≫ p))

/-- **Stacks 0ER1, parts (1) and (2).** The *refined Gysin homomorphism*
`i^* : Z_{k+1}(X) ⟶ CH_k(E)` of the vanishing locus `E = Z(s)` of a global section `s` of an
invertible sheaf `ℒ` on a good algebraic space `X/B`, with `i : E → X` the closed immersion.

On the cycle of an integral closed subspace `W ⊆ X` of δ-dimension `k + 1` it is the class of
`[E ∩ W]_k` when `W ⊄ E`, which is part (1)(a), and the class of `i'_*(c₁(ℒ|_W) ∩ [W])` when
`W ⊆ E`, which is part (1)(b); see
`AlgebraicGeometry.Space.refinedGysin_integralCycle_of_not_le` and
`AlgebraicGeometry.Space.refinedGysin_integralCycle_of_le`.  Part (2), the extension of that
rule over an arbitrary `(k+1)`-cycle, is `AlgebraicGeometry.Space.gysinCycleMap`, which is
proved to land in `Z_k(E)` and to be additive.

The Chow group `CH_k(E)` and the two component cycles `[E ∩ W]_k` and `c₁(ℒ|_W) ∩ [W]` are
explicit parameters, standing in for Stacks 0EQ6 parts (2)–(4), Stacks 0EE9 and Stacks 0EQJ,
none of which is available for algebraic spaces in this repository; see the implementation notes
of `StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierIntersection`. -/
@[stacks 0ER1 "the refined Gysin homomorphism i^* : Z_{k+1}(X) → CH_k(D) of the vanishing locus
D = Z(s), parts (1)(a), (1)(b) and (2); the Chow group of D and the two component cycles
[D ∩ W]_k and c_1(L|_W) ∩ [W] are explicit parameters, instantiated by Stacks 0EQ6 parts
(2)-(4) (chowTarget), Stacks 0EE9 (closedSubspaceCycle) and Stacks 0EQJ
(canonicalFirstChernRule)"]
def refinedGysin (_hL : IsInvertibleSheaf D p hp L)
    (rule : GysinComponentRule D p (vanishingLocus D p hp L s) k)
    {CH : Type w} [AddCommGroup CH]
    (chow : ChowTarget.{u, w, v} D ((vanishingLocus D p hp L s).1.ι ≫ p) hE k CH) :
    CycleGroup D p (k + 1) →+ CH :=
  chow.cls.comp (gysinCycleMap D p (vanishingLocus D p hp L s) hE k rule)

/-- **Stacks 0ER1(1)(a).** On the cycle of an integral closed subspace `W ⊆ X` of δ-dimension
`k + 1` which is not contained in `E`, the refined Gysin homomorphism is the class of the
`k`-cycle `[E ∩ W]_k`. -/
theorem refinedGysin_integralCycle_of_not_le (hL : IsInvertibleSheaf D p hp L)
    (rule : GysinComponentRule D p (vanishingLocus D p hp L s) k)
    {CH : Type w} [AddCommGroup CH]
    (chow : ChowTarget.{u, w, v} D ((vanishingLocus D p hp L s).1.ι ≫ p) hE k CH)
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1)
    (hWE : ¬ W.subspace ≤ (vanishingLocus D p hp L s).1) :
    refinedGysin D p hp L s k hE hL rule chow (integralCycle D p (k + 1) W hW) =
      chow.cls (rule.intersectionCycle W hW hWE) := by
  rw [refinedGysin, AddMonoidHom.comp_apply,
    gysinCycleMap_integralCycle D p (vanishingLocus D p hp L s) hE k rule hW,
    gysinComponentCycle_of_not_le D p (vanishingLocus D p hp L s) hE k rule hW hWE]

/-- **Stacks 0ER1(1)(b).** On the cycle of an integral closed subspace `W ⊆ E` of δ-dimension
`k + 1`, the refined Gysin homomorphism is the class of `i'_*(c₁(ℒ|_W) ∩ [W])`, for the induced
closed immersion `i' : W → E`. -/
theorem refinedGysin_integralCycle_of_le (hL : IsInvertibleSheaf D p hp L)
    (rule : GysinComponentRule D p (vanishingLocus D p hp L s) k)
    {CH : Type w} [AddCommGroup CH]
    (chow : ChowTarget.{u, w, v} D ((vanishingLocus D p hp L s).1.ι ≫ p) hE k CH)
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1)
    (hWE : W.subspace ≤ (vanishingLocus D p hp L s).1) :
    refinedGysin D p hp L s k hE hL rule chow (integralCycle D p (k + 1) W hW) =
      chow.cls (containedPushforward D p (vanishingLocus D p hp L s) hE k hWE
        (rule.chernCycle W hW hWE)) := by
  rw [refinedGysin, AddMonoidHom.comp_apply,
    gysinCycleMap_integralCycle D p (vanishingLocus D p hp L s) hE k rule hW,
    gysinComponentCycle_of_le D p (vanishingLocus D p hp L s) hE k rule hW hWE]

/-- **Stacks 0ER1, part (3).** Intersecting with an effective Cartier divisor: when `E = Z(s)`
is an effective Cartier divisor on `X` one writes `E · α = i_* i^* α` for the pushforward along
the closed immersion `i : E → X` of the refined Gysin class of `α`.

The pushforward is the honest pushforward of cycles along a closed immersion,
`AlgebraicGeometry.Space.cycleGroupClosedPushforward`, applied to the cycle-level Gysin map; the
class map of a Chow group for `X` is applied afterwards.  The source applies `i_*` to a Chow
class, which needs proper pushforward to respect rational equivalence; the form below is that
statement at the level of cycles, and is the same once Stacks 0EQ6 parts (2)–(4) land. -/
@[stacks 0ER1 "part (3): the operation D · α = i_* i^* α of an effective Cartier divisor
D = Z(s), with the Chow group of X and the component cycles [D ∩ W]_k and c_1(L|_W) ∩ [W] taken
as explicit parameters, instantiated by Stacks 0EQ6 parts (2)-(4) (chowTarget), Stacks 0EE9
(closedSubspaceCycle) and Stacks 0EQJ (canonicalFirstChernRule); the pushforward i_* is applied
to the cycle-level Gysin map, the source applying it to the class"]
def effectiveCartierIntersection (_hL : IsInvertibleSheaf D p hp L)
    (_hCartier : IsEffectiveCartierDivisor D.site D.base D.base_mem ⟨X, hp.1⟩
      (vanishingLocus D p hp L s))
    (rule : GysinComponentRule D p (vanishingLocus D p hp L s) k)
    {CH : Type w} [AddCommGroup CH]
    (chow : ChowTarget.{u, w, v} D p hp k CH) :
    CycleGroup D p (k + 1) →+ CH :=
  chow.cls.comp
    ((cycleGroupClosedPushforward D hp.1 (vanishingLocus D p hp L s).2.1
      (D.isDecentSpace_of_isGood p hp) (vanishingLocus D p hp L s).2.2 p hp.2.2
      ((vanishingLocus D p hp L s).1.ι ≫ p) rfl k).comp
        (gysinCycleMap D p (vanishingLocus D p hp L s) hE k rule))

end ZeroScheme

end AlgebraicGeometry.Space

end
