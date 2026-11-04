module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.BivariantVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CoherentSheafCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CycleOfClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SectionsColimitDescent

/-!
# Intersecting with an invertible sheaf on an algebraic space

In the situation of Stacks 0EDT let `X/B` be good and let `ℒ` be an invertible
`O_X`-module.  Stacks 0EQJ defines, for every `k ∈ ℤ`, the cap product with the first Chern
class of `ℒ`

  `c₁(ℒ) ∩ - : Z_{k+1}(X) ⟶ CH_k(X)`

by prescribing it on an integral closed subspace `i : W → X` with `dim_δ(W) = k + 1`, where it
is `i_*(c₁(i^*ℒ) ∩ [W])`, and extending it by linearity over a cycle `α = ∑ n_j [W_j]`.

## Main definitions

* `AlgebraicGeometry.Space.FirstChernComponentCycleRule`: the component datum of the source,
  the `(k)`-cycle `c₁(ℒ|_W) ∩ [W]` on an integral closed subspace `W ⊆ X` of δ-dimension
  `k + 1`, taken as an explicit parameter; see the implementation notes.
* `AlgebraicGeometry.Space.firstChernComponentCycle`: the `k`-cycle `i_*(c₁(ℒ|_W) ∩ [W])` on
  `X` attached to an integral closed subspace `W ⊆ X`, which is case (1) of the source.
* `AlgebraicGeometry.Space.firstChernCapCycleMap`: the additive extension of the component
  rule, `Z_{k+1}(X) ⟶ Z_k(X)`, which is case (2) of the source at the level of cycles.
* `AlgebraicGeometry.Space.firstChernClassCap`: **Stacks 0EQJ**, the cap product
  `c₁(ℒ) ∩ - : Z_{k+1}(X) ⟶ CH_k(X)` with the first Chern class of an invertible sheaf.
* `AlgebraicGeometry.Space.ComponentsOfDeltaDimension`: the irreducible components of `X` of a
  given δ-dimension, as integral closed subspaces.
* `AlgebraicGeometry.Space.fundamentalCycleCoeff`: the coefficient family of the fundamental
  cycle `[X]_n`, which is the cycle `[𝒪_X]_n` of the structure sheaf.
* `AlgebraicGeometry.Space.integralClosedSubspaceRestrict`,
  `AlgebraicGeometry.Space.integralClosedSubspaceRestrictSection` and
  `AlgebraicGeometry.Space.componentVanishingLocus`: the restrictions `ℒ|_W` and `s|_W` to an
  integral closed subspace `W ⊆ X`, and the zero scheme `Z(s|_W)` of the latter on `W`.
* `AlgebraicGeometry.Space.componentZeroCycleCoeff` and
  `AlgebraicGeometry.Space.componentZeroCycleSumCoeff`: **Stacks 0EQL, the right-hand side**,
  the cycle `[Z(s|_{X_i})]_k` pushed forward to `X` and the weighted sum `∑ n_i [Z(s_i)]_k` of
  the source, as coefficient families on `X`.

## Main results

* `AlgebraicGeometry.Space.firstChernCapCoeff_mem_cyclesOfDimension`: the coefficientwise
  extension of the component rule over a `(k+1)`-cycle is a `k`-cycle on `X`.  This is the
  content of case (2): the sum defining it is finite at every integral closed subspace of `X`,
  its support is locally finite, and every subspace in that support has δ-dimension `k`.
* `AlgebraicGeometry.Space.firstChernClassCap_integralCycle`: **Stacks 0EQJ**, case (1), the
  value of the cap product on the fundamental cycle of a single integral closed subspace of
  δ-dimension `k + 1`.
* `cycleCoeffOfClosedSubspace_vanishingLocus_eq_componentZeroCycleSumCoeff`: the identity
  `[Z(s)]_k = ∑ n_i [Z(s_i)]_k` of Stacks 0EQL, reduced to a single local identity at the
  integral closed subspaces of δ-dimension `k` contained in `Z(s)`, which is carried as a
  hypothesis.  It carries no `@[stacks 0EQL]` attribute; see the implementation notes.
* `AlgebraicGeometry.Space.locallyFinite_irreducibleComponents_points`: the irreducible
  components of `|X|` form a locally finite collection, which is Stacks 0EE5 for `X` itself.
* `AlgebraicGeometry.Space.hasFiniteSupport_componentZeroCycleSumCoeff`: the sum
  `∑ n_i [Z(s_i)]_k` is a finite sum at every integral closed subspace of `X`.
* `AlgebraicGeometry.Space.subspacePointSet_subset_of_cycleCoeffOfClosedSubspace_ne_zero`:
  only the integral closed subspaces contained in a closed subspace `Y ⊆ X` occur in `[Y]_k`.

## Implementation notes

### The component cycle is an explicit parameter

The component rule of Stacks 0EQJ is `c₁(ℒ|_W) ∩ [W]` for an *integral* algebraic space `W` of
δ-dimension `k + 1`, which is Stacks 0EQE (Definition 82.17.1): the class of the Weil divisor
`div_{ℒ|_W}(s)` of a nonzero meromorphic section `s` of `ℒ|_W`.  That definition is **not**
available in this repository, and neither is the chain under it: Stacks 0EQE rests on Stacks
0EPU (the order `ord_{Z,ℒ}(s)` of a meromorphic section of an invertible sheaf along a prime
divisor of an integral algebraic space), Stacks 0EPT (independence of the chosen section) and
Stacks 0EPZ (that a Weil divisor on an integral good space of δ-dimension `n` has δ-dimension
`n - 1`).

So, exactly as `StacksFrontier.AlgebraicGeometry.Chow.FirstChernClass` does on the scheme side for
the corresponding gap (Stacks 02SJ), every declaration below takes that component cycle as an
explicit argument `chern` of type
`AlgebraicGeometry.Space.FirstChernComponentCycleRule`.  Substituting the divisor cycle of
Stacks 0EQE, once it lands, recovers the statement of Stacks 0EQJ verbatim; until then nothing
here depends on the gap.

The parameter is *cycle*-valued rather than Chow-class valued, because the source's inner
expression is the class of an explicit cycle, `div_{ℒ|_W}(s)` for a chosen nonzero meromorphic
section: pushing that cycle forward along `W → X` and then taking its class in `CH_k(X)` is the
honest reading of the source's `i_*(c₁(ℒ|_W) ∩ [W])`.  The source applies `i_*` to a *class*,
which needs proper pushforward to respect rational equivalence (Stacks 0EQ8, which this
repository does not have); the two agree once that lands, and the cycle-level form is the finer
of the two.

The pushforward `i_*` itself is **not** a parameter: it is the genuine pushforward of cycles
along the closed immersion of an integral closed subspace,
`AlgebraicGeometry.Space.integralClosedSubspacePushforward`, whose support property is proved
rather than assumed.  Nor is the fundamental cycle `[W]` a parameter: for an integral closed
subspace of δ-dimension exactly `k + 1` it is the coefficient family taking the value `1` at
`W`, which is `AlgebraicGeometry.Space.integralCycle` and needs none of the multiplicity theory
that the general `[Z]_k` of Stacks 0EE9 does.

### The Chow group of `X` is an explicit parameter

The target `CH_k(X)` is the Chow group of Stacks 0EQ6, of which only part (1) is available
here; `AlgebraicGeometry.Space.ChowTarget` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierIntersection` packages it as a
parameter, and it is reused unchanged rather than respelled.  That is the only reason this
module imports the module of Stacks 0ER1: nothing in Stacks 0EQJ depends on Stacks 0ER1, and
indeed the dependence runs the other way — case (1)(b) of Stacks 0ER1 consumes the component
cycle of Stacks 0EQE, which is the parameter of this file.

Case (2) is formalized as the coefficientwise identity rather than as finite additivity,
because a cycle is an infinite formal sum: `∑ n_j c₁(ℒ) ∩ [W_j]` is not a finite sum of
elements of `CH_k(X)`, and the source's `∑` is meaningful only because the family of subspaces
carrying a cycle is locally finite.  This is also why
`AlgebraicGeometry.Space.firstChernCapCycleMap` is built at the level of cycles and the
parameter `CH_k(X)` is applied afterwards.

### The zero cycle of a regular section

Stacks 0EQL compares, for a regular section `s` of `ℒ` on a good `X/B` with
`dim_δ(X) ≤ k + 1`, the `k`-cycle of the zero scheme `Z(s)` with the sum
`∑ n_i [Z(s|_{X_i})]_k` over the irreducible components `X_i ⊆ X` of δ-dimension `k + 1`,
weighted by their multiplicities in `[X]_{k+1}`.

The `k`-cycle `[Y]_k` of a closed subspace `Y ⊆ X` exists in this library as the coefficient
family `AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace` on the integral closed subspaces
of `X`, which is the form in which Stacks 0EE9 and Stacks 0EED are stated here, so the
identity of `k`-cycles is the identity of those two coefficient families.  The multiplicity
`n_i` is the coefficient of `X_i` in `[X]_{k+1} = [𝒪_X]_{k+1}`, that is the length of `𝒪_X` at
the generic point of `X_i`, which is part (1) of Stacks 0EEB; and `s|_{X_i}` is the inverse
image of Stacks 03LU along the closed immersion `X_i → X`, so `Z(s|_{X_i})` is the zero scheme
of Stacks 0845 of an honest section of an `𝒪_{X_i}`-module.  Lengths are taken at chosen
geometric representatives of the generic points, as everywhere in this development, Stacks
0EE1 not being available.

Two inputs of the source are explicit hypotheses of
`cycleCoeffOfClosedSubspace_vanishingLocus_eq_componentZeroCycleSumCoeff`:

* `hover`: that a point of `Z(s|_{X_i})` lies over a point of `Z(s)`.  The zero scheme of a
  restricted section is the base change of the zero scheme, which is out of reach here: the
  defining ideal of the zero scheme of Stacks 0845 is not identified with the image of
  evaluation at the section, for want of quasi-coherent ideals on an algebraic space (Stacks
  03MB).  The implementation notes of
  `StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeFactorization` record the same gap: it is
  not available even that `s` pulls back to zero along `Z(s) → X`.
* `hlocal`: the identity of coefficients at an integral closed subspace of δ-dimension `k`
  contained in `Z(s)`, that is the additivity of lengths at its generic point.

**Only the right-hand side carries a `@[stacks 0EQL]` attribute.**  The subspaces of
δ-dimension `k` contained in `Z(s)` are exactly those at which either side of the identity can
be nonzero, so `hlocal` is the assertion of Stacks 0EQL wherever it has content; a tag on the
conditional statement would report the source as proved from itself.  Discharging `hlocal`
needs the source's own proof — pull back along a surjective étale chart from a scheme, apply
the scheme case Stacks 0EPI, descend — and each step is blocked: Stacks 0EP8 and the cycle
identity of Stacks 0EPY do not exist here, Stacks 0EPI is stated over a base *scheme* rather
than the base algebraic space of Situation 0EDT, and the two developments measure
multiplicities by lengths over different local rings, their comparison being Stacks 0EE1 for a
module.  The docstring of the conditional statement spells this out.

What *is* proved is the remainder of the identity: both sides vanish at an integral closed
subspace of δ-dimension other than `k`, which is where the compatibility of the pushforward of
cycles with δ-dimension enters, and both sides vanish at an integral closed subspace of
δ-dimension `k` which is not contained in `Z(s)`.  The sum over the components is also shown
to be a finite sum at each integral closed subspace, which is what makes it the `∑` of the
source: a contributing component passes through the generic point of that subspace, and the
components of `|X|` are locally finite by Stacks 0EE5.

## References

* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EPU](https://stacks.math.columbia.edu/tag/0EPU)
* [Stacks Project, Tag 0EPZ](https://stacks.math.columbia.edu/tag/0EPZ)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0EQL](https://stacks.math.columbia.edu/tag/0EQL)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 01WY](https://stacks.math.columbia.edu/tag/01WY)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 0EDX](https://stacks.math.columbia.edu/tag/0EDX)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE5](https://stacks.math.columbia.edu/tag/0EE5)
* [Stacks Project, Tag 0EE8](https://stacks.math.columbia.edu/tag/0EE8)
* [Stacks Project, Tag 0EEB](https://stacks.math.columbia.edu/tag/0EEB)
* [Stacks Project, Tag 0EED](https://stacks.math.columbia.edu/tag/0EED)
* [Stacks Project, Tag 0ENF](https://stacks.math.columbia.edu/tag/0ENF)
* [Stacks Project, Tag 0EPI](https://stacks.math.columbia.edu/tag/0EPI)
* [Stacks Project, Tag 0EPY](https://stacks.math.columbia.edu/tag/0EPY)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u w v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] Classical.propDecidable

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-! ### The component input -/

/-- The component datum of Stacks 0EQJ: for every integral closed subspace `W ⊆ X` of
δ-dimension `k + 1`, a `k`-cycle on `W`.  The intended value is the Weil divisor
`div_{ℒ|_W}(s)` of a nonzero meromorphic section of `ℒ|_W`, whose class is the
`c₁(ℒ|_W) ∩ [W]` of Stacks 0EQE; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernClassCap`. -/
abbrev FirstChernComponentCycleRule (sX : X ⟶ D.space) (k : ℤ) :=
  ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
    deltaDimension D sX W = k + 1 → CycleGroup D (W.subspace.ι ≫ sX) k

section ComponentRule

variable (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    (chern : FirstChernComponentCycleRule D sX k)

/-! ### The component rule -/

/-- **Stacks 0EQJ, case (1), at the level of cycles.** The `k`-cycle on `X` attached to an
integral closed subspace `W ⊆ X` of δ-dimension `k + 1`: the pushforward along the closed
immersion `i : W → X` of the component cycle `c₁(ℒ|_W) ∩ [W]` on `W`.  It is zero when
`dim_δ(W) ≠ k + 1`, in which case `W` does not occur in a `(k+1)`-cycle. -/
def firstChernComponentCycle (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    CycleGroup D sX k :=
  if hW : deltaDimension D sX W = k + 1 then
    integralClosedSubspacePushforward D sX hX W k (chern W hW)
  else 0

/-- For `W` of δ-dimension `k + 1` the component cycle is `i_*(c₁(ℒ|_W) ∩ [W])`. -/
theorem firstChernComponentCycle_of_deltaDimension_eq
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D sX W = k + 1) :
    firstChernComponentCycle D sX hX k chern W =
      integralClosedSubspacePushforward D sX hX W k (chern W hW) := by
  rw [firstChernComponentCycle, dite_eq_left hW]

/-- A subspace of δ-dimension other than `k + 1` does not occur in a `(k+1)`-cycle, and its
component cycle is zero. -/
theorem firstChernComponentCycle_of_deltaDimension_ne
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D sX W ≠ k + 1) :
    firstChernComponentCycle D sX hX k chern W = 0 := by
  rw [firstChernComponentCycle, dite_eq_right hW]

/-- The component cycle of `W` is supported on `W`: it is a pushforward along the closed
immersion of `W`, hence carried by the point set of `W`. -/
theorem subspacePointSet_subset_of_firstChernComponentCycle_ne_zero
    (W Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : (firstChernComponentCycle D sX hX k chern W).1 Z ≠ 0) :
    subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆
      subspacePointSet D.site D.base D.base_mem X W.subspace := by
  by_cases hW : deltaDimension D sX W = k + 1
  · rw [firstChernComponentCycle_of_deltaDimension_eq D sX hX k chern hW] at hZ
    exact subspacePointSet_subset_of_pushforward_ne_zero D sX hX W k _ Z hZ
  · rw [firstChernComponentCycle_of_deltaDimension_ne D sX hX k chern hW] at hZ
    exact absurd rfl hZ

/-! ### The additive extension -/

/-- **Stacks 0EQJ, case (2).** The coefficient at an integral closed subspace `Z ⊆ X` of the
additive extension of the component rule over a `(k+1)`-cycle `α = ∑ n_W [W]` on `X`: the sum
of `n_W` times the coefficient of the component cycle of `W` at `Z`. -/
def firstChernCapCoeff (α : CycleGroup D sX (k + 1))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) : ℤ :=
  ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X,
    α.1 W * (firstChernComponentCycle D sX hX k chern W).1 Z

/-- The coefficient at `Z` of the additive extension of the component rule over
`α = ∑ n_W [W]` is the sum of `n_W` times the coefficient of the component cycle of `W` at `Z`. -/
theorem firstChernCapCoeff_def (α : CycleGroup D sX (k + 1))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    firstChernCapCoeff D sX hX k chern α Z =
      ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X,
        α.1 W * (firstChernComponentCycle D sX hX k chern W).1 Z :=
  rfl

/-- A finite sum of products vanishes if no index has both factors nonzero. -/
private theorem finsum_mul_eq_zero_of_forall {ι : Type*} (a b : ι → ℤ)
    (h : ∀ i, a i ≠ 0 → b i ≠ 0 → False) : ∑ᶠ i, a i * b i = 0 :=
  finsum_eq_zero_of_forall_eq_zero fun i => by
    rcases eq_or_ne (a i) 0 with ha | ha
    · rw [ha, zero_mul]
    · rw [of_not_not (h i ha), mul_zero]

/-- A nonzero coefficient of the extension comes from a subspace occurring in `α` whose
component cycle has a nonzero coefficient there. -/
theorem exists_ne_zero_of_firstChernCapCoeff_ne_zero (α : CycleGroup D sX (k + 1))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : firstChernCapCoeff D sX hX k chern α Z ≠ 0) :
    ∃ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      α.1 W ≠ 0 ∧ (firstChernComponentCycle D sX hX k chern W).1 Z ≠ 0 := by
  by_contra hall
  refine hZ ?_
  rw [firstChernCapCoeff_def]
  exact finsum_mul_eq_zero_of_forall _ _ fun W h₁ h₂ => hall ⟨W, h₁, h₂⟩

/-- At a fixed integral closed subspace of `X` only finitely many subspaces contribute to the
extension, so the sum defining it is a finite sum: a contributing `W` contains the generic
point of `Z`, because the component cycle of `W` is carried by `W`, and only finitely many
subspaces occurring in `α` meet a neighbourhood of that point. -/
theorem hasFiniteSupport_firstChernCapCoeff (α : CycleGroup D sX (k + 1))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    Function.HasFiniteSupport fun W : IntegralClosedSubspace D.site D.base D.base_mem X =>
      α.1 W * (firstChernComponentCycle D sX hX k chern W).1 Z := by
  set ξ : points D.site D.base D.base_mem X :=
    pointsMap D.site D.base D.base_mem Z.subspace.toFunctor Z.subspace.ι
      (Z.genericPoint D.site D.base D.base_mem)
  have hξZ : ξ ∈ subspacePointSet D.site D.base D.base_mem X Z.subspace := ⟨_, rfl⟩
  obtain ⟨V, hV, hVfin⟩ := α.2.1 ξ
  refine hVfin.subset fun W hW => ?_
  have hprod : α.1 W * (firstChernComponentCycle D sX hX k chern W).1 Z ≠ 0 :=
    Function.mem_support.1 hW
  have hWne : α.1 W ≠ 0 := left_ne_zero_of_mul hprod
  have hcomp : (firstChernComponentCycle D sX hX k chern W).1 Z ≠ 0 := right_ne_zero_of_mul hprod
  refine ⟨ξ, ?_, mem_of_mem_nhds hV⟩
  have hsub := subspacePointSet_subset_of_firstChernComponentCycle_ne_zero D sX hX k chern W Z
    hcomp hξZ
  simpa [hWne] using hsub

/-- **Stacks 0EQJ, case (2).** The coefficientwise extension of the component rule over a
`(k+1)`-cycle on `X` is a `k`-cycle on `X`.

Local finiteness: a point of `|X|` has a neighbourhood `V` meeting only finitely many of the
subspaces occurring in `α`; intersecting it with the finitely many neighbourhoods supplied by
the component cycles of those subspaces gives a neighbourhood meeting the point sets of only
finitely many subspaces with a nonzero coefficient, because a subspace with a nonzero
coefficient is carried by one of them.  The δ-dimension of such a subspace is `k` because that
holds for the component cycle it comes from. -/
theorem firstChernCapCoeff_mem_cyclesOfDimension (α : CycleGroup D sX (k + 1)) :
    firstChernCapCoeff D sX hX k chern α ∈ cyclesOfDimension D sX k := by
  refine ⟨fun x => ?_, fun Z hZ => ?_⟩
  · obtain ⟨V, hV, hVfin⟩ := α.2.1 x
    choose U hU hUfin using fun W : IntegralClosedSubspace D.site D.base D.base_mem X =>
      (firstChernComponentCycle D sX hX k chern W).2.1 x
    set F : Set (IntegralClosedSubspace D.site D.base D.base_mem X) :=
      {W | ((if α.1 W = 0 then (∅ : Set (points D.site D.base D.base_mem X))
        else subspacePointSet D.site D.base D.base_mem X W.subspace) ∩ V).Nonempty}
    refine ⟨V ∩ (⋂ W ∈ F, U W),
      Filter.inter_mem hV ((Filter.biInter_mem hVfin).2 fun W _ => hU W), ?_⟩
    refine (hVfin.biUnion fun W _ => hUfin W).subset ?_
    intro Z hZ
    obtain ⟨q, hqZ, hqN⟩ := hZ
    by_cases hne : firstChernCapCoeff D sX hX k chern α Z = 0
    · simp [hne] at hqZ
    have hqZ' : q ∈ subspacePointSet D.site D.base D.base_mem X Z.subspace := by
      simpa [hne] using hqZ
    obtain ⟨W, hWne, hcomp⟩ :=
      exists_ne_zero_of_firstChernCapCoeff_ne_zero D sX hX k chern α Z hne
    have hWF : W ∈ F := by
      refine ⟨q, ?_, hqN.1⟩
      have hsub := subspacePointSet_subset_of_firstChernComponentCycle_ne_zero D sX hX k chern
        W Z hcomp hqZ'
      simpa [hWne] using hsub
    refine Set.mem_iUnion₂.2 ⟨W, hWF, q, ?_, Set.mem_iInter₂.1 hqN.2 W hWF⟩
    simpa [hcomp] using hqZ'
  · obtain ⟨W, -, hcomp⟩ :=
      exists_ne_zero_of_firstChernCapCoeff_ne_zero D sX hX k chern α Z hZ
    exact (firstChernComponentCycle D sX hX k chern W).2.2 Z hcomp

/-- The extension of the component rule over the zero cycle is zero. -/
theorem firstChernCapCoeff_zero : firstChernCapCoeff D sX hX k chern 0 = 0 := by
  funext Z
  simp only [Pi.zero_apply]
  rw [firstChernCapCoeff_def]
  exact finsum_mul_eq_zero_of_forall _ _ fun W h _ => h rfl

/-- **Stacks 0EQJ, case (2).** The extension of the component rule is additive in the cycle:
this is the coefficientwise form of `c₁(ℒ) ∩ (α + β) = c₁(ℒ) ∩ α + c₁(ℒ) ∩ β`, and it is where
the finiteness of the defining sum is used. -/
theorem firstChernCapCoeff_add (α β : CycleGroup D sX (k + 1)) :
    firstChernCapCoeff D sX hX k chern (α + β) =
      firstChernCapCoeff D sX hX k chern α + firstChernCapCoeff D sX hX k chern β := by
  funext Z
  rw [Pi.add_apply, firstChernCapCoeff_def, firstChernCapCoeff_def, firstChernCapCoeff_def,
    ← finsum_add_distrib (hasFiniteSupport_firstChernCapCoeff D sX hX k chern α Z)
      (hasFiniteSupport_firstChernCapCoeff D sX hX k chern β Z)]
  refine finsum_congr fun W => ?_
  have hadd : (α + β).1 W = α.1 W + β.1 W := rfl
  rw [hadd, add_mul]

/-- **Stacks 0EQJ, cases (1) and (2), at the level of cycles.** The additive extension of the
component rule, `Z_{k+1}(X) ⟶ Z_k(X)`.  Composing it with the class map of an
`AlgebraicGeometry.Space.ChowTarget` for `X` gives the cap product of the source. -/
def firstChernCapCycleMap : CycleGroup D sX (k + 1) →+ CycleGroup D sX k where
  toFun α := ⟨firstChernCapCoeff D sX hX k chern α,
    firstChernCapCoeff_mem_cyclesOfDimension D sX hX k chern α⟩
  map_zero' := Subtype.ext (firstChernCapCoeff_zero D sX hX k chern)
  map_add' α β := Subtype.ext (firstChernCapCoeff_add D sX hX k chern α β)

/-- The coefficient at `Z` of the image of `α = ∑ n_W [W]` under `firstChernCapCycleMap` is the
sum of `n_W` times the coefficient of the component cycle of `W` at `Z`. -/
@[simp]
theorem firstChernCapCycleMap_apply (α : CycleGroup D sX (k + 1))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (firstChernCapCycleMap D sX hX k chern α).1 Z =
      ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X,
        α.1 W * (firstChernComponentCycle D sX hX k chern W).1 Z :=
  rfl

/-- **Stacks 0EQJ, case (1), at the level of cycles.** On the cycle `[W]` of a single integral
closed subspace of δ-dimension `k + 1` the extension is the component cycle of `W`, that is
`i_*(c₁(ℒ|_W) ∩ [W])`. -/
theorem firstChernCapCycleMap_integralCycle
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D sX W = k + 1) :
    firstChernCapCycleMap D sX hX k chern (integralCycle D sX (k + 1) W hW) =
      integralClosedSubspacePushforward D sX hX W k (chern W hW) := by
  refine Subtype.ext (funext fun Z => ?_)
  rw [firstChernCapCycleMap_apply, finsum_eq_single _ W fun W' hW' => by
      rw [integralCycle_coe, integralCycleCoeff_eq_zero D W hW', zero_mul],
    integralCycle_coe, integralCycleCoeff_self, one_mul,
    firstChernComponentCycle_of_deltaDimension_eq D sX hX k chern hW]

end ComponentRule

/-! ### The cap product -/

section Cap

variable (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1) (k : ℤ)

/-- **Stacks 0EQJ.** *Intersection with the first Chern class of an invertible sheaf*: the cap
product `c₁(ℒ) ∩ - : Z_{k+1}(X) ⟶ CH_k(X)` attached to an invertible sheaf `ℒ` on a good
algebraic space `X/B`.

On the cycle `[W]` of an integral closed subspace `W ⊆ X` of δ-dimension `k + 1` it is the
class of `i_*(c₁(ℒ|_W) ∩ [W])`, which is case (1) of the source; see
`AlgebraicGeometry.Space.firstChernClassCap_integralCycle`.  Case (2), the extension of that
rule by linearity over an arbitrary `(k+1)`-cycle, is
`AlgebraicGeometry.Space.firstChernCapCycleMap`, which is proved to land in `Z_k(X)` and to be
additive.

The component cycle `c₁(ℒ|_W) ∩ [W]` on `W` and the Chow group `CH_k(X)` are explicit
parameters, standing in for Stacks 0EQE and Stacks 0EQ6 parts (2)–(4), neither of which is
available for algebraic spaces in this repository; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernClassCap`.  The pushforward `i_*` and the
fundamental cycle `[W]` are not parameters. -/
@[stacks 0EQJ "the cap product c_1(L) ∩ - : Z_{k+1}(X) → CH_k(X) with the first Chern class of
an invertible sheaf L on a good algebraic space X/B, cases (1) and (2); the component cycle
c_1(L|_W) ∩ [W] on an integral closed subspace W of δ-dimension k+1 and the Chow group CH_k(X)
are explicit parameters, standing in for Stacks 0EQE and Stacks 0EQ6 parts (2)-(4), neither of
which exists for algebraic spaces here; the pushforward i_* and the fundamental cycle [W] are
not parameters"]
def firstChernClassCap (_hL : IsInvertibleSheaf D sX hX L)
    (chern : FirstChernComponentCycleRule D sX k)
    {CH : Type w} [AddCommGroup CH] (chow : ChowTarget.{u, w, v} D sX hX k CH) :
    CycleGroup D sX (k + 1) →+ CH :=
  chow.cls.comp (firstChernCapCycleMap D sX hX k chern)

/-- **Stacks 0EQJ, case (1).** On the cycle `[W]` of an integral closed subspace `W ⊆ X` of
δ-dimension `k + 1` the cap product is the class of `i_*(c₁(ℒ|_W) ∩ [W])`, for the closed
immersion `i : W → X`.

The source applies the proper pushforward `i_* : CH_k(W) ⟶ CH_k(X)` to the *class* of
`c₁(ℒ|_W) ∩ [W]`; the form below applies the pushforward of cycles and takes the class
afterwards, which is the same statement once proper pushforward is known to respect rational
equivalence. -/
@[stacks 0EQJ "case (1): the value of the cap product on the fundamental cycle [W] of an
integral closed subspace W of δ-dimension k+1 is the class of i_*(c_1(L|_W) ∩ [W]), with the
component cycle c_1(L|_W) ∩ [W] and the Chow group CH_k(X) as explicit parameters standing in
for Stacks 0EQE and Stacks 0EQ6 parts (2)-(4); the pushforward i_* is applied to the cycle and
the class taken afterwards, the source applying it to the class"]
theorem firstChernClassCap_integralCycle (hL : IsInvertibleSheaf D sX hX L)
    (chern : FirstChernComponentCycleRule D sX k)
    {CH : Type w} [AddCommGroup CH] (chow : ChowTarget.{u, w, v} D sX hX k CH)
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D sX W = k + 1) :
    firstChernClassCap D sX hX L k hL chern chow (integralCycle D sX (k + 1) W hW) =
      chow.cls (integralClosedSubspacePushforward D sX hX W k (chern W hW)) := by
  rw [firstChernClassCap, AddMonoidHom.comp_apply,
    firstChernCapCycleMap_integralCycle D sX hX k chern hW]

end Cap

/-! ### The zero cycle of a regular section of an invertible sheaf -/

section ZeroCycleOfSection

variable (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1) (s : L.sections) (k : ℤ)

/-- The integral closed subspaces of `X` which are irreducible components of `X` of
δ-dimension `n`: the subspaces the fundamental cycle `[X]_n` is a sum over. -/
abbrev ComponentsOfDeltaDimension (n : ℤ) :=
  {W : IntegralClosedSubspace D.site D.base D.base_mem X //
    IsIrreducibleComponent D.site D.base D.base_mem hX.1 W.subspace ∧
      deltaDimension D sX W = n}

/-- The set of points of an irreducible component of `X`, as an irreducible component of
`|X|`. -/
def ComponentsOfDeltaDimension.points (n : ℤ) (W : ComponentsOfDeltaDimension D sX hX n) :
    irreducibleComponents (Space.points D.site D.base D.base_mem X) :=
  ⟨subspacePointSet D.site D.base D.base_mem X W.1.subspace, W.2.1.2.2⟩

/-- An irreducible component of `X` is determined by its set of points, by Stacks 0ENF. -/
theorem injective_componentsOfDeltaDimension_points (n : ℤ) :
    Function.Injective (ComponentsOfDeltaDimension.points D sX hX n) := fun _ _ h =>
  Subtype.ext (injective_integralClosedSubspaceSupport D.site D.base D.base_mem hX.1
    (IrreducibleCloseds.ext (congrArg Subtype.val h)))

include hX in
/-- **Stacks 0EE5 for the whole space.** The irreducible components of the point space of a
good algebraic space form a locally finite collection: the point space is locally Noetherian,
the structure morphism being locally of finite type over the locally Noetherian base. -/
theorem locallyFinite_irreducibleComponents_points :
    LocallyFinite fun C : irreducibleComponents (Space.points D.site D.base D.base_mem X) =>
      (C : Set (Space.points D.site D.base D.base_mem X)) := by
  have hN := isLocallyNoetherian_of_isLocallyOfFiniteType D.site D.base D.base_mem hX.1
    D.isAlgebraicSpace sX hX.2.2 D.locallyNoetherian
  have h := (isLocallyNoetherianSpace_of_isLocallyNoetherian D.site D.base D.base_mem X hX.1
    hN).locallyFinite_image_irreducibleComponents
      (f := id (α := Space.points D.site D.base D.base_mem X))
      ⟨Topology.IsEmbedding.id, by rw [Set.range_id]; exact isClosed_univ⟩
  simpa using h

/-- The coefficient family of the fundamental cycle `[X]_n` of a good algebraic space `X/B`:
at an integral closed subspace `Z ⊆ X` of δ-dimension `n` it is the length of `𝒪_X` at the
generic point of `Z`, read at the geometric point `γ` assigns to it, and it is zero at a
subspace of any other δ-dimension.

This is the cycle `[𝒪_X]_n` of Stacks 0EEB part (2) at the structure sheaf, which is `[X]_n`
by Stacks 0EED, the inclusion of `X` in itself being the identity. -/
def fundamentalCycleCoeff (n : ℤ)
    (γ : Space.points D.site D.base D.base_mem X →
      GeometricPoint D.site D.base D.base_mem X) :
    IntegralClosedSubspace D.site D.base D.base_mem X → ℤ :=
  cycleCoeffOfModule D sX hX (SheafOfModules.unit _) n γ

/-- The restriction `ℒ|_W` of an `𝒪_X`-module to an integral closed subspace `W ⊆ X`: its
inverse image of Stacks 03LU along the closed immersion `W → X`. -/
abbrev integralClosedSubspaceRestrict
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    Modules.{u, u} D.site D.base D.base_mem W.subspace.toFunctor W.isClosedSubspace.1 :=
  (modulePullback D.site D.base D.base_mem
    (closedSubspaceHom D.site D.base D.base_mem hX.1 W.subspace W.isClosedSubspace)).obj L

/-- The restriction `s|_W` of a global section of `ℒ` to an integral closed subspace
`W ⊆ X`: its inverse image along the closed immersion `W → X`. -/
abbrev integralClosedSubspaceRestrictSection
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (integralClosedSubspaceRestrict D sX hX L W).sections :=
  modulePullbackSections D.site D.base D.base_mem
    (closedSubspaceHom D.site D.base D.base_mem hX.1 W.subspace W.isClosedSubspace) L s

/-- The zero scheme `Z(s|_W)` of the restriction of `s` to an integral closed subspace
`W ⊆ X`, as a closed subspace of `W`.  This is Stacks 0845 on `W`. -/
abbrev componentVanishingLocus (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    ClosedSubspaces D.site D.base D.base_mem W.subspace.toFunctor :=
  zeroScheme D.site D.base D.base_mem ⟨W.subspace.toFunctor, W.isClosedSubspace.1⟩
    (integralClosedSubspaceRestrict D sX hX L W)
    (integralClosedSubspaceRestrictSection D sX hX L s W)

/-- A choice of geometric representative for every point of the zero scheme `Z(s|_{X_i})` on
every irreducible component `X_i ⊆ X` of δ-dimension `k + 1`. -/
abbrev ComponentGeometricRepresentatives :=
  ∀ W : ComponentsOfDeltaDimension D sX hX (k + 1),
    Space.points D.site D.base D.base_mem
        (componentVanishingLocus D sX hX L s W.1).1.toFunctor →
      GeometricPoint D.site D.base D.base_mem
        (componentVanishingLocus D sX hX L s W.1).1.toFunctor

/-- The coefficient family on `X` of the `k`-cycle `[Z(s|_W)]_k` of the zero scheme of the
restriction of `s` to an integral closed subspace `W ⊆ X`, pushed forward along the closed
immersion `W → X`.

The cycle on `W` is the one of Stacks 0EE9, read coefficientwise as in
`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace`, and the pushforward is the honest
pushforward of coefficient families along a closed immersion. -/
def componentZeroCycleCoeff (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (γ : Space.points D.site D.base D.base_mem
        (componentVanishingLocus D sX hX L s W).1.toFunctor →
      GeometricPoint D.site D.base D.base_mem
        (componentVanishingLocus D sX hX L s W).1.toFunctor) :
    IntegralClosedSubspace D.site D.base D.base_mem X → ℤ :=
  cycleClosedPushforward D hX.1 W.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX)
    W.isClosedSubspace.2
    (cycleCoeffOfClosedSubspace D (W.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX W) (componentVanishingLocus D sX hX L s W).1
      (componentVanishingLocus D sX hX L s W).2 k γ)

/-- **Only the subspaces of `Y` occur in `[Y]_k`.** An integral closed subspace of `X` with a
nonzero coefficient in the cycle of a closed subspace `Y ⊆ X` is contained in `Y`. -/
theorem subspacePointSet_subset_of_cycleCoeffOfClosedSubspace_ne_zero (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y)
    (γ : Space.points D.site D.base D.base_mem Y.toFunctor →
      GeometricPoint D.site D.base D.base_mem Y.toFunctor)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : cycleCoeffOfClosedSubspace D sX hX Y hY k γ Z ≠ 0) :
    subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆
      subspacePointSet D.site D.base D.base_mem X Y := by
  by_cases hex : ∃ W, closedSubspaceComponentImage D sX hX Y hY W = Z
  · obtain ⟨W, rfl⟩ := hex
    rw [closedSubspaceComponentImage, IntegralClosedSubspace.subspacePointSet_pushforward]
    exact Set.image_subset_range _ _
  · exact absurd (cycleCoeffOfClosedSubspace_eq_zero D sX hX Y hY k γ Z
      fun W hW => hex ⟨W, hW⟩) hZ

/-- A nonzero coefficient of the pushed-forward cycle of `Z(s|_W)` occurs at the image of an
integral closed subspace of `W`. -/
private theorem exists_pushforward_eq_of_componentZeroCycleCoeff_ne_zero
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (γ : Space.points D.site D.base D.base_mem
        (componentVanishingLocus D sX hX L s W).1.toFunctor →
      GeometricPoint D.site D.base D.base_mem
        (componentVanishingLocus D sX hX L s W).1.toFunctor)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : componentZeroCycleCoeff D sX hX L s k W γ Z ≠ 0) :
    ∃ Z', IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
      W.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 Z' = Z := by
  by_contra hex
  exact hZ (cycleClosedPushforward_apply_of_forall_ne D hX.1 W.isClosedSubspace.1
    (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 _ Z fun Z' hZ' => hex ⟨Z', hZ'⟩)

/-- The cycle of the zero scheme of `s|_W` is carried by `W`: a nonzero coefficient occurs
only at an integral closed subspace of `X` contained in `W`. -/
theorem subspacePointSet_subset_of_componentZeroCycleCoeff_ne_zero
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (γ : Space.points D.site D.base D.base_mem
        (componentVanishingLocus D sX hX L s W).1.toFunctor →
      GeometricPoint D.site D.base D.base_mem
        (componentVanishingLocus D sX hX L s W).1.toFunctor)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : componentZeroCycleCoeff D sX hX L s k W γ Z ≠ 0) :
    subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆
      subspacePointSet D.site D.base D.base_mem X W.subspace := by
  obtain ⟨Z', rfl⟩ :=
    exists_pushforward_eq_of_componentZeroCycleCoeff_ne_zero D sX hX L s k W γ Z hZ
  rw [IntegralClosedSubspace.subspacePointSet_pushforward]
  exact Set.image_subset_range _ _

/-- A nonzero coefficient of the pushed-forward cycle of `Z(s|_W)` occurs only in
δ-dimension `k`: the inclusion of `W` preserves the δ-dimension of an integral closed
subspace, by Stacks 0EDX. -/
theorem deltaDimension_eq_of_componentZeroCycleCoeff_ne_zero
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (γ : Space.points D.site D.base D.base_mem
        (componentVanishingLocus D sX hX L s W).1.toFunctor →
      GeometricPoint D.site D.base D.base_mem
        (componentVanishingLocus D sX hX L s W).1.toFunctor)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : componentZeroCycleCoeff D sX hX L s k W γ Z ≠ 0) :
    deltaDimension D sX Z = k := by
  obtain ⟨Z', rfl⟩ :=
    exists_pushforward_eq_of_componentZeroCycleCoeff_ne_zero D sX hX L s k W γ Z hZ
  rw [deltaDimension_closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace Z']
  by_contra hne
  rw [componentZeroCycleCoeff, cycleClosedPushforward_apply_pushforward,
    cycleCoeffOfClosedSubspace, ite_eq_right hne] at hZ
  exact hZ rfl

/-- **Stacks 0EQL, the right-hand side.** The coefficient family of the `k`-cycle
`∑ n_i [Z(s|_{X_i})]_k` on `X`: the sum, over the irreducible components `X_i ⊆ X` of
δ-dimension `k + 1`, of the pushforward along `X_i → X` of the cycle of the zero scheme of
`s|_{X_i}`, weighted by the multiplicity `n_i` of `X_i` in the fundamental cycle
`[X]_{k+1}`.

The sum is a finite sum at every integral closed subspace of `X`, by
`AlgebraicGeometry.Space.hasFiniteSupport_componentZeroCycleSumCoeff`. -/
@[stacks 0EQL "RIGHT-HAND SIDE ONLY — the equality of 0EQM is NOT formalized here, see
cycleCoeffOfClosedSubspace_vanishingLocus_eq_componentZeroCycleSumCoeff: the sum
∑ n_i [Z(s_i)]_k as a coefficient family on the integral closed subspaces of X, over the
irreducible components X_i of X of δ-dimension k+1, of the pushforward along X_i → X of the
cycle [Z(s|_{X_i})]_k of Stacks 0EE9, weighted by the coefficient n_i of X_i in
[X]_{k+1} = [O_X]_{k+1}; the restriction s|_{X_i} is the inverse image of Stacks 03LU and
Z(s|_{X_i}) its zero scheme of Stacks 0845, both on X_i; the geometric representatives of the
generic points are the arguments γ and γW, as throughout this library, Lemma 0EE1 being absent
from it"]
def componentZeroCycleSumCoeff
    (γ : Space.points D.site D.base D.base_mem X →
      GeometricPoint D.site D.base D.base_mem X)
    (γW : ComponentGeometricRepresentatives D sX hX L s k)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) : ℤ :=
  ∑ᶠ W : ComponentsOfDeltaDimension D sX hX (k + 1),
    fundamentalCycleCoeff D sX hX (k + 1) γ W.1 *
      componentZeroCycleCoeff D sX hX L s k W.1 (γW W) Z

/-- At a fixed integral closed subspace `Z ⊆ X` only finitely many components contribute to
`∑ n_i [Z(s|_{X_i})]_k`, so that sum is the finite sum of the source: a contributing
component contains the generic point of `Z`, the irreducible components of `|X|` are locally
finite by Stacks 0EE5, and an irreducible component is determined by its set of points by
Stacks 0ENF. -/
theorem hasFiniteSupport_componentZeroCycleSumCoeff
    (γ : Space.points D.site D.base D.base_mem X →
      GeometricPoint D.site D.base D.base_mem X)
    (γW : ComponentGeometricRepresentatives D sX hX L s k)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    Function.HasFiniteSupport fun W : ComponentsOfDeltaDimension D sX hX (k + 1) =>
      fundamentalCycleCoeff D sX hX (k + 1) γ W.1 *
        componentZeroCycleCoeff D sX hX L s k W.1 (γW W) Z := by
  obtain ⟨V, hV, hVfin⟩ := locallyFinite_irreducibleComponents_points D sX hX
    (Z.ambientGenericPoint D.site D.base D.base_mem)
  have hfin : {W : ComponentsOfDeltaDimension D sX hX (k + 1) |
      (subspacePointSet D.site D.base D.base_mem X W.1.subspace ∩ V).Nonempty}.Finite := by
    refine Set.Finite.of_finite_image
      (f := ComponentsOfDeltaDimension.points D sX hX (k + 1)) (hVfin.subset ?_)
      ((injective_componentsOfDeltaDimension_points D sX hX (k + 1)).injOn)
    rintro C ⟨W, hW, rfl⟩
    exact hW
  refine hfin.subset fun W hW => ?_
  have hcomp := right_ne_zero_of_mul (Function.mem_support.1 hW)
  exact ⟨Z.ambientGenericPoint D.site D.base D.base_mem,
    subspacePointSet_subset_of_componentZeroCycleCoeff_ne_zero D sX hX L s k W.1 (γW W) Z
      hcomp ⟨Z.genericPoint D.site D.base D.base_mem, rfl⟩,
    mem_of_mem_nhds hV⟩

/-- The cycle `∑ n_i [Z(s|_{X_i})]_k` has coefficient zero at an integral closed subspace of
δ-dimension other than `k`: every summand does. -/
theorem componentZeroCycleSumCoeff_eq_zero_of_deltaDimension_ne
    (γ : Space.points D.site D.base D.base_mem X →
      GeometricPoint D.site D.base D.base_mem X)
    (γW : ComponentGeometricRepresentatives D sX hX L s k)
    {Z : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hZ : deltaDimension D sX Z ≠ k) :
    componentZeroCycleSumCoeff D sX hX L s k γ γW Z = 0 := by
  exact finsum_mul_eq_zero_of_forall _ _ fun W _ h =>
    hZ (deltaDimension_eq_of_componentZeroCycleCoeff_ne_zero D sX hX L s k W.1 (γW W) Z h)

/-- The compatibility of the zero scheme of Stacks 0845 with restriction to an irreducible
component, read on points: a point of `Z(s|_{X_i})` lies over a point of `Z(s)`.

The zero scheme of a restricted section is the base change of the zero scheme, which this
library does not prove: the defining ideal of the zero scheme is not identified with the image
of evaluation at the section, for want of quasi-coherent ideals on an algebraic space
(Stacks 03MB).  See the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.ZeroScheme`. -/
abbrev ComponentVanishingLocusOver : Prop :=
  ∀ (W : ComponentsOfDeltaDimension D sX hX (k + 1))
      (x : Space.points D.site D.base D.base_mem
        (componentVanishingLocus D sX hX L s W.1).1.toFunctor),
    pointsMap D.site D.base D.base_mem W.1.subspace.toFunctor W.1.subspace.ι
        (pointsMap D.site D.base D.base_mem
          (componentVanishingLocus D sX hX L s W.1).1.toFunctor
          (componentVanishingLocus D sX hX L s W.1).1.ι x) ∈
      subspacePointSet D.site D.base D.base_mem X (vanishingLocus D sX hX L s).1

/-- Granting the compatibility of zero schemes with restriction, the component
`[Z(s|_{X_i})]_k` contributes only at integral closed subspaces of `X` contained in `Z(s)`:
such a subspace is the image of one contained in `Z(s|_{X_i})`. -/
theorem subspacePointSet_subset_vanishingLocus_of_componentZeroCycleCoeff_ne_zero
    (hover : ComponentVanishingLocusOver D sX hX L s k)
    (W : ComponentsOfDeltaDimension D sX hX (k + 1))
    (γ : Space.points D.site D.base D.base_mem
        (componentVanishingLocus D sX hX L s W.1).1.toFunctor →
      GeometricPoint D.site D.base D.base_mem
        (componentVanishingLocus D sX hX L s W.1).1.toFunctor)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : componentZeroCycleCoeff D sX hX L s k W.1 γ Z ≠ 0) :
    subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆
      subspacePointSet D.site D.base D.base_mem X (vanishingLocus D sX hX L s).1 := by
  obtain ⟨Z', rfl⟩ :=
    exists_pushforward_eq_of_componentZeroCycleCoeff_ne_zero D sX hX L s k W.1 γ Z hZ
  rw [componentZeroCycleCoeff, cycleClosedPushforward_apply_pushforward] at hZ
  have hsub := subspacePointSet_subset_of_cycleCoeffOfClosedSubspace_ne_zero D
    (W.1.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W.1) k
    (componentVanishingLocus D sX hX L s W.1).1
    (componentVanishingLocus D sX hX L s W.1).2 γ Z' hZ
  rw [IntegralClosedSubspace.subspacePointSet_pushforward]
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨z, rfl⟩ := hsub hy
  exact hover W z

/-- **Stacks 0EQL.** In Situation 0EDT let `X/B` be good, let `ℒ` be an invertible
`𝒪_X`-module, let `s ∈ Γ(X, ℒ)` be a regular section and assume `dim_δ(X) ≤ k + 1`.  Write
`[X]_{k+1} = ∑ n_i [X_i]` over the irreducible components `X_i ⊆ X` of δ-dimension `k + 1`
and set `s_i = s|_{X_i}`.  Then

`[Z(s)]_k = ∑ n_i [Z(s_i)]_k`

as `k`-cycles on `X`.

Both sides are coefficient families on the integral closed subspaces of `X`, which is what a
`k`-cycle of a closed subspace is in this library: `[Z(s)]_k` is
`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace` at the zero scheme of Stacks 0845, as in
Stacks 0EED, and the right-hand side is
`AlgebraicGeometry.Space.componentZeroCycleSumCoeff`.

Away from δ-dimension `k` both sides vanish, the right-hand side by
`AlgebraicGeometry.Space.componentZeroCycleSumCoeff_eq_zero_of_deltaDimension_ne`; and at an
integral closed subspace of δ-dimension `k` not contained in `Z(s)` both sides vanish as
well, by
`AlgebraicGeometry.Space.subspacePointSet_subset_vanishingLocus_of_componentZeroCycleCoeff_ne_zero`
and `AlgebraicGeometry.Space.subspacePointSet_subset_of_cycleCoeffOfClosedSubspace_ne_zero`.
What remains, at an integral closed subspace of δ-dimension `k` contained in `Z(s)`, is the
additivity of lengths at its generic point, and that is the hypothesis `hlocal`.

**No `@[stacks 0EQL]` attribute is carried by this declaration.** The subspaces of
δ-dimension `k` contained in `Z(s)` are exactly those at which either side can be nonzero, so
`hlocal` is the assertion of the source at every subspace that matters, and this statement
would report Stacks 0EQL as proved on the strength of its own hypothesis.  It is recorded
because it reduces Stacks 0EQL to that one local identity.

Discharging `hlocal` is the content of the source's proof: pull back along a surjective étale
chart `φ : V → X` with `V` a scheme, apply the scheme case Stacks 0EPI on `V`, and descend.
Each of the three steps is unavailable here:

* the descent needs the étale pullback of cycles, Stacks 0EP8, and the cycle identity
  `φ^*[Z] = ∑ [Z']` of Stacks 0EPY.  Neither exists in this library; the implementation notes
  of `StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponents` record that of the
  latter only the well-definedness of the right-hand side is proved, "and neither of its two
  sides exists in this library";
* Stacks 0EPI is stated over `Stacks.Chow.ChowSituation`, whose base is a *scheme* with a
  dimension function on it, whereas the base of Situation 0EDT is an algebraic space
  (`AlgebraicGeometry.Space.BaseSpaceDimensionSituation.space`).  Nothing builds the one from
  the other, and the two δ-dimensions are different functions;
* the coefficients here are lengths over the étale local ring at a chosen geometric point,
  while those of Stacks 0EPI are lengths of Zariski stalks; their agreement is Stacks 0EE1 for
  a module, which the implementation notes of
  `StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkLength` record as unavailable for want of
  Stacks 05VP.

The local algebra under Stacks 0EPI, that is Stacks 02QG, *is* available as
`AlgebraicGeometry.natCast_length_quotient_span_eq_sum_minimalPrimes`, but on the étale local
ring it sums over the minimal primes of a strictly henselian ring — the branches at the point —
and grouping those over the irreducible components of `X` is again the étale descent above.

Both carried hypotheses are satisfiable:
`AlgebraicGeometry.Space.forall_cycleCoeffOfClosedSubspace_eq_of_isEmpty_points` and
`AlgebraicGeometry.Space.componentVanishingLocusOver_of_isEmpty_points`. -/
theorem cycleCoeffOfClosedSubspace_vanishingLocus_eq_componentZeroCycleSumCoeff
    (_hL : IsInvertibleSheaf D sX hX L)
    (_hs : IsRegularSection (structureCommRings D.site D.base D.base_mem ⟨X, hX.1⟩)
      (structureRingSheaf D.site D.base D.base_mem ⟨X, hX.1⟩).property s)
    (_hdim : deltaDimensionClosed D sX hX Set.univ isClosed_univ ≤ ((k + 1 : ℤ) : EInt))
    (γ : Space.points D.site D.base D.base_mem X →
      GeometricPoint D.site D.base D.base_mem X)
    (γW : ComponentGeometricRepresentatives D sX hX L s k)
    (γZ : Space.points D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor →
      GeometricPoint D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor)
    (hover : ComponentVanishingLocusOver D sX hX L s k)
    (hlocal : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
      deltaDimension D sX Z = k →
        subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆
          subspacePointSet D.site D.base D.base_mem X (vanishingLocus D sX hX L s).1 →
        cycleCoeffOfClosedSubspace D sX hX (vanishingLocus D sX hX L s).1
            (vanishingLocus D sX hX L s).2 k γZ Z =
          componentZeroCycleSumCoeff D sX hX L s k γ γW Z) :
    cycleCoeffOfClosedSubspace D sX hX (vanishingLocus D sX hX L s).1
        (vanishingLocus D sX hX L s).2 k γZ =
      componentZeroCycleSumCoeff D sX hX L s k γ γW := by
  funext Z
  by_cases h : deltaDimension D sX Z = k
  · by_cases hsub : subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆
        subspacePointSet D.site D.base D.base_mem X (vanishingLocus D sX hX L s).1
    · exact hlocal Z h hsub
    · have hzero : cycleCoeffOfClosedSubspace D sX hX (vanishingLocus D sX hX L s).1
          (vanishingLocus D sX hX L s).2 k γZ Z = 0 := by
        by_contra hne
        exact hsub (subspacePointSet_subset_of_cycleCoeffOfClosedSubspace_ne_zero D sX hX k
          (vanishingLocus D sX hX L s).1 (vanishingLocus D sX hX L s).2 γZ Z hne)
      have hzero' : componentZeroCycleSumCoeff D sX hX L s k γ γW Z = 0 := by
        exact finsum_mul_eq_zero_of_forall _ _ fun W _ hw => hsub
          (subspacePointSet_subset_vanishingLocus_of_componentZeroCycleCoeff_ne_zero D sX hX
            L s k hover W (γW W) Z hw)
      rw [hzero, hzero']
  · rw [cycleCoeffOfClosedSubspace, ite_eq_right h,
      componentZeroCycleSumCoeff_eq_zero_of_deltaDimension_ne D sX hX L s k γ γW h]

/-- The hypothesis `hlocal` of Stacks 0EQL above is satisfiable: an algebraic space with no
points has no integral closed subspaces, every such subspace having a generic point. -/
theorem forall_cycleCoeffOfClosedSubspace_eq_of_isEmpty_points
    (γ : Space.points D.site D.base D.base_mem X →
      GeometricPoint D.site D.base D.base_mem X)
    (γW : ComponentGeometricRepresentatives D sX hX L s k)
    (γZ : Space.points D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor →
      GeometricPoint D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor)
    (hempty : IsEmpty (Space.points D.site D.base D.base_mem X)) :
    ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
      deltaDimension D sX Z = k →
        subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆
          subspacePointSet D.site D.base D.base_mem X (vanishingLocus D sX hX L s).1 →
        cycleCoeffOfClosedSubspace D sX hX (vanishingLocus D sX hX L s).1
            (vanishingLocus D sX hX L s).2 k γZ Z =
          componentZeroCycleSumCoeff D sX hX L s k γ γW Z :=
  fun Z _ _ => (hempty.false (Z.ambientGenericPoint D.site D.base D.base_mem)).elim

/-- The hypothesis `hover` of Stacks 0EQL above is satisfiable: an algebraic space with no
points has no irreducible components, every integral closed subspace having a generic
point. -/
theorem componentVanishingLocusOver_of_isEmpty_points
    (hempty : IsEmpty (Space.points D.site D.base D.base_mem X)) :
    ComponentVanishingLocusOver D sX hX L s k :=
  fun W _ => (hempty.false (W.1.ambientGenericPoint D.site D.base D.base_mem)).elim

end ZeroCycleOfSection

end AlgebraicGeometry.Space

end
