module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalence

/-!
# A principal divisor cycle is determined by its rational function

`AlgebraicGeometry.Space.IsPrincipalDivisorCycle` is the summand condition of rational
equivalence (Stacks 0EQ6, parts (1) and (2)): a `k`-cycle `c` on `W/B` is a principal divisor when
it is `div(f)` for some `f ∈ R(W)^*`. The order of vanishing `ord_Z(f)` at a prime divisor `Z`
with generic point `ξ` is read through an embedding `R(W) → Q(𝒪^h_{W,ξ})` (Stacks 0ENK); here it
is the canonical embedding `AlgebraicGeometry.Space.genericFractionEmbedding`, and the only other
quantified data are the propositions that `W` is good and integral.

The embedding has to be the canonical one. Were it an arbitrary ring map chosen independently at
every prime divisor, the predicate would degenerate: on `ℙ¹` over a field, taking the canonical
embedding composed with `s ↦ s²` at one point `p`, one rational function `f` would be a witness
both for `2[p] - [q]` and for `[p] - [q]`, so `[p]` would be rationally equivalent to zero and
`CH_0(ℙ¹)` would collapse.

With the canonical embedding one rational function gives one cycle: a `k`-cycle which is `div(f)`
for a given `f` is unique, whatever proofs of goodness and integrality are used and whatever the
degree `k`. So no single `f` witnesses two distinct cycles.

## Main definitions

* `AlgebraicGeometry.Space.IsPrincipalDivisorCycleOf`: the cycle `c` is `div(f)` for the given
  rational function `f`, read at the canonical embeddings of Stacks 0ENK.

## Main results

* `AlgebraicGeometry.Space.isPrincipalDivisorCycle_iff`: a cycle is a principal divisor exactly
  when it is `div(f)`, at the canonical embeddings, for some good and integral structure and some
  `f ∈ R(W)^*`.
* `AlgebraicGeometry.Space.IsPrincipalDivisorCycleOf.coe_eq` and
  `AlgebraicGeometry.Space.IsPrincipalDivisorCycleOf.eq`: the cycle is determined by `f`; two
  cycles that are `div(f)` for the same `f` are equal.
* `AlgebraicGeometry.Space.IsPrincipalDivisorCycleOf.not_and_of_ne`: two distinct cycles, such
  as `2[p] - [q]` and `[p] - [q]`, are never `div(f)` for the same `f`.
* `AlgebraicGeometry.Space.IsPrincipalDivisorCycleOf.apply_toIntegralClosedSubspace`: the
  coefficient of `div(f)` at a prime divisor `Z` is the canonical order of vanishing `ord_Z(f)`.
* `AlgebraicGeometry.Space.IsPrincipalDivisorCycleOf.add` and
  `AlgebraicGeometry.Space.isPrincipalDivisorCycle_add`: `div(fg) = div(f) + div(g)`, so the
  principal divisor cycles on `W` are closed under addition.

## References

* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENQ](https://stacks.math.columbia.edu/tag/0ENQ)
* [Stacks Project, Tag 0EQ1](https://stacks.math.columbia.edu/tag/0EQ1)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The `k`-cycle `c` on a good integral algebraic space `Y/B` is the principal divisor `div(f)`
of the given rational function `f ∈ R(Y)^*`: its coefficient family is
`AlgebraicGeometry.Space.principalDivisorCycleCoefficients` of `f`, read through the canonical
embeddings `R(Y) → Q(𝒪^h_{Y,ξ})` of Stacks 0ENK,
`AlgebraicGeometry.Space.genericFractionEmbedding`. -/
def IsPrincipalDivisorCycleOf (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hint : IsIntegralSpace D.site D.base D.base_mem Y) (k : ℤ)
    (f : (rationalFunctions D.site D.base D.base_mem hY.1)ˣ) (c : CycleGroup D sY k) : Prop :=
  letI E := genericFractionEmbedding D.site D.base D.base_mem hY.1 hint.isDecentSpace hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
  letI := E.nontrivial
  letI := E.isNoetherianRing
  letI := E.krullDimLE
  (c : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) =
    principalDivisorCycleCoefficients D sY hY hint.isDecentSpace E.emb
      (f : rationalFunctions D.site D.base D.base_mem hY.1) fun W => f.isUnit.map (E.emb W)

/-- A `k`-cycle is a principal divisor exactly when it is `div(f)`, at the canonical embeddings
of Stacks 0ENK, for some proofs that `Y/B` is good and integral and some `f ∈ R(Y)^*`. -/
theorem isPrincipalDivisorCycle_iff (sY : Y ⟶ D.space) (k : ℤ) (c : CycleGroup D sY k) :
    IsPrincipalDivisorCycle D sY k c ↔
      ∃ (hY : D.IsGood sY) (hint : IsIntegralSpace D.site D.base D.base_mem Y)
        (f : (rationalFunctions D.site D.base D.base_mem hY.1)ˣ),
        IsPrincipalDivisorCycleOf D sY hY hint k f c :=
  Iff.rfl

namespace IsPrincipalDivisorCycleOf

variable {D} {sY : Y ⟶ D.space} {hY : D.IsGood sY}
    {hint : IsIntegralSpace D.site D.base D.base_mem Y}
    {f : (rationalFunctions D.site D.base D.base_mem hY.1)ˣ}

/-- Two cycles which are `div(f)` for the same `f` have the same coefficients, whatever proofs of
goodness and integrality witness them and whatever their degrees. -/
theorem coe_eq {hY' : D.IsGood sY} {hint' : IsIntegralSpace D.site D.base D.base_mem Y}
    {k k' : ℤ} {c : CycleGroup D sY k} {c' : CycleGroup D sY k'}
    (hc : IsPrincipalDivisorCycleOf D sY hY hint k f c)
    (hc' : IsPrincipalDivisorCycleOf D sY hY' hint' k' f c') :
    (c : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) = c' :=
  hc.trans hc'.symm

/-- In a fixed degree `k`, two `k`-cycles which are `div(f)` for the same `f` are equal. -/
theorem eq {hY' : D.IsGood sY} {hint' : IsIntegralSpace D.site D.base D.base_mem Y} {k : ℤ}
    {c c' : CycleGroup D sY k} (hc : IsPrincipalDivisorCycleOf D sY hY hint k f c)
    (hc' : IsPrincipalDivisorCycleOf D sY hY' hint' k f c') : c = c' :=
  Subtype.ext (hc.coe_eq hc')

/-- Two distinct `k`-cycles, such as `2[p] - [q]` and `[p] - [q]` on a curve, are never both the
principal divisor of the same rational function `f`. -/
theorem not_and_of_ne {hY' : D.IsGood sY} {hint' : IsIntegralSpace D.site D.base D.base_mem Y}
    {k : ℤ} {c c' : CycleGroup D sY k} (hne : c ≠ c') :
    ¬ (IsPrincipalDivisorCycleOf D sY hY hint k f c ∧
      IsPrincipalDivisorCycleOf D sY hY' hint' k f c') :=
  fun h => hne (h.1.eq h.2)

/-- The coefficient of `div(f)` at the integral closed subspace underlying a prime divisor `Z` is
the order of vanishing `ord_Z(f)` of the image of `f` under the canonical embedding
`R(Y) → Q(𝒪^h_{Y,ξ})` of Stacks 0ENK. -/
theorem apply_toIntegralClosedSubspace {k : ℤ} {c : CycleGroup D sY k}
    (hc : IsPrincipalDivisorCycleOf D sY hY hint k f c)
    (Z : PrimeDivisor D.site D.base D.base_mem Y) :
    (c : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ)
        (Z.toIntegralClosedSubspace D.site D.base D.base_mem) =
      (genericFractionEmbedding D.site D.base D.base_mem hY.1 hint.isDecentSpace hint
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)).ord f Z := by
  let E := genericFractionEmbedding D.site D.base D.base_mem hY.1 hint.isDecentSpace hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
  let := E.nontrivial
  let := E.isNoetherianRing
  let := E.krullDimLE
  rw [show (c : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) = _ from hc]
  exact principalDivisorCycleCoefficients_toIntegralClosedSubspace D sY hY hint.isDecentSpace
    E.emb (f : rationalFunctions D.site D.base D.base_mem hY.1)
    (fun W => f.isUnit.map (E.emb W)) Z

/-- `div(fg) = div(f) + div(g)`: the sum of the principal divisors of two rational functions is
the principal divisor of their product. -/
theorem add {k : ℤ} {g : (rationalFunctions D.site D.base D.base_mem hY.1)ˣ}
    {c c' : CycleGroup D sY k} (hc : IsPrincipalDivisorCycleOf D sY hY hint k f c)
    (hc' : IsPrincipalDivisorCycleOf D sY hY hint k g c') :
    IsPrincipalDivisorCycleOf D sY hY hint k (f * g) (c + c') := by
  let E := genericFractionEmbedding D.site D.base D.base_mem hY.1 hint.isDecentSpace hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
  let := E.nontrivial
  let := E.isNoetherianRing
  let := E.krullDimLE
  funext Z
  change (c : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) Z +
      (c' : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) Z = _
  rw [show (c : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) = _ from hc,
    show (c' : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) = _ from hc']
  by_cases h : codimension
      (integralClosedSubspaceSupport D.site D.base D.base_mem hY.1 Z) = 1
  · simp only [principalDivisorCycleCoefficients, dite_eq_left h]
    exact (E.ord_mul_apply f g _).symm
  · simp only [principalDivisorCycleCoefficients, dite_eq_right h, add_zero]

end IsPrincipalDivisorCycleOf

/-- The principal divisor cycles on `Y` are closed under addition: if `c = div(f)` and
`c' = div(g)` then `c + c' = div(fg)`. -/
theorem isPrincipalDivisorCycle_add (sY : Y ⟶ D.space) (k : ℤ) {c c' : CycleGroup D sY k}
    (hc : IsPrincipalDivisorCycle D sY k c) (hc' : IsPrincipalDivisorCycle D sY k c') :
    IsPrincipalDivisorCycle D sY k (c + c') := by
  obtain ⟨hY, hint, f, hf⟩ := hc
  obtain ⟨_, _, g, hg⟩ := hc'
  exact ⟨hY, hint, f * g, IsPrincipalDivisorCycleOf.add hf hg⟩

end AlgebraicGeometry.Space

end
