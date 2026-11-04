module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFibreSum
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorFunctionFieldEmbedding

/-!
# Principal divisors at the canonical embeddings of Stacks 0ENK

In the situation of Stacks 0EDT let `W/B` be a good, *integral* algebraic space. Part (1) of
Stacks 0EQ6 asks of a summand that it be `div(f)` for a rational function `f ∈ R(W)^*`. Reading
`div(f)` requires, at every prime divisor `ξ` of `W`, an embedding
`R(W) → Q(𝒪^h_{W,ξ})` and the three ring-theoretic facts about `𝒪^h_{W,ξ}` that make the order
of vanishing along `ξ` defined — all of them conclusions of Stacks 0ENK.

For a good integral `W` these embeddings and facts are provided by
`AlgebraicGeometry.Space.genericFractionEmbedding`, and this file defines principal divisors
`div(f)` at those canonical embeddings.

## Main results

* `AlgebraicGeometry.Space.IsPrincipalDivisorCycleOfGood`: a `k`-cycle on a good integral `W/B`
  is `div(f)` for a unit `f` of `R(W)`, at the canonical embeddings of Stacks 0ENK.
* `AlgebraicGeometry.Space.isPrincipalDivisorCycleOfGood_neg`: the negative of such a cycle is
  again one, by `-div(f) = div(f⁻¹)`.
* `AlgebraicGeometry.Space.IsPrincipalDivisorCycleOfGood.isPrincipalDivisorCycle`: such a cycle
  is a principal divisor in the sense of `AlgebraicGeometry.Space.IsPrincipalDivisorCycle`.

## Tags

Stacks 0ENK, Stacks 0EQ1, Stacks 0EQ6.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- A `k`-cycle on a good, integral algebraic space `W/B` is a *principal divisor* when it is
`div(f)` for a rational function `f ∈ R(W)^*`, that is, when its coefficient family is
`AlgebraicGeometry.Space.principalDivisorCycleCoefficients` of a unit `f` of `R(W)` at the
canonical embeddings `R(W) → Q(𝒪^h_{W,ξ})` of Stacks 0ENK. -/
def IsPrincipalDivisorCycleOfGood (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hint : IsIntegralSpace D.site D.base D.base_mem Y) (k : ℤ) (c : CycleGroup D sY k) : Prop :=
  letI E := genericFractionEmbedding D.site D.base D.base_mem hY.1 hint.isDecentSpace hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
  letI := E.nontrivial
  letI := E.isNoetherianRing
  letI := E.krullDimLE
  ∃ (f : rationalFunctions D.site D.base D.base_mem hY.1) (hf : IsUnit f),
    (c : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) =
      principalDivisorCycleCoefficients D sY hY hint.isDecentSpace E.emb f
        fun W => hf.map (E.emb W)

/-- A principal divisor at the canonical embeddings of Stacks 0ENK is a principal divisor in the
sense of `AlgebraicGeometry.Space.IsPrincipalDivisorCycle`. -/
theorem IsPrincipalDivisorCycleOfGood.isPrincipalDivisorCycle {sY : Y ⟶ D.space}
    {hY : D.IsGood sY} {hint : IsIntegralSpace D.site D.base D.base_mem Y} {k : ℤ}
    {c : CycleGroup D sY k} (h : IsPrincipalDivisorCycleOfGood D sY hY hint k c) :
    IsPrincipalDivisorCycle D sY k c := by
  let E := genericFractionEmbedding D.site D.base D.base_mem hY.1 hint.isDecentSpace hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
  obtain ⟨f, ⟨g, rfl⟩, heq⟩ := h
  exact ⟨hY, hint, g, heq⟩

/-- The negative of a principal divisor is a principal divisor: `-div(f) = div(f⁻¹)`, the inverse
being taken in the ring of rational functions, where `f` is a unit. -/
theorem isPrincipalDivisorCycleOfGood_neg (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hint : IsIntegralSpace D.site D.base D.base_mem Y) (k : ℤ) {c : CycleGroup D sY k}
    (h : IsPrincipalDivisorCycleOfGood D sY hY hint k c) :
    IsPrincipalDivisorCycleOfGood D sY hY hint k (-c) := by
  let E := genericFractionEmbedding D.site D.base D.base_mem hY.1 hint.isDecentSpace hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
  let := E.nontrivial
  let := E.isNoetherianRing
  let := E.krullDimLE
  obtain ⟨f, hf, heq⟩ := h
  obtain ⟨w, hw⟩ := hf
  refine ⟨(↑w⁻¹ : rationalFunctions _ _ _ hY.1), w⁻¹.isUnit, ?_⟩
  have hgf : (↑w⁻¹ : rationalFunctions D.site D.base D.base_mem hY.1) * f = 1 := by
    rw [← hw]
    exact w.inv_mul
  have key := principalDivisorCycleCoefficients_of_mul_eq_one D sY hY hint.isDecentSpace E.emb
    (↑w⁻¹ : rationalFunctions D.site D.base D.base_mem hY.1) f
    (fun W => w⁻¹.isUnit.map (E.emb W)) (fun W => (hw ▸ w.isUnit).map (E.emb W)) hgf
  show ((-c : CycleGroup D sY k) :
      IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) = _
  rw [show ((-c : CycleGroup D sY k) :
      IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) =
    -(c : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) from rfl, heq, key]

end AlgebraicGeometry.Space

end
