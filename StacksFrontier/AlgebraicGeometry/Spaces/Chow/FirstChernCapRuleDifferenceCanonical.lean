module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapRationalEquivalenceCanonicalSummand
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaTameCarrier

/-!
# Two component rules of Stacks 0EQJ which differ by principal divisors

In Situation 0EDT let `Y/B` be good and let `R₁`, `R₂` be two component rules of Stacks 0EQJ on
`Y`: each assigns to an integral closed subspace `T ⊆ Y` of δ-dimension `k + 1` a `k`-cycle on `T`.
If, at every `T` occurring in a `(k+1)`-cycle `β`, the two values either agree or differ by a
principal divisor on `T` — read at the canonical embeddings of Stacks 0ENK — with `|T|` inside a
fixed subset `S ⊆ |Y|`, then the two cap products `c₁ ∩ β` differ by a cycle rationally equivalent
to zero at the canonical embeddings **within `S`**.

This is the bookkeeping behind the remark that the cap product of Stacks 0EQJ does not depend on
the choice of the nonzero meromorphic sections of `ℒ|_T` (Stacks 0EQE part (2), Stacks 0EPT),
with the carrier of the rational equivalence kept: the members of the presenting family are the
`T` at which the two values differ, and nothing else.

## Main results

* `AlgebraicGeometry.Space.IsPrincipalDivisorCycleOfGood.add`,
  `AlgebraicGeometry.Space.IsPrincipalDivisorCycleOfGood.zsmul` and
  `AlgebraicGeometry.Space.isPrincipalDivisorCycleOfGood_zero`: the principal divisor cycles at the
  canonical embeddings form a subgroup, by Stacks 0ENQ.
* `AlgebraicGeometry.Space.IsRationallyEquivalentToZeroWithinCanonical.neg` and `.sub`.
* `AlgebraicGeometry.Space.isRationallyEquivalentToZeroWithinCanonical_firstChernCapCycleMap_sub`:
  the comparison of the two cap products.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENQ](https://stacks.math.columbia.edu/tag/0ENQ)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Principal divisor cycles at the canonical embeddings form a subgroup -/

section Principal

variable {D : BaseSpaceDimensionSituation.{u}}
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sY : Y ⟶ D.space}
    {hY : D.IsGood sY} {hint : IsIntegralSpace D.site D.base D.base_mem Y} {k : ℤ}

/-- **Stacks 0ENQ at the canonical embeddings.** A sum of two principal divisor cycles is a
principal divisor cycle: `div(f) + div(g) = div(fg)`. -/
theorem IsPrincipalDivisorCycleOfGood.add {c c' : CycleGroup D sY k}
    (h : IsPrincipalDivisorCycleOfGood D sY hY hint k c)
    (h' : IsPrincipalDivisorCycleOfGood D sY hY hint k c') :
    IsPrincipalDivisorCycleOfGood D sY hY hint k (c + c') := by
  let E := genericFractionEmbedding D.site D.base D.base_mem hY.1 hint.isDecentSpace hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
  let := E.nontrivial
  let := E.isNoetherianRing
  let := E.krullDimLE
  obtain ⟨f, hf, hc⟩ := h
  obtain ⟨g, hg, hc'⟩ := h'
  refine ⟨((hf.unit * hg.unit : (rationalFunctions D.site D.base D.base_mem hY.1)ˣ) :
    rationalFunctions D.site D.base D.base_mem hY.1), (hf.unit * hg.unit).isUnit, ?_⟩
  funext W
  change c.1 W + c'.1 W = _
  rw [show c.1 W = _ from congrFun hc W, show c'.1 W = _ from congrFun hc' W]
  simp only [principalDivisorCycleCoefficients]
  split_ifs with hcod
  · exact (E.ord_mul_apply hf.unit hg.unit
      (W.toPrimeDivisor D.site D.base D.base_mem hY.1 hcod)).symm
  · rfl

/-- The zero cycle is the principal divisor of `1`. -/
theorem isPrincipalDivisorCycleOfGood_zero :
    IsPrincipalDivisorCycleOfGood D sY hY hint k 0 := by
  let E := genericFractionEmbedding D.site D.base D.base_mem hY.1 hint.isDecentSpace hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
  let := E.nontrivial
  let := E.isNoetherianRing
  let := E.krullDimLE
  refine ⟨1, isUnit_one, ?_⟩
  funext W
  change (0 : ℤ) = _
  simp only [principalDivisorCycleCoefficients]
  split_ifs with hcod
  · exact (congrFun E.ord_one (W.toPrimeDivisor D.site D.base D.base_mem hY.1 hcod)).symm
  · rfl

/-- An integer multiple of a principal divisor cycle is a principal divisor cycle:
`a · div(f) = div(f^a)`. -/
theorem IsPrincipalDivisorCycleOfGood.zsmul {c : CycleGroup D sY k}
    (h : IsPrincipalDivisorCycleOfGood D sY hY hint k c) (a : ℤ) :
    IsPrincipalDivisorCycleOfGood D sY hY hint k (a • c) := by
  induction a using Int.induction_on with
  | zero => rw [zero_smul]; exact isPrincipalDivisorCycleOfGood_zero
  | succ n ih => rw [add_smul, one_smul]; exact ih.add h
  | pred n ih =>
    rw [sub_smul, one_smul, sub_eq_add_neg]
    exact ih.add (isPrincipalDivisorCycleOfGood_neg D sY hY hint k h)

/-- A difference of two principal divisor cycles is a principal divisor cycle. -/
theorem IsPrincipalDivisorCycleOfGood.sub {c c' : CycleGroup D sY k}
    (h : IsPrincipalDivisorCycleOfGood D sY hY hint k c)
    (h' : IsPrincipalDivisorCycleOfGood D sY hY hint k c') :
    IsPrincipalDivisorCycleOfGood D sY hY hint k (c - c') := by
  rw [sub_eq_add_neg]
  exact h.add (isPrincipalDivisorCycleOfGood_neg D sY hY hint k h')

end Principal

/-! ### Negation and difference of rational equivalences with a carrier -/

section Within

variable {D : BaseSpaceDimensionSituation.{u}}
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sX : X ⟶ D.space}
    {hX : D.IsGood sX} {k : ℤ} {α β : CycleGroup D sX k}
    {T : Set (points D.site D.base D.base_mem X)}

/-- The negative of a cycle rationally equivalent to zero within `T` is rationally equivalent to
zero within `T`, through the same family with the inverse functions. -/
theorem IsRationallyEquivalentToZeroWithinCanonical.neg
    (h : IsRationallyEquivalentToZeroWithinCanonical.{v} D sX hX k α T) :
    IsRationallyEquivalentToZeroWithinCanonical.{v} D sX hX k (-α) T := by
  obtain ⟨J, W, hWfin, c, hsub, hdim, hprin, hsum⟩ := h
  refine ⟨J, W, hWfin, fun j => -c j, hsub, hdim,
    fun j => isPrincipalDivisorCycleOfGood_neg D _ _ _ k (hprin j), ?_⟩
  rw [hsum]
  refine Subtype.ext (funext fun Z => ?_)
  change -((cycleFamilySum D sX hX W hWfin k c).1 Z) = _
  rw [cycleFamilySum_apply, cycleFamilySum_apply, ← finsum_neg_distrib]
  refine finsum_congr fun j => ?_
  rw [map_neg]
  rfl

/-- The difference of two cycles rationally equivalent to zero within `T` is rationally
equivalent to zero within `T`. -/
theorem IsRationallyEquivalentToZeroWithinCanonical.sub
    (hα : IsRationallyEquivalentToZeroWithinCanonical.{v} D sX hX k α T)
    (hβ : IsRationallyEquivalentToZeroWithinCanonical.{v} D sX hX k β T) :
    IsRationallyEquivalentToZeroWithinCanonical.{v} D sX hX k (α - β) T := by
  rw [sub_eq_add_neg]
  exact hα.add hβ.neg

end Within

/-! ### Two component rules differing by principal divisors -/

section RuleDifference

variable (D : BaseSpaceDimensionSituation.{u})
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (k : ℤ)

/-- **Two component rules of Stacks 0EQJ differing by principal divisors give cap products
differing by a rational equivalence, with its carrier.**  Let `R₁`, `R₂` be component rules on a
good `Y/B`, let `β ∈ Z_{k+1}(Y)` and let `S ⊆ |Y|`.  Suppose that at every integral closed
subspace `T ⊆ Y` occurring in `β` at which the two rules disagree, the difference `R₁(T) - R₂(T)`
is a principal divisor on `T` at the canonical embeddings of Stacks 0ENK and `|T| ⊆ S`.  Then

`c₁ ∩ β` at `R₁`  minus  `c₁ ∩ β` at `R₂`

is rationally equivalent to zero at the canonical embeddings within `S`.

Both cap products are the locally finite sums `∑_T β(T) · (T → Y)_* R_i(T)` over the support of
`β` (`AlgebraicGeometry.Space.firstChernCapCycleMap_eq_cycleFamilySum`), so their difference is
the sum of the `β(T) · (R₁(T) - R₂(T))`; the terms at which the rules agree vanish, and the
remaining ones form the presenting family. -/
theorem isRationallyEquivalentToZeroWithinCanonical_firstChernCapCycleMap_sub
    (R₁ R₂ : FirstChernComponentCycleRule D sY k) (β : CycleGroup D sY (k + 1))
    (S : Set (points D.site D.base D.base_mem Y))
    (h : ∀ (T : IntegralClosedSubspace D.site D.base D.base_mem Y)
      (hT : deltaDimension D sY T = k + 1), β.1 T ≠ 0 → R₁ T hT ≠ R₂ T hT →
        IsPrincipalDivisorCycleOfGood D (T.subspace.ι ≫ sY)
            (isGood_integralClosedSubspace D sY hY T) T.isIntegralSpace k (R₁ T hT - R₂ T hT) ∧
          subspacePointSet D.site D.base D.base_mem Y T.subspace ⊆ S) :
    IsRationallyEquivalentToZeroWithinCanonical.{u + 1} D sY hY k
      (firstChernCapCycleMap D sY hY k R₁ β - firstChernCapCycleMap D sY hY k R₂ β) S := by
  classical
  have hcov : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem Y, β.1 W ≠ 0 →
      ∃ i : {W : IntegralClosedSubspace D.site D.base D.base_mem Y // β.1 W ≠ 0}, i.1 = W :=
    fun W hW => ⟨⟨W, hW⟩, rfl⟩
  have hcap := fun R => firstChernCapCycleMap_eq_cycleFamilySum D sY hY k R β Subtype.val
    Subtype.val_injective (locallyFinite_cycleSupport β) (fun i => β.2.2 i.1 i.2) hcov
  rw [hcap R₁, hcap R₂, ← cycleFamilySum_sub,
    cycleFamilySum_eq_cycleFamilySum_subtype D sY hY _ _ k _
      (fun i => R₁ i.1 (β.2.2 i.1 i.2) ≠ R₂ i.1 (β.2.2 i.1 i.2))
      (fun i hi => by rw [not_not.1 hi, sub_self])]
  refine ⟨{i : {W : IntegralClosedSubspace D.site D.base D.base_mem Y // β.1 W ≠ 0} //
      R₁ i.1 (β.2.2 i.1 i.2) ≠ R₂ i.1 (β.2.2 i.1 i.2)}, fun j => j.1.1,
    ((locallyFinite_cycleSupport β).comp_injective Subtype.val_injective),
    fun j => β.1 j.1.1 • R₁ j.1.1 (β.2.2 j.1.1 j.1.2) - β.1 j.1.1 • R₂ j.1.1 (β.2.2 j.1.1 j.1.2),
    fun j => (h j.1.1 _ j.1.2 j.2).2, fun j => β.2.2 j.1.1 j.1.2, fun j => ?_, rfl⟩
  have hj := ((h j.1.1 _ j.1.2 j.2).1.zsmul (β.1 j.1.1))
  rwa [smul_sub] at hj

end RuleDifference

end AlgebraicGeometry.Space

end
