module

public import Mathlib.NumberTheory.Padics.Complex
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Valuation.Domination
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings

/-!
# The ring of integers of the `p`-adic complex numbers as an adic valuation ring

The ring of integers `PadicComplexInt p` of the field `ℂ_[p]` of `p`-adic complex numbers is a
valuation ring whose topology is the `(p)`-adic one, which is complete, and whose maximal ideal
is the radical of `(p)` but is not finitely generated. It is therefore an example of a valuation
ring `(A, 𝔪, κ)` which is `(π)`-adically complete for some nonzero `π ∈ 𝔪` while `𝔪` is not
finitely generated: take `A = 𝒪_{ℂ_p}` and `π = p`.

## Main results

* `PadicComplexInt.instIsLinearTopology`: the topology of `PadicComplexInt p` is linear.
* `PadicComplexInt.isAdic_span_p`: that topology is the `(p)`-adic topology.
* `PadicComplexInt.isComplete`: `PadicComplexInt p` is separated and complete.
* `PadicComplexInt.natCast_mem_maximalIdeal`: `p` lies in the maximal ideal.
* `PadicComplexInt.radical_span_p`: the radical of `(p)` is the maximal ideal.
* `PadicComplexInt.isValuationRing`: `PadicComplexInt p` is a valuation ring.
* `PadicComplexInt.not_fg_maximalIdeal`: its maximal ideal is not finitely generated.

## Implementation notes

The ring `PadicComplexInt p` is the valuation subring of the rank-one valuation
`(PadicComplex.valued p).v` of `ℂ_[p]`, so membership in a power of the ideal `(p)` is a bound
on that valuation; `mem_span_p_pow_iff_valuation_le` records this translation, and the proofs
below all run through it. Completeness is `TopologicalRing.IsComplete`, which is separatedness
together with completeness for the canonical right uniformity of the additive group; it follows
from the valuation subring being closed in the complete field `ℂ_[p]`. That the maximal ideal is
not finitely generated uses that `ℂ_[p]` is algebraically closed: a square root of a generator
still lies in the maximal ideal, yet has strictly larger valuation than the generator.

## References

* [Stacks Project, Tag 0CB8](https://stacks.math.columbia.edu/tag/0CB8)
-/

@[expose] public section

open IsLocalRing Valuation
open scoped NNReal Topology

namespace PadicComplexInt

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- An element of the ring of integers of `ℂ_[p]` lies in the `n`-th power of the ideal `(p)`
exactly when its valuation is at most the `n`-th power of the valuation of `p`. -/
private theorem mem_span_p_pow_iff_valuation_le (n : ℕ) (x : PadicComplexInt p) :
    x ∈ (Ideal.span {(p : PadicComplexInt p)} ^ n) ↔
      (PadicComplex.valued p).v.restrict (x : ℂ_[p]) ≤
        (PadicComplex.valued p).v.restrict (p : ℂ_[p]) ^ n := by
  let v := (PadicComplex.valued p).v
  rw [Ideal.span_singleton_pow]
  show x ∈ (Ideal.span {((p : PadicComplexInt p) ^ n)} : Set (PadicComplexInt p)) ↔ _
  rw [(PadicComplexInt.integers p).coe_span_singleton_eq_setOfPred_le_v_algebraMap]
  show v (x : ℂ_[p]) ≤ v (((p : PadicComplexInt p) ^ n) : ℂ_[p]) ↔ _
  rw [show (((p : PadicComplexInt p) ^ n) : ℂ_[p]) = (p : ℂ_[p]) ^ n by norm_cast, ← map_pow]
  exact (v.restrict_le_iff).symm

/-- The valuation of `p` in `ℂ_[p]` is `1 / p`, in particular it is less than one. -/
private theorem valuation_p_lt_one : (PadicComplex.valued p).v (p : ℂ_[p]) < 1 := by
  rw [PadicComplex.valuation_p]
  simpa using (one_div_lt_one_div
    (show (0 : ℝ≥0) < p by exact_mod_cast (Fact.out : Nat.Prime p).pos)
    (by norm_num : (0 : ℝ≥0) < 1)).2 (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt)

/-- The restricted valuation of `p` in `ℂ_[p]` is nonzero. -/
private theorem restrict_natCast_ne_zero :
    (PadicComplex.valued p).v.restrict (p : ℂ_[p]) ≠ 0 :=
  (Valuation.ne_zero_iff _).2 (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero)

/-- An element of `ℂ_[p]` of valuation less than one has restricted valuation less than one. -/
private theorem restrict_lt_one_of_lt_one {x : ℂ_[p]} (h : (PadicComplex.valued p).v x < 1) :
    (PadicComplex.valued p).v.restrict x < 1 := by
  rw [Valuation.restrict_lt_iff_lt_embedding]
  simpa using h

/-- **Stacks 0CB8.** The topology of the ring of integers of `ℂ_[p]`, inherited from `ℂ_[p]`, is
the `(p)`-adic topology. -/
@[stacks 0CB8 "the p-adic complex integers"]
theorem isAdic_span_p :
    IsAdic (Ideal.span ({(p : PadicComplexInt p)} : Set (PadicComplexInt p))) := by
  let v := (PadicComplex.valued p).v
  let q := v.restrict (p : ℂ_[p])
  have hq0 : q ≠ 0 := restrict_natCast_ne_zero p
  have hqlt : q < 1 := restrict_lt_one_of_lt_one p (valuation_p_lt_one p)
  let qu := Units.mk0 q hq0
  have hqult : qu < 1 := hqlt
  apply isAdic_iff.mpr
  constructor
  · intro n
    have hset : ((Ideal.span {(p : PadicComplexInt p)} ^ n : Ideal (PadicComplexInt p)) :
        Set (PadicComplexInt p)) =
      Subtype.val ⁻¹' {z : ℂ_[p] | v.restrict z ≤ q ^ n} := by
      ext x
      simpa [q] using mem_span_p_pow_iff_valuation_le p n x
    rw [hset]
    exact (Valued.isOpen_closedBall (ℂ_[p]) (pow_ne_zero n hq0)).preimage
      continuous_subtype_val
  · intro U hU
    have hbasis : (𝓝 (0 : PadicComplexInt p)).HasBasis (fun (_ : Units
        (MonoidWithZeroHom.ValueGroup₀ (.ofClass v))) => True)
        (fun γ => {x : PadicComplexInt p | v.restrict (x : ℂ_[p]) < γ.1}) := by
      rw [nhds_subtype_eq_comap]
      exact (Valued.hasBasis_nhds_zero (ℂ_[p]) ℝ≥0).comap
        (Subtype.val : PadicComplexInt p → ℂ_[p])
    obtain ⟨γ, -, hγ⟩ := hbasis.mem_iff.mp hU
    obtain ⟨n, hn⟩ := exists_pow_lt hqult γ
    have hnval : (qu ^ n : MonoidWithZeroHom.ValueGroup₀ (.ofClass v)) < γ.1 := hn
    refine ⟨n, fun x hx => ?_⟩
    have hxle : v.restrict (x : ℂ_[p]) ≤ (qu ^ n :
        MonoidWithZeroHom.ValueGroup₀ (.ofClass v)) := by
      simpa [qu, q] using (mem_span_p_pow_iff_valuation_le p n x).1 hx
    exact hγ (hxle.trans_lt hnval)

/-- **Stacks 0CB8.** The topology of the ring of integers of `ℂ_[p]` is linear: the open ideals
form a basis of neighbourhoods of zero. -/
@[stacks 0CB8 "the p-adic complex integers"]
instance instIsLinearTopology : IsLinearTopology (PadicComplexInt p) (PadicComplexInt p) :=
  (isAdic_span_p p) ▸
    (Ideal.span ({(p : PadicComplexInt p)} : Set (PadicComplexInt p))).isLinearTopology

/-- **Stacks 0CB8.** The ring of integers of `ℂ_[p]` is separated and complete for its
topology. -/
@[stacks 0CB8 "the p-adic complex integers"]
theorem isComplete : TopologicalRing.IsComplete (PadicComplexInt p) := by
  refine ⟨inferInstance, ?_⟩
  have hclosed : IsClosed (PadicComplexInt p : Set ℂ_[p]) :=
    Valued.isClosed_valuationSubring (ℂ_[p])
  have hunif : IsTopologicalAddGroup.rightUniformSpace (PadicComplexInt p) =
      (inferInstance : UniformSpace (PadicComplexInt p)) :=
    IsUniformAddGroup.rightUniformSpace_eq
  exact hunif.symm ▸ hclosed.completeSpace_coe

/-- **Stacks 0CB8.** The element `p` of the ring of integers of `ℂ_[p]` lies in its maximal
ideal; in particular it is nonzero and not a unit. -/
@[stacks 0CB8 "the p-adic complex integers"]
theorem natCast_mem_maximalIdeal :
    (p : PadicComplexInt p) ∈ maximalIdeal (PadicComplexInt p) := by
  show (p : (PadicComplex.valued p).v.valuationSubring) ∈
    maximalIdeal ((PadicComplex.valued p).v.valuationSubring)
  rw [Valuation.mem_maximalIdeal_iff]
  show (PadicComplex.valued p).v ((p : PadicComplexInt p) : ℂ_[p]) < 1
  rw [show ((p : PadicComplexInt p) : ℂ_[p]) = (p : ℂ_[p]) by norm_cast]
  exact valuation_p_lt_one p

/-- **Stacks 0CB8.** The radical of the ideal `(p)` of the ring of integers of `ℂ_[p]` is its
maximal ideal. -/
@[stacks 0CB8 "the p-adic complex integers"]
theorem radical_span_p :
    (Ideal.span ({(p : PadicComplexInt p)} : Set (PadicComplexInt p))).radical =
      maximalIdeal (PadicComplexInt p) := by
  let v := (PadicComplex.valued p).v
  let O := PadicComplexInt p
  apply le_antisymm
  · exact (maximalIdeal.isMaximal O).isPrime.radical_le_iff.mpr
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (natCast_mem_maximalIdeal p)))
  · intro x hx
    rw [Ideal.mem_radical_iff]
    have hxv : v (x : ℂ_[p]) < 1 :=
      (Valuation.mem_maximalIdeal_iff (K := ℂ_[p]) v).1 hx
    by_cases hx0 : (x : ℂ_[p]) = 0
    · obtain rfl : x = 0 := Subtype.ext hx0
      exact ⟨1, by simp⟩
    · have hq0 : v.restrict (x : ℂ_[p]) ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
      let xu := Units.mk0 (v.restrict (x : ℂ_[p])) hq0
      let pu := Units.mk0 (v.restrict (p : ℂ_[p])) (restrict_natCast_ne_zero p)
      have hxult : xu < 1 := restrict_lt_one_of_lt_one p hxv
      obtain ⟨n, hn⟩ := exists_pow_lt hxult pu
      have hpow : v.restrict (x : ℂ_[p]) ^ n < v.restrict (p : ℂ_[p]) := hn
      refine ⟨n, ?_⟩
      simpa only [pow_one] using (mem_span_p_pow_iff_valuation_le p 1 (x ^ n)).2
        (by
          show v.restrict ((x : ℂ_[p]) ^ n) ≤ v.restrict (p : ℂ_[p]) ^ 1
          simpa only [map_pow, pow_one] using hpow.le)

/-- **Stacks 0CB8.** The ring of integers of `ℂ_[p]` is a valuation ring: inside its fraction
field it is maximal for the domination order among local subrings. -/
@[stacks 0CB8 "the p-adic complex integers"]
theorem isValuationRing : IsValuationRing (PadicComplexInt p) :=
  isValuationRing_of_valuationRing (PadicComplexInt p)

/-- **Stacks 0CB8.** The maximal ideal of the ring of integers of `ℂ_[p]` is not finitely
generated: the valuation of `ℂ_[p]` takes arbitrarily small positive values, since `ℂ_[p]` is
algebraically closed, so no element of the maximal ideal generates it. -/
@[stacks 0CB8 "the p-adic complex integers"]
theorem not_fg_maximalIdeal : ¬ (maximalIdeal (PadicComplexInt p)).FG := by
  intro hfg
  let O := PadicComplexInt p
  let v := (PadicComplex.valued p).v
  have hp0O : (p : O) ≠ 0 := fun h =>
    Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero (congrArg Subtype.val h)
  obtain ⟨a, ha⟩ := IsBezout.isPrincipal_of_FG (maximalIdeal O) hfg
  have haM : a ∈ maximalIdeal O := by
    rw [ha]
    exact Ideal.subset_span (by simp)
  have ha0 : a ≠ 0 := by
    intro hz
    have hp : (p : O) ∈ O ∙ a := by
      rw [← ha]
      exact natCast_mem_maximalIdeal p
    rw [hz] at hp
    exact hp0O (by simpa using hp)
  have haValLt : v (a : ℂ_[p]) < 1 :=
    (Valuation.mem_maximalIdeal_iff (K := ℂ_[p]) v).1 haM
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ_[p]) two_pos
  have hyValSq : v y ^ 2 = v (a : ℂ_[p]) := by rw [← map_pow, hy]
  have hyValLt : v y < 1 := by
    by_contra h
    have hsq : 1 ≤ (v y) ^ 2 := one_le_pow₀ (le_of_not_gt h)
    rw [hyValSq] at hsq
    exact (not_le_of_gt haValLt) hsq
  have hyValPos : 0 < v y := by
    by_contra h
    have hy0 : v y = 0 := le_antisymm (le_of_not_gt h) (by positivity)
    have hav0 : v (a : ℂ_[p]) = 0 := by simpa [hy0] using hyValSq.symm
    exact ((Valuation.ne_zero_iff _).2 (by exact_mod_cast ha0)) hav0
  have haValLtY : v (a : ℂ_[p]) < v y := by
    rw [← hyValSq]
    exact pow_lt_self_of_lt_one₀ hyValPos hyValLt (by norm_num)
  let yO : O := ⟨y, (Valuation.mem_valuationSubring_iff v y).2 hyValLt.le⟩
  have hySpan : yO ∈ O ∙ a := by
    rw [← ha]
    exact (Valuation.mem_maximalIdeal_iff (K := ℂ_[p]) v).2 hyValLt
  have hyMem : yO ∈ (Ideal.span {a} : Set O) := hySpan
  rw [(PadicComplexInt.integers p).coe_span_singleton_eq_setOfPred_le_v_algebraMap a] at hyMem
  exact (not_le_of_gt haValLtY) hyMem

end PadicComplexInt

end
