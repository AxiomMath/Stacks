module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ChainBasis

/-!
# The degree-zero part of a graded divided-power polynomial algebra

The variables of a graded divided-power polynomial algebra all sit in positive degree, so
adjoining one of them does not change the degree-zero part. Consequently the degree-zero part of
the whole algebra is exactly the image of the coefficient algebra.

This file proves that. Unlike the construction of a monotone family of bases, the statement is
about submodules rather than about chosen bases, so it is invariant under reordering the
variables and the induction is an ordinary `Finset.induction` rather than a chain indexed by `ℕ`.
No countability hypothesis is needed.

## Main results

* `DividedPowers.TateResolution.OddVariableExtension.grade_eq_map_of_lt` and
  `DividedPowers.TateResolution.EvenVariableAlgebra.grade_eq_map_of_lt` — below the degree of the
  new variable, a homogeneous piece of a one-variable extension is the image of the
  corresponding piece of the coefficient algebra.
* `DividedPowers.TateResolution.inf_finiteVariableStageSubmodule_insert_le` and
  `DividedPowers.TateResolution.inf_finiteVariableStageSubmodule_le_filter` — a finite variable
  stage is unchanged, in degrees below the degrees of the variables concerned, by adjoining
  them.
* `DividedPowers.TateResolution.inf_finiteVariableStageSubmodule_le_range` — the degree-zero part
  of a finite variable stage consists of coefficients.
* `DividedPowers.TateResolution.mem_grade_zero_iff_exists_coefficient` — the degree-zero part of
  the whole algebra is the image of the coefficient algebra. This is the `degree_zero` field of
  a Tate resolution.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w z

section GradeZero

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

namespace OddVariableExtension

/-- Below the degree of the new variable, a homogeneous piece of an odd variable extension is the
image of the corresponding piece of the coefficient algebra: the shifted summand of
`grade_eq_sup_map` vanishes there. -/
public theorem grade_eq_map_of_lt (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] {d m : ℕ}
    (hm : m < d) :
    grade Aᵢ d m = (Aᵢ m).map (inclusionLinearMap Aᵢ d) := by
  rw [grade_eq_sup_map, ite_eq_right (by omega : ¬ d ≤ m), Submodule.map_bot, sup_bot_eq]

end OddVariableExtension

namespace EvenVariableAlgebra

/-- Below the degree of the new variable, a homogeneous piece of an even variable extension is
the image of the corresponding piece of the coefficient algebra: in `grade_eq_iSup_map` every
summand with a positive exponent of the new variable vanishes, so the join collapses to its
`n = 0` term. -/
public theorem grade_eq_map_of_lt (𝒜 : ℕ → Submodule R A) {d m : ℕ} (hm : m < d) :
    grade 𝒜 d m = (𝒜 m).map (monomialLinearMap (R := R) 0) := by
  rw [grade_eq_iSup_map]
  refine le_antisymm (iSup_le fun n => ?_) (le_iSup_of_le 0 (by simp))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [ite_eq_right (Nat.not_le.mpr (hm.trans_le (Nat.le_mul_of_pos_left d hn))),
      Submodule.map_bot]
    exact bot_le

end EvenVariableAlgebra

end GradeZero

section Stage

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [Ring P] [Algebra R P] [Ring A] [Algebra R A]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
  {γ : DividedPowerStructure 𝒜} {ι : P →ₐ[R] A}
  (h : GradedDividedPowerPolynomial 𝒜 γ ι)

/-- If every degree-`m` element of an extension `B` of a stage, read through an equivalence onto
a larger stage, comes from the smaller stage, then so does every degree-`m` element of the larger
stage. -/
private theorem exists_eq_coe_of_equiv {J : Type z} {T : J → A} {S U : Finset J} {B : Type w}
    [Ring B] (γ : DividedPowerStructure 𝒜) (ι : P →ₐ[R] A)
    (e : B ≃+* finiteVariableStage γ ι T U) {m : ℕ} {x : A} (hx0 : x ∈ 𝒜 m)
    (hxU : x ∈ finiteVariableStageSubmodule γ ι T U)
    (hz : ∀ z : B, ((e z : finiteVariableStage γ ι T U) : A) ∈ 𝒜 m →
      ∃ b : finiteVariableStage γ ι T S, ((e z : finiteVariableStage γ ι T U) : A) = b) :
    ∃ b : finiteVariableStage γ ι T S, x = b := by
  obtain ⟨z, rfl⟩ := exists_stageRingHom_eq γ ι T U e x hxU
  exact hz z hx0

/-- **Adjoining a variable does not enlarge a finite variable stage below the degree of that
variable.** The degree-`m` piece of the successor extension is the image of the degree-`m` piece
of the stage as soon as `m` is below the degree `j.1 + 1` of the new variable, by
`grade_eq_map_of_lt` in either parity. The degree-zero case, where the hypothesis is vacuous, is
what the `degree_zero` field of a Tate resolution needs.

As in `exists_basis_insert`, the next stage is described by a membership characterisation rather
than written as `insert j S`, because the `successor` field supplies its own decidable equality
on the index type. -/
public theorem inf_finiteVariableStageSubmodule_insert_le
    (S : Finset (Σ n : ℕ, h.indices n)) (j : Σ n : ℕ, h.indices n) (hj : j ∉ S)
    (U : Finset (Σ n : ℕ, h.indices n)) (hU : ∀ k, k ∈ U ↔ k = j ∨ k ∈ S)
    {m : ℕ} (hm : m ≤ j.1) :
    𝒜 m ⊓ finiteVariableStageSubmodule γ ι h.generator U ≤
      𝒜 m ⊓ finiteVariableStageSubmodule γ ι h.generator S := by
  rintro x ⟨hx0, hxU⟩
  obtain ⟨aS, -, Sᵢ, gS, cS, δS, -, hoddBr, hevenBr⟩ := h.successor S j hj
  let instJ : DecidableEq ((n : ℕ) × h.indices n) := Classical.decEq _
  have hUeq : (insert j S : Finset ((n : ℕ) × h.indices n)) = U := by
    ext k
    simp [hU k]
  rw [hUeq] at hoddBr hevenBr
  let instA : Algebra R (finiteVariableStage γ ι h.generator S) := aS
  let instG : GradedAlgebra Sᵢ := gS
  let instC : IsStrictlyGradedComm Sᵢ := cS
  suffices hb : ∃ b : finiteVariableStage γ ι h.generator S, x = b by
    obtain ⟨b, rfl⟩ := hb
    exact ⟨hx0, b.2⟩
  rcases Nat.even_or_odd (j.1 + 1) with heven | hodd
  · let instFact : Fact (Even (j.1 + 1)) := ⟨heven⟩
    obtain ⟨e, hcoeff, -, hgrade, -⟩ := hevenBr heven
    refine exists_eq_coe_of_equiv γ ι e hx0 hxU fun z hz => ?_
    have hz0 : z ∈ EvenVariableAlgebra.grade Sᵢ (j.1 + 1) m := (hgrade m z).mpr hz
    rw [EvenVariableAlgebra.grade_eq_map_of_lt Sᵢ (by omega : m < j.1 + 1)] at hz0
    obtain ⟨b, -, rfl⟩ := hz0
    exact ⟨b, by simpa using hcoeff b⟩
  · obtain ⟨e, hcoeff, -, hgrade, -⟩ := hoddBr hodd
    refine exists_eq_coe_of_equiv γ ι e hx0 hxU fun z hz => ?_
    have hz0 : z ∈ OddVariableExtension.grade Sᵢ (j.1 + 1) m := (hgrade m z).mpr hz
    rw [OddVariableExtension.grade_eq_map_of_lt Sᵢ (by omega : m < j.1 + 1)] at hz0
    obtain ⟨b, -, rfl⟩ := hz0
    exact ⟨b, hcoeff b⟩

/-- **A finite variable stage may be truncated to its variables of degree at most `m` without
changing its degree-`m` piece.**

The variables of degree greater than `m` are discarded one at a time by
`inf_finiteVariableStageSubmodule_insert_le`, which is why the induction is on the finite set of
variables ordered by strict inclusion rather than on the degree: each step removes one variable
and the remaining set is a strict subset with the same low-degree part. -/
public theorem inf_finiteVariableStageSubmodule_le_filter (m : ℕ)
    (S : Finset (Σ n : ℕ, h.indices n)) :
    𝒜 m ⊓ finiteVariableStageSubmodule γ ι h.generator S ≤
      𝒜 m ⊓ finiteVariableStageSubmodule γ ι h.generator (S.filter fun j => j.1 < m) := by
  classical
  induction S using Finset.strongInduction with
  | _ S ih =>
    by_cases hex : ∃ j, j ∈ S ∧ m ≤ j.1
    · obtain ⟨j, hjS, hj⟩ := hex
      have hins : ∀ k, k ∈ S ↔ k = j ∨ k ∈ S.erase j := fun k => by
        rw [← Finset.mem_insert, Finset.insert_erase hjS]
      have hfilt : (S.erase j).filter (fun k => k.1 < m) = S.filter (fun k => k.1 < m) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_erase, and_assoc]
        refine ⟨fun hk => ⟨hk.2.1, hk.2.2⟩, fun hk => ⟨?_, hk.1, hk.2⟩⟩
        rintro rfl
        omega
      refine le_trans (inf_finiteVariableStageSubmodule_insert_le h (S.erase j) j
        (Finset.notMem_erase j S) S hins hj) ?_
      rw [← hfilt]
      exact ih (S.erase j) (Finset.erase_ssubset hjS)
    · push Not at hex
      rw [Finset.filter_true_of_mem hex]

/-- **The degree-zero part of a finite variable stage consists of coefficients.** The induction
is an ordinary induction on the finite set of adjoined variables: the statement is about
submodules, so it does not depend on the order in which the variables are adjoined, and no
countability hypothesis on the index type is needed. -/
public theorem inf_finiteVariableStageSubmodule_le_range
    (S : Finset (Σ n : ℕ, h.indices n)) :
    𝒜 0 ⊓ finiteVariableStageSubmodule γ ι h.generator S ≤
      LinearMap.range (ι.toLinearMap : P →ₗ[R] A) := by
  classical
  induction S using Finset.induction with
  | empty =>
      rintro x ⟨-, hx⟩
      exact (mem_finiteVariableStage_empty_iff h x).mp hx
  | insert j T hj ih =>
      exact le_trans
        (inf_finiteVariableStageSubmodule_insert_le h T j hj _ (fun _ => Finset.mem_insert)
          (Nat.zero_le j.1)) ih

include h in
/-- **The degree-zero part of a graded divided-power polynomial algebra is exactly the image of
its coefficient algebra.**

Every variable has positive degree, so no stage contributes anything new in degree zero, and the
stages exhaust the algebra. This is the `degree_zero` field of a Tate resolution. -/
public theorem mem_grade_zero_iff_exists_coefficient (a : A) :
    a ∈ 𝒜 0 ↔ ∃ p : P, ι p = a := by
  refine ⟨fun ha => ?_, fun ha => ha.elim fun p hp => hp ▸ h.coefficient_mem p⟩
  have hle : 𝒜 0 ≤ LinearMap.range (ι.toLinearMap : P →ₗ[R] A) := by
    rw [← iSup_inf_finiteVariableStageSubmodule γ ι h.generator h.finite_support 0]
    exact iSup_le (inf_finiteVariableStageSubmodule_le_range h)
  exact hle ha

end Stage

end DividedPowers.TateResolution

end
