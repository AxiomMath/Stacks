module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.DegreeZeroStage

/-!
# The degree-one part of a graded divided-power polynomial algebra

The variables of a graded divided-power polynomial algebra sit in positive degree, so the only
ones that can contribute to degree one are those of degree one, and they contribute linearly:
a divided power or a product of two variables of degree one already has degree two. So the
degree-one part of the algebra is spanned, over the coefficient algebra, by the variables of
degree one.

This file proves that, by the same induction over the finite variable stages that computes the
degree-zero part: the statement is about submodules, so it does not depend on the order in which
the variables are adjoined and no countability hypothesis is needed. The one-variable step is
the odd extension's `grade_eq_sup_map` at degree one, whose two summands are the degree-one part
of the stage — handled by the induction — and the degree-zero part of the stage multiplied by
the new variable, which `inf_finiteVariableStageSubmodule_le_range` identifies with the
coefficients.

## Main definitions

* `DividedPowers.TateResolution.gradeOneGenerators` — the coefficients together with the
  coefficient multiples of the variables of degree one.

## Main results

* `DividedPowers.TateResolution.inf_finiteVariableStageSubmodule_one_le` — the degree-one part of
  a finite variable stage whose variables all have degree one is spanned by those generators.
* `DividedPowers.TateResolution.grade_one_le_span` — the degree-one part of the whole algebra is
  spanned by those generators.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

section Stage

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [Ring P] [Algebra R P] [Ring A] [Algebra R A]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
  {γ : DividedPowerStructure 𝒜} {ι : P →ₐ[R] A}
  (h : GradedDividedPowerPolynomial 𝒜 γ ι)

/-- The coefficients of a graded divided-power polynomial algebra together with the coefficient
multiples of its variables of degree one. The degree-one part of the algebra is the span of this
set, by `grade_one_le_span`. -/
public def gradeOneGenerators : Set A :=
  Set.range (fun p : P => ι p) ∪
    {x : A | ∃ (p : P) (j : Σ n : ℕ, h.indices n), j.1 = 0 ∧ x = ι p * h.generator j}

/-- A coefficient is one of the degree-one generators. -/
public theorem coefficient_mem_gradeOneGenerators (p : P) : ι p ∈ gradeOneGenerators h :=
  Or.inl ⟨p, rfl⟩

/-- A coefficient multiple of a variable of degree one is one of the degree-one generators. -/
public theorem mul_generator_mem_gradeOneGenerators (p : P) (j : Σ n : ℕ, h.indices n)
    (hj : j.1 = 0) : ι p * h.generator j ∈ gradeOneGenerators h :=
  Or.inr ⟨p, j, hj, rfl⟩

/-- **Adjoining one variable of degree one to a finite variable stage enlarges its degree-one
part only by coefficient multiples of that variable.** This is the odd extension's
`grade_eq_sup_map` at degree one: the degree-one piece of the extension is the degree-one piece
of the stage together with its degree-zero piece multiplied by the new variable, and the
degree-zero piece of a stage consists of coefficients.

As in `inf_finiteVariableStageSubmodule_insert_le`, the next stage is described by a membership
characterisation rather than written as `insert j S`, because the `successor` field supplies its
own decidable equality on the index type. -/
public theorem inf_finiteVariableStageSubmodule_one_insert_le
    (S : Finset (Σ n : ℕ, h.indices n)) (j0 : h.indices 0)
    (hj : (⟨0, j0⟩ : Σ n : ℕ, h.indices n) ∉ S)
    (U : Finset (Σ n : ℕ, h.indices n))
    (hU : ∀ k, k ∈ U ↔ k = ⟨0, j0⟩ ∨ k ∈ S) :
    𝒜 1 ⊓ finiteVariableStageSubmodule γ ι h.generator U ≤
      (𝒜 1 ⊓ finiteVariableStageSubmodule γ ι h.generator S) ⊔
        Submodule.span R {x : A | ∃ p : P, x = ι p * h.generator ⟨0, j0⟩} := by
  rintro x ⟨hx0, hxU⟩
  obtain ⟨aS, -, Sᵢ, gS, cS, δS, -, hoddBr, -⟩ := h.successor S ⟨0, j0⟩ hj
  let instJ : DecidableEq ((n : ℕ) × h.indices n) := Classical.decEq _
  have hUeq : (insert (⟨0, j0⟩ : Σ n : ℕ, h.indices n) S) = U := by
    ext k
    simp [hU k]
  rw [hUeq] at hoddBr
  let instA : Algebra R (finiteVariableStage γ ι h.generator S) := aS
  let instG : GradedAlgebra Sᵢ := gS
  let instC : IsStrictlyGradedComm Sᵢ := cS
  obtain ⟨e, hcoeff, hgen, hgrade, -⟩ := hoddBr odd_one
  obtain ⟨z, hz⟩ := exists_stageRingHom_eq γ ι h.generator U e x hxU
  have hzx : ((e z : finiteVariableStage γ ι h.generator U) : A) = x := hz
  have hz1 : z ∈ OddVariableExtension.grade Sᵢ 1 1 :=
    (hgrade 1 z).mpr (by rw [hzx]; exact hx0)
  rw [OddVariableExtension.grade_eq_sup_map Sᵢ 1 1, ite_eq_left (le_refl 1)] at hz1
  obtain ⟨z1, hz1', z2, hz2', hsum⟩ := Submodule.mem_sup.mp hz1
  obtain ⟨b1, hb1, rfl⟩ := hz1'
  obtain ⟨b0, hb0, rfl⟩ := hz2'
  have hincl1 : ((e (OddVariableExtension.inclusionLinearMap Sᵢ 1 b1) :
      finiteVariableStage γ ι h.generator U) : A) = (b1 : A) := hcoeff b1
  have hb1A : (b1 : A) ∈ 𝒜 1 := by
    have hmem := (hgrade 1 (OddVariableExtension.inclusionLinearMap Sᵢ 1 b1)).mp
      (OddVariableExtension.inclusion_mem_grade Sᵢ 1 1 hb1)
    rwa [hincl1] at hmem
  have hincl0 : ((e (OddVariableExtension.inclusionLinearMap Sᵢ 1 b0) :
      finiteVariableStage γ ι h.generator U) : A) = (b0 : A) := hcoeff b0
  have hb0A : (b0 : A) ∈ 𝒜 0 := by
    have hmem := (hgrade 0 (OddVariableExtension.inclusionLinearMap Sᵢ 1 b0)).mp
      (OddVariableExtension.inclusion_mem_grade Sᵢ 1 0 hb0)
    rwa [hincl0] at hmem
  obtain ⟨p, hp0⟩ := inf_finiteVariableStageSubmodule_le_range h S ⟨hb0A, b0.2⟩
  have hp : ι p = (b0 : A) := hp0
  have hmul : ((e (OddVariableExtension.generatorMulLinearMap Sᵢ 1 b0) :
      finiteVariableStage γ ι h.generator U) : A) = (b0 : A) * h.generator ⟨0, j0⟩ := by
    have hrw : OddVariableExtension.generatorMulLinearMap Sᵢ 1 b0 =
        OddVariableExtension.inclusionLinearMap Sᵢ 1 b0 *
          OddVariableExtension.generator Sᵢ 1 := rfl
    rw [hrw, map_mul, MulMemClass.coe_mul, hincl0, hgen]
  have hxeq : x = (b1 : A) + ι p * h.generator ⟨0, j0⟩ := by
    rw [← hzx, ← hsum, map_add, AddMemClass.coe_add, hincl1, hmul, hp]
  rw [hxeq]
  exact Submodule.add_mem_sup ⟨hb1A, b1.2⟩ (Submodule.subset_span ⟨p, rfl⟩)

/-- **The degree-one part of a finite variable stage whose variables all have degree one is
spanned by the coefficients and the coefficient multiples of those variables.** The induction is
an ordinary induction on the finite set of adjoined variables, as for the degree-zero part. -/
public theorem inf_finiteVariableStageSubmodule_one_le
    (S : Finset (Σ n : ℕ, h.indices n)) (hS : ∀ j ∈ S, j.1 = 0) :
    𝒜 1 ⊓ finiteVariableStageSubmodule γ ι h.generator S ≤
      Submodule.span R (gradeOneGenerators h) := by
  classical
  induction S using Finset.induction with
  | empty =>
      rintro x ⟨-, hx⟩
      obtain ⟨p, hp⟩ := (mem_finiteVariableStage_empty_iff h x).mp hx
      exact hp ▸ Submodule.subset_span (coefficient_mem_gradeOneGenerators h p)
  | insert j T hjT ih =>
      have hj0 : j.1 = 0 := hS j (Finset.mem_insert_self j T)
      have hTS : ∀ k ∈ T, k.1 = 0 := fun k hk => hS k (Finset.mem_insert_of_mem hk)
      obtain ⟨n, jn⟩ := j
      have hn : n = 0 := hj0
      subst hn
      refine le_trans
        (inf_finiteVariableStageSubmodule_one_insert_le h T jn hjT _
          (fun _ => Finset.mem_insert)) (sup_le (ih hTS) ?_)
      rw [Submodule.span_le]
      rintro y ⟨p, rfl⟩
      exact Submodule.subset_span
        (mul_generator_mem_gradeOneGenerators h p ⟨0, jn⟩ rfl)

include h in
/-- **The degree-one part of a graded divided-power polynomial algebra is spanned by the
coefficients and the coefficient multiples of its variables of degree one.**

Only the variables of degree one can contribute, by
`inf_finiteVariableStageSubmodule_le_filter`, and the stages exhaust the algebra. -/
public theorem grade_one_le_span :
    𝒜 1 ≤ Submodule.span R (gradeOneGenerators h) := by
  classical
  rw [← iSup_inf_finiteVariableStageSubmodule γ ι h.generator h.finite_support 1]
  refine iSup_le fun S => le_trans (inf_finiteVariableStageSubmodule_le_filter h 1 S) ?_
  refine inf_finiteVariableStageSubmodule_one_le h _ fun j hj => ?_
  have hj' := (Finset.mem_filter.mp hj).2
  omega

end Stage

end DividedPowers.TateResolution

end
