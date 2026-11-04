module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.GradedPolynomialMap
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.StageDecomposition

/-!
# Elements of a graded divided-power polynomial algebra killed by a scalar

Let `B` be a graded divided-power polynomial algebra over a coefficient algebra `P`, both over a
commutative ring `R'`, and let `f ∈ R'`. If an element of `P` killed by `f` lies in
`ann (f) • P`, then the same holds in `B`: an element of `B` killed by `f` lies in
`ann (f) • B`.

This is the conclusion for which freeness of `B` over `R'` is used in
[Stacks, Tag 09PS](https://stacks.math.columbia.edu/tag/09PS) — through
`DividedPowers.TateResolution.exists_derivation_of_differentialLift` — and it is proved here
without a basis, by induction over the finite-variable stages: a coefficient of an element killed
by `f` is itself killed by `f`, because the coefficients of an element of a successor stage are
unique.

The hypothesis holds for a polynomial algebra, coefficient by coefficient, which is the case the
tag needs.

## Main results

* `DividedPowers.TateResolution.mem_annihilator_smul_top_of_smul_eq_zero_mvPolynomial`
* `DividedPowers.TateResolution.mem_annihilator_smul_top_of_smul_eq_zero_polynomialAlgebra`

## Implementation notes

The submodule `ann (f) • ⊤` of `B` is stable under multiplication by an arbitrary element of
`B`, by `smul_mul_assoc` on its generators; that is what lets a coefficient lying in it be
multiplied back by a power of the new variable.

The induction is over `Finset.induction_on`, whose `insert` uses the `DecidableEq` instance
introduced by `classical`, while the successor clause of `GradedDividedPowerPolynomial` uses
`Classical.decEq`. The decomposition lemmas are therefore stated for an index set described by
its membership, and the step passes the membership description rather than an equation between
the two `insert`s.

## References

* [Stacks Project, Tag 09PS](https://stacks.math.columbia.edu/tag/09PS)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w z

/-- An element killing a generator of a principal ideal lies in that ideal's annihilator. -/
public theorem mem_annihilator_of_mul_eq_zero {R' : Type u} [CommRing R'] {f c : R'}
    (h : f * c = 0) : c ∈ (Ideal.span {f}).annihilator := by
  rw [Submodule.mem_annihilator]
  intro n hn
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hn
  rw [smul_eq_mul, show c * (b * f) = b * (f * c) from by ring, h, mul_zero]

/-- **A polynomial killed by a scalar has all its coefficients killed by that scalar**, hence
lies in the submodule cut out by the annihilator. -/
public theorem mem_annihilator_smul_top_of_smul_eq_zero_mvPolynomial
    {R' : Type u} [CommRing R'] {σ : Type v} (f : R') (p : MvPolynomial σ R')
    (hp : f • p = 0) :
    p ∈ (Ideal.span {f}).annihilator • (⊤ : Submodule R' (MvPolynomial σ R')) := by
  have hcoeff : ∀ m : σ →₀ ℕ, MvPolynomial.coeff m p ∈ (Ideal.span {f}).annihilator := by
    intro m
    refine mem_annihilator_of_mul_eq_zero ?_
    have h := congrArg (MvPolynomial.coeff m) hp
    rwa [MvPolynomial.coeff_smul, MvPolynomial.coeff_zero, smul_eq_mul] at h
  rw [← MvPolynomial.support_sum_monomial_coeff p]
  refine Submodule.sum_mem _ fun m _ => ?_
  have hmon : MvPolynomial.monomial m (MvPolynomial.coeff m p) =
      MvPolynomial.coeff m p • MvPolynomial.monomial m (1 : R') := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hmon]
  exact Submodule.smul_mem_smul (hcoeff m) Submodule.mem_top

section

variable {R' : Type u} {P : Type v} {B : Type w}
  [CommRing R'] [Ring P] [Algebra R' P] [Ring B] [Algebra R' B]
  {ℬ : ℕ → Submodule R' B} [GradedAlgebra ℬ] [IsStrictlyGradedComm ℬ]
  {δ : DividedPowerStructure ℬ} {ι' : P →ₐ[R'] B}

/-- Every finite-variable stage is stable under the scalars. -/
public theorem smul_mem_finiteVariableStage
    {J : Type z} (T : J → B) (S : Finset J) (r : R') {b : B}
    (hb : b ∈ finiteVariableStage δ ι' T S) :
    r • b ∈ finiteVariableStage δ ι' T S := by
  rw [Algebra.smul_def]
  exact Subring.mul_mem _ (algebraMap_mem_finiteVariableStage δ ι' T S r) hb

variable (f : R')

/-- A linear map into `B` sends `ann (f) • ⊤` into `ann (f) • B`. -/
private theorem linearMap_mem_annihilator_smul_top {M : Type*} [AddCommGroup M] [Module R' M]
    (g : M →ₗ[R'] B) {x : M} (hx : x ∈ (Ideal.span {f}).annihilator • (⊤ : Submodule R' M)) :
    g x ∈ (Ideal.span {f}).annihilator • (⊤ : Submodule R' B) := by
  refine Submodule.smul_induction_on (p := fun y => g y ∈ _) hx ?_ ?_
  · intro r hr y _
    rw [map_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · intro y z hy hz
    rw [map_add]
    exact Submodule.add_mem _ hy hz

/-- The submodule cut out by the annihilator of `f` is a two-sided ideal. -/
private theorem mul_mem_annihilator_smul_top {b : B}
    (hb : b ∈ (Ideal.span {f}).annihilator • (⊤ : Submodule R' B)) (c : B) :
    b * c ∈ (Ideal.span {f}).annihilator • (⊤ : Submodule R' B) :=
  linearMap_mem_annihilator_smul_top f (LinearMap.mulRight R' c) hb

/-- **An element of a graded divided-power polynomial algebra killed by `f` lies in
`ann (f) • B`**, as soon as the same holds in the coefficient algebra.

This is the only consequence of freeness of the lifted algebra that
`DividedPowers.TateResolution.exists_derivation_of_differentialLift` uses, and the proof here
needs no basis: the coefficients of an element of a successor finite-variable stage are unique,
so a coefficient of an element killed by `f` is again killed by `f`. -/
public theorem mem_annihilator_smul_top_of_smul_eq_zero_polynomialAlgebra
    (hcoeff : ∀ p : P, f • p = 0 →
      p ∈ (Ideal.span {f}).annihilator • (⊤ : Submodule R' P))
    (hp : GradedDividedPowerPolynomial ℬ δ ι') (b : B) (hb : f • b = 0) :
    b ∈ (Ideal.span {f}).annihilator • (⊤ : Submodule R' B) := by
  classical
  set N := (Ideal.span {f}).annihilator • (⊤ : Submodule R' B) with hN
  have hstage : ∀ S : Finset (Σ n : ℕ, hp.indices n),
      ∀ c ∈ finiteVariableStage δ ι' hp.generator S, f • c = 0 → c ∈ N := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        intro c hc hfc
        obtain ⟨p, rfl⟩ := exists_coefficient_of_mem_stage_empty hp
          (by simp) hc
        have hfp : f • p = 0 := by
          refine hp.coefficient_injective ?_
          rw [map_smul, hfc, map_zero]
        exact linearMap_mem_annihilator_smul_top f ι'.toLinearMap (hcoeff p hfp)
    | insert j S hj ih =>
        intro c hc hfc
        have hU : ∀ k, k ∈ insert j S ↔ k = j ∨ k ∈ S := by intro k; simp
        rcases Nat.even_or_odd (j.1 + 1) with heven | hodd
        · obtain ⟨hexists, hunique⟩ :=
            stage_insert_even_decomposition hp S (insert j S) j hj hU heven
          obtain ⟨s, a, ha, rfl⟩ := hexists c hc
          have hzero : ∀ n ∈ s, f • a n = 0 := by
            refine hunique s (fun n => f • a n)
              (fun n => smul_mem_finiteVariableStage hp.generator S f (ha n)) ?_
            rw [← hfc, Finset.smul_sum]
            exact Finset.sum_congr rfl fun n _ => smul_mul_assoc f (a n) _
          refine Submodule.sum_mem _ fun n hn => ?_
          exact mul_mem_annihilator_smul_top f (ih (a n) (ha n) (hzero n hn)) _
        · obtain ⟨hexists, hunique⟩ :=
            stage_insert_odd_decomposition hp S (insert j S) j hj hU hodd
          obtain ⟨b₀, b₁, h0, h1, rfl⟩ := hexists c hc
          obtain ⟨hz0, hz1⟩ := hunique (f • b₀) (f • b₁)
            (smul_mem_finiteVariableStage hp.generator S f h0)
            (smul_mem_finiteVariableStage hp.generator S f h1)
            (by rw [smul_mul_assoc, ← smul_add]; exact hfc)
          exact Submodule.add_mem _ (ih b₀ h0 hz0)
            (mul_mem_annihilator_smul_top f (ih b₁ h1 hz1) _)
  obtain ⟨S, hS⟩ := hp.finite_support b
  exact hstage S b hS hb

end

end DividedPowers.TateResolution

end
