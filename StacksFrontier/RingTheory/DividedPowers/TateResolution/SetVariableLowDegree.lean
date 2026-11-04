module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ChainColimit
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableDerivation

/-! # Low degrees of a set-variable extension, and of the colimit of a chain of them

Adjoining variables of a single degree `d` leaves every degree below `d` untouched: a monomial in
the new variables that involves one of them has degree at least `d`, so a homogeneous element of
degree `m < d` already lies in the coefficient algebra. This file proves that, and propagates it
along an `ω`-chain whose `n`-th step adjoins variables of degree `n + 1`: the degree-`m` piece of
the colimit of such a chain is exactly the image of the degree-`m` piece of its `m`-th stage.

That last statement is what makes Tate's construction converge. The variables adjoined at the
step `n` are indexed by the cycles of degree `n` of the stage `n`, so a cycle of degree `n` in the
colimit has to be recognised as coming from that stage before it can be exhibited as a boundary;
and every later step adjoins variables of degree greater than `n + 1`, so neither the degree-`n`
piece nor the boundary map into it changes again.

## Main results

* `DividedPowers.TateResolution.IsSetVariableExtension.exists_coefficient_of_mem_grade_lt` — a
  homogeneous element of a set-variable divided power extension, of degree below the degree of
  the adjoined variables, is the image of a homogeneous element of the coefficient algebra.
* `DividedPowers.TateResolution.exists_chainMap_eq_of_mem_grade` — the same along a chain of such
  extensions, the `n`-th adjoining variables of degree `n + 1`.
* `DividedPowers.TateResolution.exists_chainColimitInclusion_eq_of_mem_grade` — the degree-`m`
  piece of the colimit of such a chain is the image of the degree-`m` piece of its `m`-th stage.

## Implementation notes

The one-step statement is proved by the subring trick rather than by induction on the finite
variable stages: the elements all of whose homogeneous components below degree `d` lie in the
coefficient algebra form a subring, because a product of two components of degrees summing to
less than `d` has both factors in the coefficient algebra, so it is enough to check the
generators of a finite variable stage. For a divided power `γₙ T` of a variable the check is a
degree count: `T` has a nonzero divided power only when its degree `d` is positive and even, and
then `γₙ T` has degree `n * d ≥ d` for `n ≥ 1`, while `γ₀ T` is `1`.

## References

* [Stacks Project, Tag 0F4I](https://stacks.math.columbia.edu/tag/0F4I)
* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w z

section OneStep

variable {R : Type u} {A : Type v} {C : Type z} {J : Type w}
  [CommRing R] [Ring A] [Algebra R A] [Ring C] [Algebra R C]
  (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
  (γ : DividedPowerStructure Aᵢ)
  (Cᵢ : ℕ → Submodule R C) [GradedAlgebra Cᵢ] [IsStrictlyGradedComm Cᵢ]
  (δ : DividedPowerStructure Cᵢ)
  (ι : A →ₐ[R] C) (T : J → C) (d : ℕ) (hd : 0 < d)

/-- Every homogeneous component below degree `d` of a divided power of an adjoined variable lies
in the coefficient algebra. A variable has a nonzero positive divided power only when its degree
`d` is positive and even, and then the `n`-th divided power is homogeneous of degree `n * d`,
which is at least `d`; the zeroth divided power is `1` or `0`. -/
private theorem gradedPart_dpow_generator_mem_range
    (hone : ∀ m, gradedPart Cᵢ (1 : C) m ∈ ι.range)
    (hC : IsSetVariableExtension Aᵢ γ Cᵢ δ ι T d hd) (j : J) (n m : ℕ) (hm : m < d) :
    gradedPart Cᵢ (δ.dpow n (T j)) m ∈ ι.range := by
  have hzero : ∀ y : C, y = 0 → gradedPart Cᵢ y m ∈ ι.range := by
    intro y hy
    rw [hy, gradedPart_zero]
    exact ι.range.zero_mem
  by_cases hpos : T j ∈ positiveEvenPart Cᵢ
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [δ.dpow_zero hpos]
      exact hone m
    · rcases positiveEven_homogeneous_eq_zero_or_grade Cᵢ (hC.generator_mem j) hpos with
        hz | ⟨e, he⟩
      · exact hzero _ (by rw [hz, δ.dpow_zero_eq_zero (by omega : n ≠ 0)])
      · have hdeg : δ.dpow n (T j) ∈ Cᵢ (2 * n * (e + 1)) :=
          δ.dpow_mem_grade (by omega : n ≠ 0) hpos (he ▸ hC.generator_mem j)
        have hge : d ≤ 2 * n * (e + 1) := by
          calc d = 2 * 1 * (e + 1) := by omega
            _ ≤ 2 * n * (e + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hn)
        rw [gradedPart_of_mem_ne Cᵢ hdeg (by omega : 2 * n * (e + 1) ≠ m)]
        exact ι.range.zero_mem
  · exact hzero _ (δ.dpow_null hpos)

/-- **Degrees below the degree of the adjoined variables are untouched.** A homogeneous element
of degree `m < d` of a set-variable divided power extension by variables of degree `d` is the
image of a homogeneous element of degree `m` of the coefficient algebra. -/
public theorem IsSetVariableExtension.exists_coefficient_of_mem_grade_lt
    (hC : IsSetVariableExtension Aᵢ γ Cᵢ δ ι T d hd) {m : ℕ} (hm : m < d) {x : C}
    (hx : x ∈ Cᵢ m) : ∃ a : A, a ∈ Aᵢ m ∧ ι a = x := by
  classical
  have hone : ∀ m, gradedPart Cᵢ (1 : C) m ∈ ι.range := fun m => by
    rcases eq_or_ne m 0 with hm0 | hm0
    · subst hm0
      rw [gradedPart_of_mem_same Cᵢ (SetLike.one_mem_graded Cᵢ)]
      exact ι.range.one_mem
    · rw [gradedPart_of_mem_ne Cᵢ (SetLike.one_mem_graded Cᵢ) (Ne.symm hm0)]
      exact ι.range.zero_mem
  -- The elements all of whose homogeneous components below degree `d` are coefficients.
  let W : Subring C :=
    { carrier := {y : C | ∀ k : ℕ, k < d → gradedPart Cᵢ y k ∈ ι.range}
      zero_mem' := fun k _ => by rw [gradedPart_zero]; exact ι.range.zero_mem
      one_mem' := fun k _ => hone k
      add_mem' := fun {y z} hy hz k hk => by
        rw [gradedPart_add]
        exact ι.range.add_mem (hy k hk) (hz k hk)
      neg_mem' := fun {y} hy k hk => by
        rw [gradedPart_neg]
        exact ι.range.neg_mem (hy k hk)
      mul_mem' := fun {y z} hy hz k hk => by
        obtain ⟨s, hs⟩ := exists_gradedPart_decomposition Cᵢ y
        obtain ⟨t, ht⟩ := exists_gradedPart_decomposition Cᵢ z
        rw [hs, ht, gradedPart_mul_sum]
        refine Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun l _ => ?_
        rcases eq_or_ne (i + l) k with hik | hik
        · rw [gradedPart_mul_homogeneous Cᵢ (gradedPart_mem Cᵢ y i)
            (gradedPart_mem Cᵢ z l) hik]
          exact ι.range.mul_mem (hy i (by omega)) (hz l (by omega))
        · rw [gradedPart_mul_homogeneous_of_ne Cᵢ (gradedPart_mem Cᵢ y i)
            (gradedPart_mem Cᵢ z l) hik]
          exact ι.range.zero_mem }
  -- The generators of a finite variable stage lie in `W`.
  have hstage : ∀ S : Finset J, finiteVariableStage δ ι T S ≤ W := by
    intro S
    refine Subring.closure_le.2 ?_
    rintro y (⟨a, rfl⟩ | ⟨i, -, rfl | ⟨n, rfl⟩⟩) k hk
    · rw [gradedPart_algHom Aᵢ Cᵢ ι hC.coefficient_grade a k]
      exact ι.mem_range_self _
    · rw [gradedPart_of_mem_ne Cᵢ (hC.generator_mem i) (by omega : d ≠ k)]
      exact ι.range.zero_mem
    · exact gradedPart_dpow_generator_mem_range Aᵢ γ Cᵢ δ ι T d hd hone hC i n k hk
  obtain ⟨S, hS⟩ := hC.finite_support x
  have hmem := hstage S hS m hm
  rw [gradedPart_of_mem_same Cᵢ hx] at hmem
  obtain ⟨a, ha⟩ := (AlgHom.mem_range ι).1 hmem
  exact ⟨a, mem_grade_of_map_mem_grade Aᵢ Cᵢ ι hC.coefficient_grade hC.coefficient_injective m
    (ha ▸ hx), ha⟩

end OneStep

section Chain

attribute [local instance] GradedDPAlgebra.ring GradedDPAlgebra.algebra
  GradedDPAlgebra.graded GradedDPAlgebra.strict

attribute [local instance] gradedLimitGradedAlgebra gradedLimitStrictlyGradedComm

variable {R : Type u} [CommRing R] (B : ℕ → GradedDPAlgebra.{u, v} R)
  (step : ∀ n : ℕ, GradedDPHom (B n) (B (n + 1)))
  {Jdx : ℕ → Type w} (V : (n : ℕ) → Jdx n → (B (n + 1)).carrier)
  (hV : ∀ n : ℕ, IsSetVariableExtension (B n).grade (B n).gamma (B (n + 1)).grade
    (B (n + 1)).gamma (step n).hom (V n) (n + 1) n.succ_pos)

include hV

/-- One step of a chain adjoining variables of degree `n + 1` leaves every degree at most `n`
untouched. -/
public theorem exists_step_eq_of_mem_grade {n m : ℕ} (hm : m ≤ n) {x : (B (n + 1)).carrier}
    (hx : x ∈ (B (n + 1)).grade m) :
    ∃ y : (B n).carrier, y ∈ (B n).grade m ∧ (step n).hom y = x :=
  (hV n).exists_coefficient_of_mem_grade_lt (B n).grade (B n).gamma (B (n + 1)).grade
    (B (n + 1)).gamma (step n).hom (V n) (n + 1) n.succ_pos (by omega) hx

/-- **A homogeneous element of a later stage of the chain comes from the stage of its own
degree.** The step at `k` adjoins variables of degree `k + 1`, so every step from the `m`-th
stage onwards is onto in degree `m`. -/
public theorem exists_chainMap_eq_of_mem_grade {m k : ℕ} (h : m ≤ k) {x : (B k).carrier}
    (hx : x ∈ (B k).grade m) :
    ∃ y : (B m).carrier, y ∈ (B m).grade m ∧ (chainMap B step h).hom y = x := by
  induction h with
  | refl => exact ⟨x, hx, chainMap_hom_self B step m x⟩
  | @step l hl ih =>
      obtain ⟨z, hz, hzx⟩ := exists_step_eq_of_mem_grade B step V hV hl hx
      obtain ⟨y, hy, hyz⟩ := ih hz
      refine ⟨y, hy, ?_⟩
      rw [chainMap_succ B step hl, ← hzx, ← hyz]
      rfl

/-- **The degree-`m` piece of the colimit is the image of the degree-`m` piece of the `m`-th
stage.** This is the statement that makes Tate's construction converge: the cycles of degree `m`
of the colimit are exactly the images of the cycles of degree `m` of the stage at which the
variables killing them are adjoined. -/
public theorem exists_chainColimitInclusion_eq_of_mem_grade (m : ℕ)
    {x : (chainColimit B step).carrier} (hx : x ∈ (chainColimit B step).grade m) :
    ∃ y : (B m).carrier, y ∈ (B m).grade m ∧ (chainColimitInclusion B step m).hom y = x := by
  obtain ⟨n, w, hw, hwx⟩ := (chainColimit_mem_grade_iff B step m x).1 hx
  have hnk : n ≤ max n m := le_max_left n m
  have hmk : m ≤ max n m := le_max_right n m
  obtain ⟨y, hy, hyw⟩ := exists_chainMap_eq_of_mem_grade B step V hV hmk
    ((chainMap B step hnk).map_grade m w hw)
  refine ⟨y, hy, ?_⟩
  rw [← chainColimitInclusion_chainMap B step hmk y, hyw,
    chainColimitInclusion_chainMap B step hnk w, hwx]

end Chain

end DividedPowers.TateResolution

end
