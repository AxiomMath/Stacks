module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.DifferentialLift
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ExteriorKoszulCompatibility
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.StageDerivation

/-!
# Squareness of a differential on a graded divided-power polynomial algebra

Let `A` be a graded divided-power polynomial algebra over a coefficient algebra `P` sitting in
degree zero, and let `D` lower degree by one and satisfy the signed Leibniz rule and the
divided-power Leibniz rule. This file shows that `D ∘ D = 0` as soon as `D (D (ι p)) = 0` for
every coefficient and `D (D (T j)) = 0` for every variable.

## Main results

* `DividedPowers.TateResolution.sq_eq_zero_of_differential` — `D ∘ D = 0` from its vanishing on
  the coefficients and the variables.
* `DividedPowers.TateResolution.degreeLowering_mem_oddPart` — a map lowering every degree by one
  carries the positive even part into the odd part.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
* [Stacks Project, Tag 09PM](https://stacks.math.columbia.edu/tag/09PM)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

section OddPart

variable {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]

omit [IsStrictlyGradedComm 𝒜] in
/-- The grading sign for `d = 1` is negation on the odd part. -/
public theorem signRingEquiv_one_of_mem_oddPart {u : A} (hu : u ∈ oddPart 𝒜) :
    signRingEquiv 𝒜 1 u = -u := by
  induction hu using Submodule.iSup_induction' with
  | mem e u hu =>
      rw [signRingEquiv_of_mem 𝒜 1 (2 * e + 1) hu, one_mul,
        Odd.neg_one_pow (⟨e, rfl⟩ : Odd (2 * e + 1)), neg_one_smul]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, ha, hb, neg_add]

end OddPart

section Square

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [Ring P] [Algebra R P] [Ring A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
  (γ : DividedPowerStructure 𝒜) (ι : P →ₐ[R] A) (D : A →ₗ[R] A)

omit [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] in
/-- A degree-lowering map sends the positive even part into the odd part. -/
public theorem degreeLowering_mem_oddPart
    (hDgrade : ∀ (n : ℕ) (a : A), a ∈ 𝒜 (n + 1) → D a ∈ 𝒜 n)
    {x : A} (hx : x ∈ positiveEvenPart 𝒜) : D x ∈ oddPart 𝒜 := by
  induction hx using Submodule.iSup_induction' with
  | mem k x hx =>
      refine Submodule.mem_iSup_of_mem k ?_
      have h : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
      rw [h] at hx
      exact hDgrade (2 * k + 1) x hx
  | zero => rw [map_zero]; exact (oddPart 𝒜).zero_mem
  | add a b _ _ ha hb => rw [map_add]; exact (oddPart 𝒜).add_mem ha hb

omit [IsStrictlyGradedComm 𝒜] in
/-- A degree-lowering map anticommutes with the grading sign for `d = 1`. -/
public theorem differential_signRingEquiv_add_eq_zero
    (hD0 : ∀ a : A, a ∈ 𝒜 0 → D a = 0)
    (hDgrade : ∀ (n : ℕ) (a : A), a ∈ 𝒜 (n + 1) → D a ∈ 𝒜 n) (x : A) :
    D (signRingEquiv 𝒜 1 x) + signRingEquiv 𝒜 1 (D x) = 0 := by
  classical
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous m x =>
      match m with
      | 0 =>
          have h1 : D (x : A) = 0 := hD0 _ x.property
          have h2 : D (signRingEquiv 𝒜 1 (x : A)) = 0 := by
            rw [signRingEquiv_of_mem 𝒜 1 0 x.property]
            exact hD0 _ (Submodule.smul_mem _ _ x.property)
          rw [h1, h2, map_zero, add_zero]
      | m + 1 =>
          rw [signRingEquiv_of_mem 𝒜 1 (m + 1) x.property, map_smul,
            signRingEquiv_of_mem 𝒜 1 m (hDgrade m _ x.property), one_mul, one_mul, pow_succ,
            mul_neg_one, neg_smul, neg_add_cancel]
  | add x y hx hy =>
      simp only [map_add]
      rw [add_add_add_comm, hx, hy, add_zero]

/-- **The square of a differential vanishes once it vanishes on the coefficients and on the
variables.** -/
public theorem sq_eq_zero_of_differential
    (hp : GradedDividedPowerPolynomial 𝒜 γ ι)
    (hD0 : ∀ a : A, a ∈ 𝒜 0 → D a = 0)
    (hDgrade : ∀ (n : ℕ) (a : A), a ∈ 𝒜 (n + 1) → D a ∈ 𝒜 n)
    (hDleibniz : ∀ (i j : ℕ) (x y : A), x ∈ 𝒜 i → y ∈ 𝒜 j →
      D (x * y) = D x * y + (-1 : R) ^ i • (x * D y))
    (hDdpow : ∀ (n : ℕ) (x : A), n ≠ 0 → x ∈ positiveEvenPart 𝒜 →
      D (γ.dpow n x) = D x * γ.dpow (n - 1) x)
    (hDι : ∀ p : P, D (D (ι p)) = 0)
    (hDgen : ∀ j : Σ n : ℕ, hp.indices n, D (D (hp.generator j)) = 0)
    (x : A) : D (D x) = 0 := by
  have hanti := differential_signRingEquiv_add_eq_zero 𝒜 D hD0 hDgrade
  have hone : D 1 = 0 := hD0 1 (SetLike.one_mem_graded 𝒜)
  have hmul : ∀ y z : A, D (D (y * z)) = D (D y) * z + y * D (D z) := by
    intro y z
    have h0 : D (signRingEquiv 𝒜 1 y) * D z + signRingEquiv 𝒜 1 (D y) * D z = 0 := by
      rw [← add_mul, hanti y, zero_mul]
    rw [map_mul_of_leibniz 𝒜 D hDleibniz y z, map_add,
      map_mul_of_leibniz 𝒜 D hDleibniz (signRingEquiv 𝒜 1 y) (D z),
      map_mul_of_leibniz 𝒜 D hDleibniz (D y) z, signRingEquiv_signRingEquiv 𝒜 1 y,
      show y * D (D z) + D (signRingEquiv 𝒜 1 y) * D z +
          (signRingEquiv 𝒜 1 (D y) * D z + D (D y) * z) =
          (D (signRingEquiv 𝒜 1 y) * D z + signRingEquiv 𝒜 1 (D y) * D z) +
          (D (D y) * z + y * D (D z)) from by abel, h0, zero_add]
  have hdpow : ∀ (n : ℕ) (y : A), n ≠ 0 → y ∈ positiveEvenPart 𝒜 →
      D (D (γ.dpow n y)) = D (D y) * γ.dpow (n - 1) y := by
    intro n y hn hy
    have hDy : D y ∈ oddPart 𝒜 := degreeLowering_mem_oddPart 𝒜 D hDgrade hy
    have hzero : signRingEquiv 𝒜 1 (D y) * D (γ.dpow (n - 1) y) = 0 := by
      rcases Nat.eq_zero_or_pos (n - 1) with h1 | h1
      · rw [h1, γ.dpow_zero hy, hone, mul_zero]
      · rw [hDdpow (n - 1) y (by omega) hy, signRingEquiv_one_of_mem_oddPart 𝒜 hDy, neg_mul,
          ← mul_assoc, mul_self_eq_zero_of_mem_oddPart 𝒜 hDy, zero_mul, neg_zero]
    rw [hDdpow n y hn hy, map_mul_of_leibniz 𝒜 D hDleibniz (D y) (γ.dpow (n - 1) y), hzero,
      zero_add]
  exact eq_zero_of_derivation_vanishing_on_generators hp (D.comp D) hDι hDgen hmul hdpow x

end Square

end DividedPowers.TateResolution

end
