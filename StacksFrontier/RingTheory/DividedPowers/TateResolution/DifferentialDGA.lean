module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.DifferentialSquare
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Homology
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.PolynomialDifferential

/-!
# The differential graded algebra axioms for a prescribed differential

The differential of a graded divided-power polynomial algebra is determined by arbitrary
degree-lowering values on its variables, and `exists_differential_gradedDividedPowerPolynomial`
produces it together with five of the six properties a Tate resolution asks of it: vanishing in
degree zero, lowering the degree by one, the signed Leibniz rule, and the divided-power Leibniz
rule. The sixth, that the differential squares to zero, is not automatic and is exactly what
fails in Tag 09PS; `sq_eq_zero_of_differential` supplies it from its vanishing on the
coefficients and on the variables.

This file assembles those statements into the two typeclasses a Tate resolution carries, so that
one call produces the differential, the differential-graded-algebra structure and the
compatibility with the divided powers, under the single extra hypothesis that the prescribed
values on the variables are themselves cycles. That hypothesis is where the recursion over
degrees does its work: the value prescribed on a variable of degree `n + 1` is a cycle of degree
`n` whose class one wants to kill.

## Main results

* `DividedPowers.TateResolution.isDifferentialGradedAlgebra_of_differential` — the two
  typeclasses from the six properties of the differential.
* `DividedPowers.TateResolution.exists_dga_differential` — the differential prescribed on the
  variables, a differential graded algebra compatible with the divided powers as soon as the
  prescribed values are cycles.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

section DGA

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [Ring P] [Algebra R P] [Ring A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
  (γ : DividedPowerStructure 𝒜) (ι : P →ₐ[R] A) (D : A →ₗ[R] A)

/-- A degree-lowering map on a graded divided-power polynomial algebra which vanishes on the
coefficients, obeys both Leibniz rules and squares to zero on the variables makes the algebra a
differential graded algebra whose divided powers are compatible with the differential.

The four axioms of `IsDifferentialGradedAlgebra` other than `d_sq_zero`, and the single axiom of
`IsCompatibleWithDifferential`, are the hypotheses verbatim; `d_sq_zero` is
`sq_eq_zero_of_differential`, and vanishing of the square on the coefficients follows from
vanishing of the differential itself. -/
public theorem isDifferentialGradedAlgebra_of_differential
    (h : GradedDividedPowerPolynomial 𝒜 γ ι)
    (hDι : ∀ p : P, D (ι p) = 0)
    (hD0 : ∀ x : A, x ∈ 𝒜 0 → D x = 0)
    (hDgrade : ∀ (n : ℕ) (x : A), x ∈ 𝒜 (n + 1) → D x ∈ 𝒜 n)
    (hDleibniz : ∀ (i j : ℕ) (x y : A), x ∈ 𝒜 i → y ∈ 𝒜 j →
      D (x * y) = D x * y + (-1 : R) ^ i • (x * D y))
    (hDdpow : ∀ (n : ℕ) (x : A), n ≠ 0 → x ∈ positiveEvenPart 𝒜 →
      D (γ.dpow n x) = D x * γ.dpow (n - 1) x)
    (hDgen : ∀ j : Σ n : ℕ, h.indices n, D (D (h.generator j)) = 0) :
    IsDifferentialGradedAlgebra 𝒜 D ∧ IsCompatibleWithDifferential γ D :=
  ⟨{ d_grade_zero := fun hx => hD0 _ hx
     d_mem := fun hx => hDgrade _ _ hx
     d_sq_zero := sq_eq_zero_of_differential 𝒜 γ ι D h hD0 hDgrade hDleibniz hDdpow
       (fun p => by rw [hDι p, map_zero]) hDgen
     leibniz := fun hx hy => hDleibniz _ _ _ _ hx hy },
    ⟨fun hn hx => hDdpow _ _ hn hx⟩⟩

/-- **The differential of a graded divided-power polynomial algebra prescribed on the variables,
packaged with its differential-graded-algebra structure.** The prescribed values are arbitrary
subject to lowering the degree by one, and the resulting differential makes the algebra a
differential graded algebra compatible with its divided powers as soon as those values are
cycles.

This is the input of one rung of the recursion over degrees: the variables of degree `n + 1`
carry prescribed boundaries in degree `n`, and the condition to check is that those boundaries
are cycles, which they are when they are chosen among the cycles of the preceding stage. -/
public theorem exists_dga_differential (h : GradedDividedPowerPolynomial 𝒜 γ ι)
    (t : (Σ n : ℕ, h.indices n) → A) (ht : ∀ j, t j ∈ 𝒜 j.1) :
    ∃ Dt : A →ₗ[R] A,
      (∀ p : P, Dt (ι p) = 0) ∧
      (∀ j : Σ n : ℕ, h.indices n, Dt (h.generator j) = t j) ∧
      ((∀ j : Σ n : ℕ, h.indices n, Dt (t j) = 0) →
        IsDifferentialGradedAlgebra 𝒜 Dt ∧ IsCompatibleWithDifferential γ Dt) := by
  obtain ⟨Dt, h1, h2, h3, h4, h5, h6⟩ :=
    exists_differential_gradedDividedPowerPolynomial 𝒜 γ ι h t ht
  refine ⟨Dt, h1, h2, fun hcyc => ?_⟩
  refine isDifferentialGradedAlgebra_of_differential 𝒜 γ ι Dt h h1 h3 h4 h5 h6 fun j => ?_
  rw [h2 j]
  exact hcyc j

end DGA

end DividedPowers.TateResolution

end
