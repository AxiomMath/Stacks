module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.StageDecomposition

/-!
# A derivation of a graded divided-power polynomial algebra is determined by its values on
the variables

Let `A` be a graded divided-power polynomial algebra over a coefficient algebra `P`: a directed
union of finite stages, each obtained from the previous one by adjoining one homogeneous variable
of positive degree. This file shows that an `R`-linear map which satisfies the *untwisted* Leibniz
rule, the divided-power Leibniz rule, and vanishes on the coefficients and on every variable is
zero.

The intended use is squareness of a differential. If `D` lowers degree by one and satisfies the
signed Leibniz rule, then `D ∘ D` satisfies the untwisted Leibniz rule — the two Koszul signs
cancel — and the divided-power Leibniz rule, so `D ∘ D = 0` as soon as `D (D (ι p)) = 0` for every
coefficient and `D (D (T j)) = 0` for every variable. For the tower of
[Stacks, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN) both hold by construction: `D`
restricts to the differential of the previous stage, which is already square-zero, and the
prescribed value of `D` on each new variable is a cycle.

## Main results

* `DividedPowers.TateResolution.eq_zero_of_derivation_vanishing_on_generators` — such a map is
  zero.

## Implementation notes

The proof is one induction over the finite variable stages, using the two coordinate
decompositions `stage_insert_odd_decomposition` and `stage_insert_even_decomposition`: the
elements of a stage are the `b₀ + b₁ T` of an odd successor and the `∑ aₙ γₙ(T)` of an even
successor, with coefficients in the previous stage, and the initial stage is the image of the
coefficient map. No sign bookkeeping appears, because the hypothesis on products is the untwisted
Leibniz rule; it is the *caller* that pays the Koszul signs when it checks that `D ∘ D` satisfies
it.

Only the existence halves of the two decompositions are used. Their uniqueness halves say that
the coordinates are determined, which a statement about a map that already vanishes does not need.

The abstract successor stage `U` of the decomposition lemmas, specified by
`∀ k, k ∈ U ↔ k = j ∨ k ∈ S` rather than written as `insert j S`, is what makes the induction go
through: `Finset.induction_on` produces an `insert` seated at the `DecidableEq` instance of the
caller, while the `successor` field of the presentation produces one seated at
`Classical.decEq`, and the two are equal but not definitionally so.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
* [Stacks Project, Tag 0F4I](https://stacks.math.columbia.edu/tag/0F4I)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [Ring P] [Algebra R P] [Ring A] [Algebra R A]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
  {γ : DividedPowerStructure 𝒜} {ι : P →ₐ[R] A}

/-- A variable of even degree lies in the positive even part, so its divided powers are the
ones of the ambient divided-power structure. -/
public theorem generator_mem_positiveEvenPart
    (hp : GradedDividedPowerPolynomial 𝒜 γ ι) {j : Σ n : ℕ, hp.indices n}
    (heven : Even (j.1 + 1)) : hp.generator j ∈ positiveEvenPart 𝒜 := by
  obtain ⟨k, hk⟩ := heven
  refine mem_positiveEvenPart_of_mem_grade 𝒜 (d := k) (by omega) ?_
  have h : 2 * k = j.1 + 1 := by omega
  rw [h]
  exact hp.generator_mem j

/-- **A derivation of a graded divided-power polynomial algebra vanishing on the coefficients and
on the variables is zero.** The hypothesis on products is the untwisted Leibniz rule, which is
what the square of a differential satisfies. -/
public theorem eq_zero_of_derivation_vanishing_on_generators
    (hp : GradedDividedPowerPolynomial 𝒜 γ ι) (E : A →ₗ[R] A)
    (hEι : ∀ p : P, E (ι p) = 0)
    (hEgen : ∀ j : Σ n : ℕ, hp.indices n, E (hp.generator j) = 0)
    (hEmul : ∀ x y : A, E (x * y) = E x * y + x * E y)
    (hEdpow : ∀ (n : ℕ) (x : A), n ≠ 0 → x ∈ positiveEvenPart 𝒜 →
      E (γ.dpow n x) = E x * γ.dpow (n - 1) x)
    (x : A) : E x = 0 := by
  classical
  have hone : E 1 = 0 := by
    have h := hEmul 1 1
    simp only [one_mul, mul_one] at h
    exact left_eq_add.mp h
  have key : ∀ S : Finset (Σ n : ℕ, hp.indices n),
      ∀ y : A, y ∈ finiteVariableStage γ ι hp.generator S → E y = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        intro y hy
        obtain ⟨p, hp'⟩ :=
          exists_coefficient_of_mem_stage_empty hp (fun k => Finset.notMem_empty k) hy
        rw [hp']
        exact hEι p
    | @insert j S hj ih =>
        intro y hy
        rcases Nat.even_or_odd (j.1 + 1) with heven | hodd
        · obtain ⟨s, a, ha, hyeq⟩ :=
            (stage_insert_even_decomposition hp S (insert j S) j hj
              (fun k => Finset.mem_insert) heven).1 y hy
          have hgen : hp.generator j ∈ positiveEvenPart 𝒜 :=
            generator_mem_positiveEvenPart hp heven
          rw [hyeq, map_sum]
          refine Finset.sum_eq_zero fun n _ => ?_
          rw [hEmul, ih (a n) (ha n), zero_mul, zero_add]
          rcases Nat.eq_zero_or_pos n with rfl | hn
          · rw [γ.dpow_zero hgen, hone, mul_zero]
          · rw [hEdpow n _ (by omega) hgen, hEgen j, zero_mul, mul_zero]
        · obtain ⟨b₀, b₁, h0, h1, hyeq⟩ :=
            (stage_insert_odd_decomposition hp S (insert j S) j hj
              (fun k => Finset.mem_insert) hodd).1 y hy
          rw [hyeq, map_add, ih b₀ h0, hEmul, ih b₁ h1, hEgen j]
          simp
  obtain ⟨S, hS⟩ := hp.finite_support x
  exact key S x hS

end DividedPowers.TateResolution

end
