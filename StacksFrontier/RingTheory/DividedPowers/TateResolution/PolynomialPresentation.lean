module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.DegreeZero
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.Construction

/-!
# A graded divided-power polynomial algebra on prescribed variables

A `GradedDividedPowerPolynomial` over `ι : P →ₐ[R] A` presents `A` as the directed union of
finite odd-exterior and even-divided-power variable extensions of a coefficient algebra sitting
in degree zero, with variables indexed in each positive degree. This file constructs one on an
arbitrary prescribed family of variables: for `idx : ℕ → Type _`, an algebra with `idx n` new
variables of degree `n + 1` for every `n`.

The construction is the set-indexed extension of
`exists_setVariableDividedPowerExtension` applied to the index type `Σ n, idx n` with
degree function `j ↦ j.1 + 1`, over `P` graded in degree zero. Every field of the structure is
one component of that theorem's conclusion: the
`successor` field in particular is already stated there in exactly the shape the structure
demands, so no stage-by-stage tower is needed to obtain it.

## Main definitions

None.

## Main results

* `DividedPowers.TateResolution.exists_gradedDividedPowerPolynomial_of_indices` — the algebra on
  a prescribed family of variables exists, its `indices` field is the prescribed family on the
  nose, and it has the graded divided-power universal property.

## Implementation notes

The structure's `indices` field lands in the same universe as the algebra, so the prescribed
family is taken in `Type (max u v w)` rather than in `Type w`; the conclusion then pins
`indices` to it by `rfl` instead of up to a `ULift`.

The universal property is restated with the hypotheses of
`exists_setVariableDividedPowerExtension` unchanged, phrased against the degree-zero
grading of the coefficient algebra; `positiveEvenPart_degreeZeroGrade` and
`degreeZeroGrade_eq_bot` reduce both of them to statements about `0` at a use site.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
* [Stacks Project, Tag 0F4I](https://stacks.math.columbia.edu/tag/0F4I)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w z

/-- For any prescribed family `idx` of variable indices, one in each positive degree, there is a
graded divided-power polynomial algebra over `P` whose variables are exactly that family.

This is the colimit algebra underlying a Tate resolution: one application of the set-indexed
divided-power extension of [Stacks, Tag 0F4I], not an iterated tower. -/
public theorem exists_gradedDividedPowerPolynomial_of_indices
    {R : Type u} {P : Type v} [CommRing R] [CommRing P] [Algebra R P]
    (idx : ℕ → Type (max u v w)) :
    ∃ (A : Type (max u v w)) (ringA : Ring A),
      letI : Ring A := ringA
      ∃ (algebraA : Algebra R A),
        letI : Algebra R A := algebraA
        ∃ (Aᵢ : ℕ → Submodule R A) (gradedA : GradedAlgebra Aᵢ),
          letI : GradedAlgebra Aᵢ := gradedA
          ∃ (strictA : IsStrictlyGradedComm Aᵢ),
            letI : IsStrictlyGradedComm Aᵢ := strictA
            ∃ (γ : DividedPowerStructure Aᵢ) (ι : P →ₐ[R] A)
              (h : GradedDividedPowerPolynomial Aᵢ γ ι),
              h.indices = idx ∧
              (∀ {D : Type z} [Ring D] [Algebra R D]
                  (Dᵢ : ℕ → Submodule R D) [GradedAlgebra Dᵢ]
                  [IsStrictlyGradedComm Dᵢ] (ε : DividedPowerStructure Dᵢ)
                  (f : P →ₐ[R] D) (t : (Σ n : ℕ, h.indices n) → D),
                  (∀ (m : ℕ) (p : P), p ∈ degreeZeroGrade R P m → f p ∈ Dᵢ m) →
                  (∀ (n : ℕ) (p : P), p ∈ positiveEvenPart (degreeZeroGrade R P) →
                    ε.dpow n (f p) =
                      f ((degreeZeroDividedPowers R P).dpow n p)) →
                  (∀ j : Σ n : ℕ, h.indices n, t j ∈ Dᵢ (j.1 + 1)) →
                  ∃! g : A →ₐ[R] D,
                    (∀ p : P, g (ι p) = f p) ∧
                    (∀ j : Σ n : ℕ, h.indices n, g (h.generator j) = t j) ∧
                    (∀ (m : ℕ) (x : A), x ∈ Aᵢ m → g x ∈ Dᵢ m) ∧
                    (∀ (n : ℕ) (x : A), x ∈ positiveEvenPart Aᵢ →
                      ε.dpow n (g x) = g (γ.dpow n x))) := by
  obtain ⟨C, ringC, algebraC, Cᵢ, gradedC, strictC, δ, ι, T, hinj, hgrade, hdpow,
      hT, hsupp, hsucc, huniv⟩ :=
    exists_setVariableDividedPowerExtension (degreeZeroGrade R P)
      (degreeZeroDividedPowers R P) (Σ n : ℕ, idx n)
      (fun j => j.1 + 1) (fun j => Nat.zero_lt_succ j.1)
  let _ : Ring C := ringC
  let _ : Algebra R C := algebraC
  let _ : GradedAlgebra Cᵢ := gradedC
  let _ : IsStrictlyGradedComm Cᵢ := strictC
  refine ⟨C, ringC, algebraC, Cᵢ, gradedC, strictC, δ, ι,
    { indices := idx
      generator := T
      generator_mem := hT
      coefficient_mem := fun p => hgrade 0 p Submodule.mem_top
      coefficient_injective := hinj
      finite_support := hsupp
      successor := hsucc }, rfl, ?_⟩
  intro D _ _ Dᵢ _ _ ε f t hf hε ht
  exact huniv Dᵢ ε f t hf hε ht

end DividedPowers.TateResolution

end
