module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Polynomial
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.Construction
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SquareZeroDerivation
public import StacksCore.Tactic.StacksAttribute

/-! # Stacks 09PS from a square-zero lift

Tag 09PS asserts that a graded divided-power polynomial algebra `A` over `R` with a
divided-power differential acquires a derivation of degree `-2` on `A/IA` after a surjection
`R' → R` with square-zero principal kernel `(f)`, where `I` is the image of the annihilator of
`f`. Its proof has two halves: lift `(A, d)` to a divided-power polynomial algebra `B` over `R'`
with an operator `D` lifting `d` — which is not square-zero — and then read the derivation off
the lift as `κ ∘ D ∘ D`.

This file is the second half, in the form the source's statement retains: given a lift, it
produces the derivation together with *all* of the lift data and compatibilities, so that the
whole of Tag 09PS reduces to the existence of a lift and nothing else.

## Main results

* `DividedPowers.TateResolution.squareZeroExtensionDerivationOfLift` — the derivation of
  Tag 09PS, with the full retained construction, from a divided-power square-zero lift.

## Implementation notes

The derivation and its four properties come from `IsSquareZeroLift`; the two divided-power
compatibilities come from `IsDividedPowerSquareZeroLift`. The two remaining components — that
the lift carries the coefficient map `ι'` to `ι` along `MvPolynomial.map q`, and that it carries
the variables of `B` to the variables of `A` under a reindexing — belong to neither predicate,
since they refer to the polynomial presentations rather than to the lifted differential, and are
taken as hypotheses here.

The carrier `B` is required to live in `Type (max u v w z)`, which is where the source's
statement puts it: it is built from the base rings, the algebra and the degree-zero variable set.
`Equiv` is universe-polymorphic, so the reindexing of the variables between the two presentations
crosses universes without further hypotheses.

## References

* [Stacks Project, Tag 09PS](https://stacks.math.columbia.edu/tag/09PS)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w z

/-- The derivation of Tag 09PS, with the whole construction the source retains, produced from a
divided-power square-zero lift of `(A, 𝒜, γ, d)` across `q`. -/
public noncomputable def squareZeroExtensionDerivationOfLift
    {R' : Type u} {R : Type v} {A : Type w} {σ : Type z}
    [CommRing R'] [CommRing R] [Ring A] [Algebra R A]
    (q : R' →+* R) (f : R')
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜)
    (d : A →ₗ[R] A) [IsDifferentialGradedAlgebra 𝒜 d]
    (ι : MvPolynomial σ R →ₐ[R] A)
    (hpoly : GradedDividedPowerPolynomial 𝒜 γ ι)
    {B : Type (max u v w z)} [Ring B] [Algebra R' B]
    (ℬ : ℕ → Submodule R' B) [GradedAlgebra ℬ] [IsStrictlyGradedComm ℬ]
    (δ : DividedPowerStructure ℬ)
    (ι' : MvPolynomial σ R' →ₐ[R'] B)
    (hpolyB : GradedDividedPowerPolynomial ℬ δ ι')
    (e : ∀ n : ℕ, hpoly.indices n ≃ hpolyB.indices n)
    (π : B →+* A) (D : B →ₗ[R'] B)
    (κ : RingHom.ker π →+ (A ⧸ squareZeroAnnihilatorSMul q f A))
    (hlift : IsDividedPowerSquareZeroLift q f 𝒜 γ d ℬ δ π D κ)
    (hcoeff : ∀ p' : MvPolynomial σ R', π (ι' p') = ι (MvPolynomial.map q p'))
    (hgen : ∀ (n : ℕ) (j : hpoly.indices n),
      π (hpolyB.generator ⟨n, e n j⟩) = hpoly.generator ⟨n, j⟩) :
    { θ : (A ⧸ squareZeroAnnihilatorSMul q f A) →ₗ[R]
        (A ⧸ squareZeroAnnihilatorSMul q f A) //
      (∀ x y : A, ∃ u v : A,
        θ (Submodule.Quotient.mk x) = Submodule.Quotient.mk u ∧
        θ (Submodule.Quotient.mk y) = Submodule.Quotient.mk v ∧
        θ (Submodule.Quotient.mk (x * y)) =
          Submodule.Quotient.mk (u * y + x * v)) ∧
      (∀ (n : ℕ) (x : A), x ∈ 𝒜 (n + 2) →
        ∃ y : A, y ∈ 𝒜 n ∧
          θ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y) ∧
      (∀ (x : A), x ∈ 𝒜 0 → θ (Submodule.Quotient.mk x) = 0) ∧
      (∀ (x : A), x ∈ 𝒜 1 → θ (Submodule.Quotient.mk x) = 0) ∧
      (∃ (C : Type (max u v w z)) (hC : Ring C),
        letI : Ring C := hC
        ∃ (hAlg : Algebra R' C),
          letI : Algebra R' C := hAlg
          ∃ (𝒞 : ℕ → Submodule R' C) (hGr : GradedAlgebra 𝒞),
            letI : GradedAlgebra 𝒞 := hGr
            ∃ (hComm : IsStrictlyGradedComm 𝒞),
              letI : IsStrictlyGradedComm 𝒞 := hComm
              ∃ (ε : DividedPowerStructure 𝒞)
                (ιC : MvPolynomial σ R' →ₐ[R'] C)
                (hpolyC : GradedDividedPowerPolynomial 𝒞 ε ιC)
                (eC : ∀ n : ℕ, hpoly.indices n ≃ hpolyC.indices n)
                (p : C →+* A) (E : C →ₗ[R'] C)
                (k : RingHom.ker p →+ (A ⧸ squareZeroAnnihilatorSMul q f A)),
            Function.Surjective p ∧
            (∀ r' : R', p (algebraMap R' C r') = algebraMap R A (q r')) ∧
            (∀ p' : MvPolynomial σ R',
              p (ιC p') = ι (MvPolynomial.map q p')) ∧
            (∀ (n : ℕ) (j : hpoly.indices n),
              p (hpolyC.generator ⟨n, eC n j⟩) = hpoly.generator ⟨n, j⟩) ∧
            (∀ (n : ℕ) (c : C), c ∈ 𝒞 n → p c ∈ 𝒜 n) ∧
            (∀ (n : ℕ) (c : C), c ∈ positiveEvenPart 𝒞 →
              p (ε.dpow n c) = γ.dpow n (p c)) ∧
            (∀ c : C, p c = 0 ↔ ∃ c' : C, c = algebraMap R' C f * c') ∧
            (∀ (c : C), c ∈ 𝒞 0 → E c = 0) ∧
            (∀ (n : ℕ) (c : C), c ∈ 𝒞 (n + 1) → E c ∈ 𝒞 n) ∧
            (∀ (i j : ℕ) (c c' : C), c ∈ 𝒞 i → c' ∈ 𝒞 j →
              E (c * c') = E c * c' + (-1 : R') ^ i • (c * E c')) ∧
            (∀ (n : ℕ) (c : C), n ≠ 0 → c ∈ positiveEvenPart 𝒞 →
              E (ε.dpow n c) = E c * ε.dpow (n - 1) c) ∧
            (∀ c : C, p (E c) = d (p c)) ∧
            (∀ (c : C) (hc : algebraMap R' C f * c ∈ RingHom.ker p),
              k ⟨algebraMap R' C f * c, hc⟩ =
                Submodule.Quotient.mk (p c)) ∧
            (∀ c : C, ∃ hc : E (E c) ∈ RingHom.ker p,
              θ (Submodule.Quotient.mk (p c)) = k ⟨E (E c), hc⟩)) } :=
  ⟨hlift.toIsSquareZeroLift.derivation,
    hlift.toIsSquareZeroLift.derivation_leibniz,
    hlift.toIsSquareZeroLift.derivation_mem_grade,
    hlift.toIsSquareZeroLift.derivation_eq_zero_of_mem_grade_zero,
    hlift.toIsSquareZeroLift.derivation_eq_zero_of_mem_grade_one,
    B, inferInstance, inferInstance, ℬ, inferInstance, inferInstance, δ, ι', hpolyB, e, π, D, κ,
    hlift.toIsSquareZeroLift.surjective,
    hlift.toIsSquareZeroLift.map_algebraMap,
    hcoeff, hgen,
    hlift.toIsSquareZeroLift.map_mem_grade,
    hlift.map_dpow,
    hlift.toIsSquareZeroLift.mem_ker_iff,
    hlift.toIsSquareZeroLift.D_eq_zero,
    hlift.toIsSquareZeroLift.D_mem_grade,
    hlift.toIsSquareZeroLift.D_leibniz,
    hlift.D_dpow,
    hlift.toIsSquareZeroLift.map_D,
    hlift.toIsSquareZeroLift.kappa_apply,
    fun b => ⟨hlift.toIsSquareZeroLift.map_D_comp_D b,
      hlift.toIsSquareZeroLift.derivation_apply b _⟩⟩

end DividedPowers.TateResolution
