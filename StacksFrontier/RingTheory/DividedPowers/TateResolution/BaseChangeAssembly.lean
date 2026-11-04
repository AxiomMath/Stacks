module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.BaseChangePolynomial
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.CoefficientRestriction
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.DerivationAssembly
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.DifferentialLift
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.StageKernel

/-!
# The derivation of a principal square-zero extension

Let `q : R' → R` be a surjection of commutative rings whose kernel is square zero and generated
by one element `f`, and let `A` be a strictly graded-commutative graded `R`-algebra with divided
powers `γ` and a compatible differential `d`, presented as a graded divided-power polynomial
algebra over `MvPolynomial σ R`. The construction of
[Stacks, Tag 09PS](https://stacks.math.columbia.edu/tag/09PS) assembles from this a
degree-minus-two derivation on `A / IA`.

This file carries out that assembly. Its five steps are the lifted algebra `B` over
`MvPolynomial σ R'` on the same variables, the reduction `π : B → A` with its six
compatibilities, the two facts about `(B, π)` that make the descent work — an element of `B`
killed by `f` lies in `ann (f) • B`, and the kernel of `π` is `f B` — the lifted differential `D`
with `π ∘ D = d ∘ π`, and the descent itself.

## Main results

* `DividedPowers.TateResolution.nonempty_squareZeroExtensionDerivation`.

## Implementation notes

The source of [Stacks, Tag 09PS](https://stacks.math.columbia.edu/tag/09PS) asks for `B` to be
free over `R'`; freeness is used only to put an element killed by `f` into `ann (f) • B`, and
that consequence is available directly from the uniqueness of the coordinates on a
finite-variable stage, so no basis of `B` is constructed anywhere.

The universe bookkeeping is the one recorded in
`DividedPowers.TateResolution.exists_gradedDividedPowerPolynomial_mvPolynomial`: the tag demands
`B : Type (max u v w z)` for `R' : Type u`, `R : Type v`, `A : Type w` and `σ : Type z`, and that
is obtained by asking for variables indexed by `ULift.{v, w} (hpoly.indices n)` rather than by
`hpoly.indices n`, whose index type would give `Type (max u z w)`.

## References

* [Stacks Project, Tag 09PS](https://stacks.math.columbia.edu/tag/09PS)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w z


/-- **The derivation of a principal square-zero extension exists.** This is the whole
construction of [Stacks, Tag 09PS](https://stacks.math.columbia.edu/tag/09PS): the lift of the
presentation across `q`, the lift of the differential, and the descent of its square. -/
public theorem nonempty_squareZeroExtensionDerivation
    {R' : Type u} {R : Type v} {A : Type w} {σ : Type z}
    [CommRing R'] [CommRing R] [Ring A] [Algebra R A]
    (q : R' →+* R) (hq : Function.Surjective q)
    (f : R') (hker : RingHom.ker q = Ideal.span {f})
    (hsq : (RingHom.ker q) ^ 2 = ⊥)
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜)
    (d : A →ₗ[R] A) [IsDifferentialGradedAlgebra 𝒜 d] [IsCompatibleWithDifferential γ d]
    (ι : MvPolynomial σ R →ₐ[R] A)
    (hpoly : GradedDividedPowerPolynomial 𝒜 γ ι) :
    let I : Ideal R := Ideal.map q (Ideal.span {f}).annihilator
    let J : Submodule R A := I • ⊤
    Nonempty { θ : (A ⧸ J) →ₗ[R] (A ⧸ J) //
      (∀ x y : A, ∃ u v : A,
        θ (Submodule.Quotient.mk x) = Submodule.Quotient.mk u ∧
        θ (Submodule.Quotient.mk y) = Submodule.Quotient.mk v ∧
        θ (Submodule.Quotient.mk (x * y)) = Submodule.Quotient.mk (u * y + x * v)) ∧
      (∀ (n : ℕ) (x : A), x ∈ 𝒜 (n + 2) →
        ∃ y : A, y ∈ 𝒜 n ∧ θ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y) ∧
      (∀ (x : A), x ∈ 𝒜 0 → θ (Submodule.Quotient.mk x) = 0) ∧
      (∀ (x : A), x ∈ 𝒜 1 → θ (Submodule.Quotient.mk x) = 0) ∧
      (∃ (B : Type (max u v w z)) (hB : Ring B),
        letI : Ring B := hB
        ∃ (hAlg : Algebra R' B),
          letI : Algebra R' B := hAlg
          ∃ (ℬ : ℕ → Submodule R' B) (hGr : GradedAlgebra ℬ),
            letI : GradedAlgebra ℬ := hGr
            ∃ (hComm : IsStrictlyGradedComm ℬ),
              letI : IsStrictlyGradedComm ℬ := hComm
              ∃ (δ : DividedPowerStructure ℬ)
                (ι' : MvPolynomial σ R' →ₐ[R'] B)
                (hpolyB : GradedDividedPowerPolynomial ℬ δ ι')
                (e : ∀ n : ℕ, hpoly.indices n ≃ hpolyB.indices n)
                (π : B →+* A) (D : B →ₗ[R'] B)
                (κ : RingHom.ker π →+ (A ⧸ J)),
            Function.Surjective π ∧
            (∀ r' : R', π (algebraMap R' B r') = algebraMap R A (q r')) ∧
            (∀ p' : MvPolynomial σ R', π (ι' p') = ι (MvPolynomial.map q p')) ∧
            (∀ (n : ℕ) (j : hpoly.indices n),
              π (hpolyB.generator ⟨n, e n j⟩) = hpoly.generator ⟨n, j⟩) ∧
            (∀ (n : ℕ) (b : B), b ∈ ℬ n → π b ∈ 𝒜 n) ∧
            (∀ (n : ℕ) (b : B), b ∈ positiveEvenPart ℬ →
              π (δ.dpow n b) = γ.dpow n (π b)) ∧
            (∀ b : B, π b = 0 ↔ ∃ c : B, b = algebraMap R' B f * c) ∧
            (∀ (b : B), b ∈ ℬ 0 → D b = 0) ∧
            (∀ (n : ℕ) (b : B), b ∈ ℬ (n + 1) → D b ∈ ℬ n) ∧
            (∀ (i j : ℕ) (b c : B), b ∈ ℬ i → c ∈ ℬ j →
              D (b * c) = D b * c + (-1 : R') ^ i • (b * D c)) ∧
            (∀ (n : ℕ) (b : B), n ≠ 0 → b ∈ positiveEvenPart ℬ →
              D (δ.dpow n b) = D b * δ.dpow (n - 1) b) ∧
            (∀ b : B, π (D b) = d (π b)) ∧
            (∀ (b : B) (hb : algebraMap R' B f * b ∈ RingHom.ker π),
              κ ⟨algebraMap R' B f * b, hb⟩ = Submodule.Quotient.mk (π b)) ∧
            (∀ b : B, ∃ hb : D (D b) ∈ RingHom.ker π,
              θ (Submodule.Quotient.mk (π b)) = κ ⟨D (D b), hb⟩)) } := by
  intro I J
  obtain ⟨B, ringB, algB, ℬ, grB, scB, δ, ι', hpolyB, hind⟩ :=
    exists_gradedDividedPowerPolynomial_mvPolynomial R' σ
      (fun n => ULift.{v, w} (hpoly.indices n))
  let _ : Ring B := ringB
  let _ : Algebra R' B := algB
  let _ : GradedAlgebra ℬ := grB
  let _ : IsStrictlyGradedComm ℬ := scB
  have e : ∀ n : ℕ, hpoly.indices n ≃ hpolyB.indices n := fun n =>
    (Equiv.ulift.{v, w}).symm.trans ((hind n).some).symm
  obtain ⟨π, hπsurj, hπalg, hπcoeff, hπgen, hπgrade, hπdpow⟩ :=
    exists_gradedDividedPowerPolynomial_map_of_ringHom q hq 𝒜 γ ι hpoly ℬ δ ι' hpolyB e
  have hfann : ∀ b : B, f • b = 0 →
      b ∈ (Ideal.span {f}).annihilator • (⊤ : Submodule R' B) :=
    mem_annihilator_smul_top_of_smul_eq_zero_polynomialAlgebra f
      (mem_annihilator_smul_top_of_smul_eq_zero_mvPolynomial f) hpolyB
  have hπker : ∀ b : B, π b = 0 ↔ ∃ c : B, b = algebraMap R' B f * c :=
    mem_ker_iff_mul_of_gradedDividedPowerPolynomial_map q f hker 𝒜 γ ι hpoly ℬ δ ι' hpolyB e π
      hπcoeff hπgen hπdpow
  obtain ⟨D, hD0, hDgrade, hDleibniz, hDdpow, hDπ⟩ :=
    exists_differential_lift_gradedDividedPowerPolynomial q 𝒜 γ d ι hpoly ℬ δ ι' hpolyB e π
      hπsurj hπalg hπcoeff hπgen hπgrade hπdpow
  exact nonempty_squareZeroExtensionDerivation_of_differentialLift q hq f hker hsq 𝒜 γ d ι
    hpoly ℬ δ ι' hpolyB e π D hfann hπsurj hπalg hπcoeff hπgen hπgrade hπdpow hπker hD0
    hDgrade hDleibniz hDdpow hDπ

end DividedPowers.TateResolution

end
