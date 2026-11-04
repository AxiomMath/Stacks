module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Polynomial
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SquareZeroDerivation

/-!
# The derivation of a principal square-zero extension, packaged on its variables

Let `q : R' → R` be a surjection of commutative rings whose kernel is square zero and generated
by one element `f`, and let `A` be a strictly graded-commutative graded `R`-algebra with divided
powers `γ` and a differential `d`, presented as a graded divided-power polynomial algebra over
`MvPolynomial σ R`. Suppose the whole presentation lifts across `q`: there is a graded
divided-power polynomial algebra `B` over `MvPolynomial σ R'` on the same variables, in which an
element killed by `f` lies in `ann (f) • ⊤`, a surjection `π : B → A` with kernel `f B` matching
coefficients, variables, grading and divided powers, and a differential `D` on `B` lifting `d`.

Then `A / IA`, for `I` the image in `R` of the annihilator of `f`, carries a degree-minus-two
derivation `θ`, together with the identification `κ` of `f B` with `A / IA` and all the
compatibilities between `θ`, `κ`, `π` and `D`.

## Main results

* `DividedPowers.TateResolution.nonempty_squareZeroExtensionDerivation_of_differentialLift`.

## Implementation notes

The derivation and the identification come from
`DividedPowers.TateResolution.exists_derivation_of_differentialLift`, which carries out the
descent from a lift presented abstractly — a graded `R'`-algebra with a degree-lowering map
obeying the signed Leibniz rule. What is added here is the bookkeeping that
turns that abstract lift into a lift *of the polynomial presentation*: the data of the lifted
coefficient map, the bijection of variable index types in each degree, and the compatibility of
`π` with the divided powers, none of which the descent argument uses but all of which the
statement of [Stacks, Tag 09PS](https://stacks.math.columbia.edu/tag/09PS) retains.

Squareness of `D` is not assumed and is false in the intended situation: `D ∘ D` is exactly the
derivation being constructed, read through `κ`. Only `d ∘ d = 0` on `A` is used, which is why the
differential graded algebra axioms enter through
`DividedPowers.TateResolution.IsDifferentialGradedAlgebra` on `A` alone.

## References

* [Stacks Project, Tag 09PS](https://stacks.math.columbia.edu/tag/09PS)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w z

/-- **The derivation of a principal square-zero extension, from a lift of the whole polynomial
presentation.** The conclusion is the full data of
[Stacks, Tag 09PS](https://stacks.math.columbia.edu/tag/09PS): a degree-minus-two derivation
`θ` on `A / IA` obeying the Leibniz rule in the quotient, vanishing in degrees zero and one,
together with the lift `(B, D, π, κ)` that produces it. -/
public theorem nonempty_squareZeroExtensionDerivation_of_differentialLift
    {R' : Type u} {R : Type v} {A : Type w} {σ : Type z} {B : Type (max u v w z)}
    [CommRing R'] [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R' B]
    (q : R' →+* R) (hq : Function.Surjective q)
    (f : R') (hker : RingHom.ker q = Ideal.span {f})
    (hsq : (RingHom.ker q) ^ 2 = ⊥)
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜)
    (d : A →ₗ[R] A) [IsDifferentialGradedAlgebra 𝒜 d]
    (ι : MvPolynomial σ R →ₐ[R] A)
    (hpoly : GradedDividedPowerPolynomial 𝒜 γ ι)
    (ℬ : ℕ → Submodule R' B) [GradedAlgebra ℬ] [IsStrictlyGradedComm ℬ]
    (δ : DividedPowerStructure ℬ) (ι' : MvPolynomial σ R' →ₐ[R'] B)
    (hpolyB : GradedDividedPowerPolynomial ℬ δ ι')
    (e : ∀ n : ℕ, hpoly.indices n ≃ hpolyB.indices n)
    (π : B →+* A) (D : B →ₗ[R'] B)
    (hfann : ∀ b : B, f • b = 0 →
      b ∈ (Ideal.span {f}).annihilator • (⊤ : Submodule R' B))
    (hπsurj : Function.Surjective π)
    (hπalg : ∀ r' : R', π (algebraMap R' B r') = algebraMap R A (q r'))
    (hπcoeff : ∀ p' : MvPolynomial σ R', π (ι' p') = ι (MvPolynomial.map q p'))
    (hπgen : ∀ (n : ℕ) (j : hpoly.indices n),
      π (hpolyB.generator ⟨n, e n j⟩) = hpoly.generator ⟨n, j⟩)
    (hπgrade : ∀ (n : ℕ) (b : B), b ∈ ℬ n → π b ∈ 𝒜 n)
    (hπdpow : ∀ (n : ℕ) (b : B), b ∈ positiveEvenPart ℬ →
      π (δ.dpow n b) = γ.dpow n (π b))
    (hπker : ∀ b : B, π b = 0 ↔ ∃ c : B, b = algebraMap R' B f * c)
    (hD0 : ∀ b : B, b ∈ ℬ 0 → D b = 0)
    (hDgrade : ∀ (n : ℕ) (b : B), b ∈ ℬ (n + 1) → D b ∈ ℬ n)
    (hDleibniz : ∀ (i j : ℕ) (b c : B), b ∈ ℬ i → c ∈ ℬ j →
      D (b * c) = D b * c + (-1 : R') ^ i • (b * D c))
    (hDdpow : ∀ (n : ℕ) (b : B), n ≠ 0 → b ∈ positiveEvenPart ℬ →
      D (δ.dpow n b) = D b * δ.dpow (n - 1) b)
    (hDπ : ∀ b : B, π (D b) = d (π b)) :
    let I : Ideal R := Ideal.map q (Ideal.span {f}).annihilator
    let J : Submodule R A := I • ⊤
    Nonempty { θ : (A ⧸ J) →ₗ[R] (A ⧸ J) //
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
            (∀ p' : MvPolynomial σ R',
              π (ι' p') = ι (MvPolynomial.map q p')) ∧
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
              κ ⟨algebraMap R' B f * b, hb⟩ =
                Submodule.Quotient.mk (π b)) ∧
            (∀ b : B, ∃ hb : D (D b) ∈ RingHom.ker π,
              θ (Submodule.Quotient.mk (π b)) = κ ⟨D (D b), hb⟩)) } := by
  intro I J
  obtain ⟨θ, κ, hκ, hθκ, hleib, hdeg, hz0, hz1⟩ :=
    exists_derivation_of_differentialLift q hq f hker hsq 𝒜 d
      (IsDifferentialGradedAlgebra.d_sq_zero 𝒜) ℬ π hπsurj D hfann hπalg hπgrade hπker hD0
      hDgrade hDleibniz hDπ
  exact ⟨θ, hleib, hdeg, hz0, hz1, B, ‹Ring B›, ‹Algebra R' B›, ℬ, inferInstance, inferInstance,
    δ, ι', hpolyB, e, π, D, κ, hπsurj, hπalg, hπcoeff, hπgen, hπgrade, hπdpow, hπker, hD0,
    hDgrade, hDleibniz, hDdpow, hDπ, hκ, hθκ⟩

end DividedPowers.TateResolution

end
