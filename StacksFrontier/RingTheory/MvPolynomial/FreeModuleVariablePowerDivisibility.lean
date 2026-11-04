module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Kaehler.Polynomial
public import StacksFrontier.RingTheory.MvPolynomial.VariablePowerDivisibility
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Denominators at distinct variables, for a module with a basis

`StacksFrontier.RingTheory.MvPolynomial.VariablePowerDivisibility` proves that in a polynomial ring
`A = R[Tᵤ]` the two subrings `A[1/Tᵢ]` and `A[1/Tⱼ]` of `A[1/(Tᵢ Tⱼ)]` meet in `A` when `i ≠ j`,
in the cleared form

`f · Tⱼ ^ l = g · Tᵢ ^ k  ⟹  ∃ w, f = Tᵢ ^ k · w  ∧  g = Tⱼ ^ l · w`.

This file carries that statement from `A` to any `A`-module `M` with a basis, by applying it to
each coordinate separately: the cofactor is produced coordinatewise and reassembled, which is
possible because the coordinates of the quotient are the monomial quotients of the coordinates of
`f`, hence have no larger support.

The case the de Rham calculations need is `M = ⋀^a Ω[A⁄R]`, which is free on the wedges of the
coordinate differentials. Read in the localizations, the conclusion there says that a
differential `a`-form on `𝐀^{m+n}_S` whose denominator is a power of `yᵢ` and also a power of
`yⱼ`, for `i ≠ j`, has no denominator at all — the form extends across the coordinate subspace
`y₁ = ⋯ = yₙ = 0` as soon as `n ≥ 2`. That is the "small detail omitted" in the proof of the
first assertion of [Stacks, Tag 0FUR], where the composite

`Γ(X, Ω^a_{X/S}) ⟶ Γ(L, Ω^a_{L/S}) ⟶ Γ(L ∖ E, Ω^a_{L/S}) = Γ(X ∖ Z, Ω^a_{X/S})`

is asserted to be an isomorphism "as `Ω^a_{X/S}` is finite free".

## Main results

* `MvPolynomial.exists_eq_smul_X_pow_of_smul_eq_smul`: **two denominators at distinct variables
  are cleared by a single common cofactor, in a module with a basis.**
* `MvPolynomial.exists_eq_smul_X_pow_of_smul_eq_smul_of_free`: the same for a free module, with
  the basis chosen by `Module.Free.chooseBasis`.
* `Stacks.Kaehler.free_exteriorPower_kaehlerDifferential_mvPolynomial`: the `a`-forms of a
  polynomial ring are a free module.
* `Stacks.Kaehler.exists_eq_smul_X_pow_of_smul_eq_smul_forms`: **the statement for differential
  `a`-forms of a polynomial ring** — the shape in which [Stacks, Tag 0FUR] uses it.

## Implementation notes

The cofactor is written down rather than chosen: coordinatewise it is
`MvPolynomial.divMonomial` at the monomial `Tᵢ ^ k`, and `Finsupp.mapRange` applies that to the
whole coordinate vector at once, which is legitimate because monomial division fixes `0`. The
coordinatewise identities are then exactly
`MvPolynomial.exists_eq_mul_X_pow_of_mul_X_pow_eq_mul_X_pow` together with
`MvPolynomial.divMonomial_monomial_mul`, which identifies the written-down quotient with the
cofactor that statement produces. Nothing is chosen with `Exists.choose`, so the cofactor is a
term one can compute with.

Indexing the induced basis of an exterior power needs a linear order on the index type, which
appears in neither statement; one is therefore chosen inside the freeness proof from
`WellOrderingRel`, as Mathlib's `Module.Basis.exteriorPower` lemmas do and as
`StacksFrontier.RingTheory.Kaehler.BlowupChartFormsPoleBound` already does for the same basis.

No hypothesis is placed on `R` and none on the number of variables: the statements are about one
pair `i ≠ j` of variables, and it is the *user* of the statement that has to produce such a pair,
which is where the source's `n ≥ 2` enters.

No `@[stacks]` attribute is attached. This is one input of the proof of the first assertion of
[Stacks, Tag 0FUR] — the omitted detail recalled above — and not one of that tag's assertions.

## References

* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
-/

@[expose] public noncomputable section

open MvPolynomial

universe u v w

namespace MvPolynomial

variable {R : Type u} [CommRing R] {σ : Type v} {M : Type w} [AddCommGroup M]
  [Module (MvPolynomial σ R) M]

/-- **Two denominators at distinct variables are cleared by a single common cofactor, in a module
with a basis.** If `Tⱼ ^ l • u = Tᵢ ^ k • v` in an `R[Tᵤ]`-module `M` with a basis and `i ≠ j`,
there is `w ∈ M` with `u = Tᵢ ^ k • w` and `v = Tⱼ ^ l • w`.

Read in the localizations: the submodules `M[1/Tᵢ]` and `M[1/Tⱼ]` of `M[1/(Tᵢ Tⱼ)]` meet in `M`,
the common element being `w`. The cofactor is produced coordinatewise by
`MvPolynomial.exists_eq_mul_X_pow_of_mul_X_pow_eq_mul_X_pow` and is the monomial quotient of the
coordinates of `u`, so the coordinate vectors are reassembled by `Finsupp.mapRange`. -/
theorem exists_eq_smul_X_pow_of_smul_eq_smul {ι : Type*}
    (B : Module.Basis ι (MvPolynomial σ R) M) {i j : σ} (hij : i ≠ j) {u v : M} {k l : ℕ}
    (h : (X j : MvPolynomial σ R) ^ l • u = (X i : MvPolynomial σ R) ^ k • v) :
    ∃ w : M, u = (X i : MvPolynomial σ R) ^ k • w ∧ v = (X j : MvPolynomial σ R) ^ l • w := by
  classical
  set d : σ →₀ ℕ := Finsupp.single i k with hd
  have key : ∀ p : ι,
      (B.repr u) p = (X i : MvPolynomial σ R) ^ k * ((B.repr u) p).divMonomial d ∧
        (B.repr v) p = (X j : MvPolynomial σ R) ^ l * ((B.repr u) p).divMonomial d := by
    intro p
    have hp : (B.repr u) p * (X j : MvPolynomial σ R) ^ l =
        (B.repr v) p * (X i : MvPolynomial σ R) ^ k := by
      have := congrArg (fun z => (B.repr z) p) h
      simpa [mul_comm] using this
    obtain ⟨w, hu, hv⟩ := exists_eq_mul_X_pow_of_mul_X_pow_eq_mul_X_pow hij hp
    have hdiv : ((B.repr u) p).divMonomial d = w := by
      rw [hu, hd, X_pow_eq_monomial, divMonomial_monomial_mul]
    rw [hdiv]
    exact ⟨hu, hv⟩
  refine ⟨B.repr.symm ((B.repr u).mapRange (fun f => f.divMonomial d) (zero_divMonomial d)),
    B.repr.injective ?_, B.repr.injective ?_⟩ <;>
    rw [map_smul, LinearEquiv.apply_symm_apply]
  · exact Finsupp.ext fun p => (key p).1
  · exact Finsupp.ext fun p => (key p).2

/-- **`MvPolynomial.exists_eq_smul_X_pow_of_smul_eq_smul` for a free module**, with the basis
chosen by `Module.Free.chooseBasis`. -/
theorem exists_eq_smul_X_pow_of_smul_eq_smul_of_free [Module.Free (MvPolynomial σ R) M]
    {i j : σ} (hij : i ≠ j) {u v : M} {k l : ℕ}
    (h : (X j : MvPolynomial σ R) ^ l • u = (X i : MvPolynomial σ R) ^ k • v) :
    ∃ w : M, u = (X i : MvPolynomial σ R) ^ k • w ∧ v = (X j : MvPolynomial σ R) ^ l • w :=
  exists_eq_smul_X_pow_of_smul_eq_smul (Module.Free.chooseBasis (MvPolynomial σ R) M) hij h

end MvPolynomial

namespace Stacks.Kaehler

variable (R : Type u) [CommRing R] (σ : Type v)

/-- **The differential `a`-forms of a polynomial ring are a free module**, on the `a`-fold wedges
of the coordinate differentials: `Ω[R[Tᵤ]⁄R]` is free on `KaehlerDifferential.mvPolynomialBasis`,
and the induced basis of an exterior power is `Module.Basis.exteriorPower`. -/
@[ega "0 20.4.13" "freeness of Ω¹_{B/A}", sga "1 II 4.2" "Affine case"]
theorem free_exteriorPower_kaehlerDifferential_mvPolynomial (a : ℕ) :
    Module.Free (MvPolynomial σ R) (⋀[MvPolynomial σ R]^a Ω[MvPolynomial σ R⁄R]) := by
  let : LinearOrder σ := IsWellOrder.linearOrder WellOrderingRel
  exact Module.Free.of_basis ((KaehlerDifferential.mvPolynomialBasis R σ).exteriorPower a)

/-- **A differential `a`-form of a polynomial ring whose denominator is a power of `Tᵢ` and also
a power of `Tⱼ`, for `i ≠ j`, has no denominator.** Precisely: if `Tⱼ ^ l • ω = Tᵢ ^ k • η` for
two `a`-forms `ω` and `η` and `i ≠ j`, then there is an `a`-form `ζ` with `ω = Tᵢ ^ k • ζ` and
`η = Tⱼ ^ l • ζ`.

This is the "small detail omitted" in the proof of the first assertion of [Stacks, Tag 0FUR]: on
`X = 𝐀^{m+n}_S` with `n ≥ 2` the coordinate subspace `Z` is cut out by at least two of the
coordinates, so an `a`-form given on `X ∖ Z` is given on each `D(yᵢ)` with a denominator a power
of `yᵢ`, and the agreement of two of those forces the denominators away — the `a`-forms being
finite free, which is `Stacks.Kaehler.free_exteriorPower_kaehlerDifferential_mvPolynomial`. -/
theorem exists_eq_smul_X_pow_of_smul_eq_smul_forms (a : ℕ) {i j : σ} (hij : i ≠ j)
    {ω η : ⋀[MvPolynomial σ R]^a Ω[MvPolynomial σ R⁄R]} {k l : ℕ}
    (h : (MvPolynomial.X j : MvPolynomial σ R) ^ l • ω =
      (MvPolynomial.X i : MvPolynomial σ R) ^ k • η) :
    ∃ ζ : ⋀[MvPolynomial σ R]^a Ω[MvPolynomial σ R⁄R],
      ω = (MvPolynomial.X i : MvPolynomial σ R) ^ k • ζ ∧
        η = (MvPolynomial.X j : MvPolynomial σ R) ^ l • ζ :=
  have := free_exteriorPower_kaehlerDifferential_mvPolynomial R σ a
  MvPolynomial.exists_eq_smul_X_pow_of_smul_eq_smul_of_free hij h

end Stacks.Kaehler

end
