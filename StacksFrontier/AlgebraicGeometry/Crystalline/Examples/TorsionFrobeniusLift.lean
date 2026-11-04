module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedEnvelopeFactorization
public import StacksFrontier.AlgebraicGeometry.Crystalline.ExampleDividedPowerComputations
public import StacksFrontier.AlgebraicGeometry.Crystalline.Examples.TorsionCompletedDeRham
public import StacksFrontier.RingTheory.DividedPowers.PadicIntegersAtPrime

/-!
# The Frobenius lift of the example of [Stacks, Tag 07LJ], and its non-injectivity on `H⁰`

Keep the situation of
`StacksFrontier.AlgebraicGeometry.Crystalline.Examples.TorsionDegreeZero`: the base
`(A, I, γ) = (ℤ_[p], (p), γ)`, the presentation `C = P/J = ℤ_[p][x, y]/(p, x², xy, y²)`, the
`p`-adically completed divided power envelope `D = D_{P, γ}(J)^∧` with its divided powers `γ̄`,
and the element `τ = γ̄_p(x²) γ̄_p(y²) − γ̄_p(xy)² ∈ D`.

The last sentence of [Stacks, Tag 07LJ] reads `F^*(τ) = σ(τ)` for "the map `σ : D → D` induced by
any lift of Frobenius on `P`", and then chooses the lift `x ↦ x^p`, `y ↦ y^p`.  This module
**constructs that `σ`** and draws the example's second numbered conclusion for the complex
`D → Ω¹_D → ⋯` of [Stacks, Proposition 60.21.3, Tag 07LG]: `σ` is not injective on the kernel of
the degree zero differential, because it kills the nonzero element `τ` of that kernel.

## How `σ` is obtained

`σ` comes from the universal property of `D` recorded as
`Crystalline.existsUnique_dPMorphism_from_envelopeCompletion`, which is the universal properties
of a polynomial algebra, of the divided power envelope of [Stacks, Tag 07H8] and of the `p`-adic
completion of a divided power ring chained together: a divided power morphism `D → T` over `A`
into a `p`-adically complete divided power ring is exactly a choice of images of the coordinates
`x`, `y` whose induced polynomial map carries `J` into the divided power ideal of `T`.  Here
`T = D` and the images are `x^p`, `y^p`, and the compatibility is the computation

`p ↦ p`, `x² ↦ (x²)^p`, `xy ↦ (xy)^p`, `y² ↦ (y²)^p`,

each of which lands in `J̄` because `J̄` is an ideal containing `p`, `x²`, `xy` and `y²`.  This is
what removes the proviso attached to
`Crystalline.TorsionExample.map_tau_eq_zero` of
`StacksFrontier.AlgebraicGeometry.Crystalline.ExampleDividedPowerComputations`, whose hypothesis was
the existence of such a `σ`.

The universal property asks for `ℤ_(p)`-algebra structures, so
`DividedPowers.padicIntAlgebraAtPrime` records the canonical map `ℤ_(p) → ℤ_[p]` — an integer
prime to `p` has `p`-adic norm one, hence is a unit of `ℤ_[p]` — and
`Crystalline.TorsionExample.envelopeIntegersAtPrimeAlgebra` carries it to the envelope.

## Main definitions

* `Crystalline.TorsionExample.frobeniusValues` — the prescribed images `x ↦ x^p`, `y ↦ y^p` of
  the coordinates.
* `Crystalline.TorsionExample.frobeniusLift` — the divided power endomorphism `σ` of
  `(D, J̄, γ̄)` over `A` with `σ(x) = x^p` and `σ(y) = y^p`.

## Main results

* `Crystalline.TorsionExample.frobeniusLift_completedX` and
  `frobeniusLift_completedY` — `σ(x) = x^p` and `σ(y) = y^p`.
* `Crystalline.TorsionExample.frobeniusLift_comp_structureMap` — `σ` is a map over the base
  `A = ℤ_[p]`, which is what makes `x ↦ x^p`, `y ↦ y^p` a lift of the Frobenius of
  `C = 𝐅_p[x, y]/(x², xy, y²)` over `A`.
* `Crystalline.TorsionExample.frobeniusLift_tau` — `σ(τ) = 0`.
* `Crystalline.TorsionExample.not_injective_frobeniusLift_ker_completedDifferential` —
  **conclusion (2) of [Stacks, Tag 07LJ] for the complex of [Stacks, Tag 07LG]**: `σ` is not
  injective on the kernel of the degree zero differential of `D → Ω¹_D → ⋯`.

## What this does and does not say

The source states conclusion (2) for the Frobenius pullback `F^*` on
`H⁰(Cris(X/S), 𝒪_{X/S})`, and gets it from this computation by its own two citations: that the
complex above computes `RΓ(Cris(X/S), 𝒪_{X/S})`, which is
[Stacks, Proposition 60.21.3, Tag 07LG], and that `F^*` acts on `H⁰` as `σ` does on
`ker(d : D → Ω¹_D)`.  The statement proved here is the computation itself, in the terms the
example computes in.  The conclusion about the Frobenius pullback on `H⁰(Cris(X/S), 𝒪_{X/S})`
itself is proved in
`StacksFrontier.AlgebraicGeometry.Crystalline.Examples.TorsionCrystallineCohomology`.

## References

* [Stacks Project, Tag 07LJ](https://stacks.math.columbia.edu/tag/07LJ)
* [Stacks Project, Tag 07H8](https://stacks.math.columbia.edu/tag/07H8)
* [Stacks Project, Tag 07KD](https://stacks.math.columbia.edu/tag/07KD)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public noncomputable section

open DividedPowers

namespace Crystalline

namespace TorsionExample

variable (p : ℕ) [Fact p.Prime]

/-! ### The `ℤ_(p)`-algebra structures the universal property asks for -/

attribute [local instance] padicIntAlgebraAtPrime

/-- The `ℤ_(p)`-algebra structure on the divided power envelope `D_{P, γ}(J)`, through its
structure map from the base `A = ℤ_[p]`. -/
@[instance_reducible]
def envelopeIntegersAtPrimeAlgebra :
    Algebra (IntegersAtPrime p) ((envelope p).object : Type) :=
  ((envelope p).structureMap.toRingHom.comp (algebraMap (IntegersAtPrime p) ℤ_[p])).toAlgebra

attribute [local instance] envelopeIntegersAtPrimeAlgebra

/-! ### `p` lies in the divided power ideals -/

/-- `p` lies in the divided power ideal of the envelope, `J` containing `p` by construction. -/
theorem prime_mem_envelope_ideal : (p : (envelope p).object) ∈ (envelope p).object.ideal := by
  have hpbase : (p : base p) ∈ (base p).ideal := Ideal.subset_span (by simp)
  simpa using (envelope p).structureMap.ideal_comp
    (Ideal.mem_map_of_mem (envelope p).structureMap.toRingHom hpbase)

/-- `p` lies in the divided power ideal `J̄` of `D`. -/
theorem prime_mem_completedIdeal : (p : completedEnvelope p) ∈ completedIdeal p := by
  have h := algebraMap_mem_completedIdeal p (prime_mem_envelope_ideal p)
  rwa [map_natCast] at h

/-! ### The Frobenius lift `σ` -/

/-- `D = D_{P, γ}(J)^∧` packaged as a divided power ring, the shape in which its universal
property `Crystalline.existsUnique_dPMorphism_from_envelopeCompletion` speaks of it. -/
abbrev completedDividedPowerRing : DividedPowerRing :=
  envelopeCompletion (envelope p) p (prime_nilpotent_mod_envelope p)

/-- The prescribed images `x ↦ x^p`, `y ↦ y^p` of the coordinates under the Frobenius lift of
[Stacks, Tag 07LJ]. -/
def frobeniusValues (i : Fin 2) : (completedDividedPowerRing p : Type) :=
  envelopeCompletionCoord (envelope p) p (prime_nilpotent_mod_envelope p) i ^ p

/-- The first prescribed image is `x^p`. -/
theorem frobeniusValues_zero : frobeniusValues p 0 = completedX p ^ p := rfl

/-- The second prescribed image is `y^p`. -/
theorem frobeniusValues_one : frobeniusValues p 1 = completedY p ^ p := rfl

/-- **The compatibility the universal property of `D` asks for.**  The polynomial map
`P → D` sending `x` to `x^p` and `y` to `y^p` carries `J = (p, x², xy, y²)` into the divided power
ideal `J̄` of `D`: the four generators go to `p`, `(x²)^p`, `(xy)^p` and `(y²)^p`, and `J̄` is an
ideal containing `p`, `x²`, `xy` and `y²`. -/
theorem frobeniusValues_map_relations_le :
    (relations p).map (MvPolynomial.eval₂Hom
        (envelopeCompletionStructureMap (envelope p) p
          (prime_nilpotent_mod_envelope p)).toRingHom (frobeniusValues p)) ≤
      (completedDividedPowerRing p).ideal := by
  have hppos : 0 < p := (Fact.out : p.Prime).pos
  set f := MvPolynomial.eval₂Hom (envelopeCompletionStructureMap (envelope p) p
    (prime_nilpotent_mod_envelope p)).toRingHom (frobeniusValues p) with hf
  have hX : f (polynomialX p) = completedX p ^ p := by
    rw [hf, show polynomialX p = MvPolynomial.X 0 from rfl, MvPolynomial.eval₂Hom_X',
      frobeniusValues_zero]
  have hY : f (polynomialY p) = completedY p ^ p := by
    rw [hf, show polynomialY p = MvPolynomial.X 1 from rfl, MvPolynomial.eval₂Hom_X',
      frobeniusValues_one]
  have key : ∀ (q : polynomial p) (w : completedEnvelope p), f q = w ^ p →
      w ∈ completedIdeal p → f q ∈ (completedDividedPowerRing p).ideal :=
    fun q w h hw ↦ h ▸ Ideal.pow_mem_of_mem _ hw p hppos
  refine Ideal.map_le_iff_le_comap.mpr ?_
  show Ideal.span ({(p : polynomial p), polynomialX p ^ 2,
    polynomialX p * polynomialY p, polynomialY p ^ 2} : Set (polynomial p)) ≤ _
  rw [Ideal.span_le]
  rintro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rw [SetLike.mem_coe, Ideal.mem_comap]
  rcases hz with rfl | rfl | rfl | rfl
  · rw [map_natCast]
    exact prime_mem_completedIdeal p
  · exact key _ _ (by rw [map_pow, hX]; exact pow_right_comm _ _ _) (completedX_sq_mem p)
  · exact key _ _ (by rw [map_mul, hX, hY, mul_pow]; rfl) (completedX_mul_completedY_mem p)
  · exact key _ _ (by rw [map_pow, hY]; exact pow_right_comm _ _ _) (completedY_sq_mem p)

/-- **The map `σ : D → D` of the last sentence of [Stacks, Tag 07LJ]**: the divided power
endomorphism of `(D, J̄, γ̄)` over the base `A = ℤ_[p]` induced by the lift of Frobenius
`x ↦ x^p`, `y ↦ y^p` of `P = ℤ_[p][x, y]`.  It exists by the universal property of `D`,
`Crystalline.existsUnique_dPMorphism_from_envelopeCompletion`, the compatibility it asks for
being `Crystalline.TorsionExample.frobeniusValues_map_relations_le`. -/
def frobeniusLift : DPMorphism (completedGamma p) (completedGamma p) :=
  envelopeCompletionLift (envelope p) p (prime_nilpotent_mod_envelope p)
    (completedDividedPowerRing p)
    (isNilpotent_mk_envelopeCompletion (envelope p) p (prime_nilpotent_mod_envelope p))
    (envelopeCompletionStructureMap (envelope p) p (prime_nilpotent_mod_envelope p))
    (frobeniusValues p) (frobeniusValues_map_relations_le p)

/-- `σ` is a map over the base `A = ℤ_[p]`, which is what makes `x ↦ x^p`, `y ↦ y^p` a lift of
the Frobenius of `C` over `A`. -/
theorem frobeniusLift_comp_structureMap :
    (frobeniusLift p).comp (envelopeCompletionStructureMap (envelope p) p
        (prime_nilpotent_mod_envelope p)) =
      envelopeCompletionStructureMap (envelope p) p (prime_nilpotent_mod_envelope p) :=
  envelopeCompletionLift_comp_structureMap (envelope p) p (prime_nilpotent_mod_envelope p)
    _ _ _ _ _

/-- `σ(x) = x^p`. -/
theorem frobeniusLift_completedX : frobeniusLift p (completedX p) = completedX p ^ p :=
  envelopeCompletionLift_coord (envelope p) p (prime_nilpotent_mod_envelope p) _ _ _ _ _ 0

/-- `σ(y) = y^p`. -/
theorem frobeniusLift_completedY : frobeniusLift p (completedY p) = completedY p ^ p :=
  envelopeCompletionLift_coord (envelope p) p (prime_nilpotent_mod_envelope p) _ _ _ _ _ 1

/-- **`σ(τ) = 0`**, the last sentence of [Stacks, Tag 07LJ] for the actual Frobenius lift: `σ`
commutes with `γ̄`, so it carries `τ = γ̄_p(x²) γ̄_p(y²) − γ̄_p(xy)²` to
`γ̄_p(x^{2p}) γ̄_p(y^{2p}) − γ̄_p(x^p y^p)²`, which vanishes by
`Crystalline.TorsionExample.frobeniusTau_eq_zero`. -/
theorem frobeniusLift_tau : frobeniusLift p (tau p) = 0 :=
  map_tau_eq_zero p (frobeniusLift p).isDPMorphism (frobeniusLift_completedX p)
    (frobeniusLift_completedY p)

/-! ### Conclusion (2) of [Stacks, Tag 07LJ] for the complex of [Stacks, Tag 07LG] -/

/-- `σ` kills the nonzero element `τ` of the kernel of the degree zero differential of
`D → Ω¹_D → ⋯`. -/
theorem exists_ne_zero_ker_completedDifferential_frobeniusLift_eq_zero :
    ∃ a : LinearMap.ker (completedDifferential p 0), a ≠ 0 ∧
      frobeniusLift p (completedFormsZeroEquiv p a) = 0 :=
  ⟨⟨tauForm p, LinearMap.mem_ker.mpr (completedDifferential_tauForm p)⟩,
    fun h ↦ tauForm_ne_zero p (congrArg Subtype.val h), by
      rw [show ((⟨tauForm p, LinearMap.mem_ker.mpr (completedDifferential_tauForm p)⟩ :
        LinearMap.ker (completedDifferential p 0)) : completedForms p 0) = tauForm p from rfl,
        completedFormsZeroEquiv_tauForm]
      exact frobeniusLift_tau p⟩

/-- **Conclusion (2) of [Stacks, Tag 07LJ] for the complex of
[Stacks, Proposition 60.21.3, Tag 07LG]**: the Frobenius lift `σ` of the example is not injective
on the kernel of the degree zero differential of

`D → Ω¹_D → Ω²_D → ⋯`.

The element `τ = γ̄_p(x²) γ̄_p(y²) − γ̄_p(xy)²` lies in that kernel, since `dτ = 0`, and is nonzero
there, since it maps to `uv ≠ 0` in the example's own witness thickening; and `σ(τ) = 0`, since
`σ` commutes with the divided powers and `γ̄_p(x^{2p}) γ̄_p(y^{2p}) − γ̄_p(x^p y^p)²` vanishes.  So
`σ` sends the distinct elements `τ` and `0` of the kernel to the same place. -/
theorem not_injective_frobeniusLift_ker_completedDifferential :
    ¬ Function.Injective (fun a : LinearMap.ker (completedDifferential p 0) ↦
      frobeniusLift p (completedFormsZeroEquiv p a)) := by
  intro hinj
  obtain ⟨a, hane, ha⟩ := exists_ne_zero_ker_completedDifferential_frobeniusLift_eq_zero p
  refine hane (hinj ?_)
  show frobeniusLift p (completedFormsZeroEquiv p a) =
    frobeniusLift p (completedFormsZeroEquiv p 0)
  rw [ha, map_zero]
  exact (map_zero (frobeniusLift p).toRingHom).symm

end TorsionExample

end Crystalline

end
