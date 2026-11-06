module

public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.DividedPowers.Padic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.Module
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRham
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRhamExterior
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerEnvelope
public import StacksFrontier.RingTheory.DividedPowers.Criteria
public import StacksFrontier.RingTheory.DividedPowers.Extend

/-!
# The torsion element of the divided power envelope of `𝐅_p[x, y]/(x², xy, y²)`

Fix a prime `p` and take the divided power ring `(A, I, γ) = (ℤ_[p], (p), γ)`, with `γ` the unique
divided powers on `(p) ⊆ ℤ_[p]`.  For `C = 𝐅_p[x, y]/(x², xy, y²)` choose the presentation

`C = P/J = ℤ_[p][x, y]/(p, x², xy, y²)`

and let `D = D_{P, γ}(J)^∧` be the `p`-adic completion of the divided power envelope, with its
divided power ideal `(J̄, γ̄)`.  Writing `x`, `y` also for the images of the variables in `D`, this
file constructs the element

`τ = γ̄_p(x²) γ̄_p(y²) − γ̄_p(xy)² ∈ D`

of [Stacks, Tag 07LJ] and proves the two identities the source computes for it: `p τ = 0`, and
`dτ = 0` in the module `Ω¹_{D/A, γ̄}` of divided power differentials.  It also proves the two
assertions the example's own setup makes: that the presentation really does present `C`, and that
the divided powers `γ` of the base are the only ones on `(p) ⊆ ℤ_[p]`.

## Main definitions

* `Crystalline.TorsionExample.base`, `relations`, `quotientRing` — the divided power ring
  `(ℤ_[p], (p), γ)`, the ideal `J = (p, x², xy, y²)` and the ring `C = P/J`.
* `Crystalline.TorsionExample.residuePolynomial`, `residueRelations`, `residueQuotient` —
  `𝐅_p[x, y]`, its ideal `(x², xy, y²)` and the quotient `𝐅_p[x, y]/(x², xy, y²)`, written out
  independently of the presentation, with `reduceCoefficients` and `presentationMap` the
  reduction `ℤ_[p][x, y] → 𝐅_p[x, y]` and its composite with the quotient map.
* `Crystalline.TorsionExample.envelope` and `completedEnvelope` — the divided power envelope
  `D_{P, γ}(J)` of [Stacks, Tag 07H8] and its `p`-adic completion `D`, with `completedGamma` the
  divided powers `γ̄` on `D` of [Stacks, Tag 07KD].
* `Crystalline.TorsionExample.envelopeTau` and `Crystalline.TorsionExample.tau` — the element
  `γ_p(x²) γ_p(y²) − γ_p(xy)²` of the envelope and its image `τ` in `D`.

## Main results

* `Crystalline.TorsionExample.quotientRingEquiv` — the presentation of the example:
  `P/J = ℤ_[p][x, y]/(p, x², xy, y²) ≅ 𝐅_p[x, y]/(x², xy, y²)`, by coefficient reduction, which
  is surjective with kernel `(p)` (`ker_reduceCoefficients`), so that the contraction of
  `(x², xy, y²)` along it is `J` (`ker_presentationMap`).
* `Crystalline.TorsionExample.base_dividedPowers_unique` — `γ` is the only divided power
  structure on `(p) ⊆ ℤ_[p]`, the uniqueness the example's first sentence asserts.
* `Crystalline.TorsionExample.prime_mul_tau_eq_zero` — `p τ = 0`, from
  `p! γ̄_p(x²) γ̄_p(y²) = x^{2p} γ̄_p(y²) = γ̄_p(x²y²) = x^p y^p γ̄_p(xy) = p! γ̄_p(xy)²` and the
  invertibility of `(p − 1)!`.
* `Crystalline.TorsionExample.dividedPowerDifferential_tau` — `dτ = 0` in `Ω¹_{D/A, γ̄}`, the
  displayed computation of [Stacks, Tag 07LJ].
* `Crystalline.TorsionExample.tau_eq_algebraMap_envelopeTau` — `τ` is the image of the
  envelope-level element `envelopeTau` under `D_{P, γ}(J) → D`, so the nonvanishing of `τ` is the
  statement that this element survives `p`-adic completion.

## The covering set of [Stacks, Tag 07LJ]

The example's assertions and where each is proved:

* `(p) ⊆ ℤ_[p]` carries exactly one divided power structure: `base_dividedPowers_unique`, here.
* `C = P/J = ℤ_[p][x, y]/(p, x², xy, y²)`: `quotientRingEquiv`, here.
* `p τ = 0` in `D`: `prime_mul_tau_eq_zero`, here.
* `dτ = 0` in `Ω_D`: `completedDifferential_tauForm` of `Examples.TorsionCompletedDeRham`, from
  the displayed computation `dividedPowerDifferential_tau` here.
* `τ ↦ uv`, which is nonzero, in the witness thickening `B`: `toWitnessRing_envelopeTau` of
  `Examples.TorsionNonvanishing`.
* `τ ≠ 0` in `D`: `tau_ne_zero` of `Examples.TorsionNonvanishing`.
* `τ` defines a nonzero `p`-torsion element of `H⁰(Cris(X/S), 𝒪_{X/S})`, and conclusion (1):
  `tauClass_ne_zero_and_prime_smul_eq_zero` and
  `exists_ne_zero_prime_smul_eq_zero_cohomologyZero` of `Examples.TorsionCrystallineCohomology`.
* `F^*(τ) = σ(τ)` for `σ` induced by any lift of Frobenius on `P`, and `F^*(τ) = 0` for
  `σ(x) = x^p`, `σ(y) = y^p`: `frobeniusPullback_tauClass_eq_envelopeMapOfLift` and
  `frobeniusPullback_tauClass` of `Examples.TorsionCrystallineCohomology`.
* conclusion (2), `F^*` is not injective on `H⁰(Cris(X/S), 𝒪_{X/S})`:
  `not_injective_frobeniusPullback` of `Examples.TorsionCrystallineCohomology`.

Each holds at every prime, as in the source.  One erratum is repaired along the way.  The
divided powers the source puts on `K = ker(B → C)` come from [Stacks, Tag 07GS],
`DividedPowers.existsUnique_of_prime_operation`, whose hypothesis (3) reads
`δ(k + k') = δ k + ∑_{i + j = p, i, j ≠ 0} k^i k'^j / (i! j!) + δ k'`; for `p = 2` the sum is the
single term `k k'`, and taking `k = u`, `k' = v` gives `δ(u + v) = 0` on the left but
`δ u + uv + δ v = uv ≠ 0` on the right.  So the source's `δ_p` satisfies (3) only for odd `p`,
where every term of the sum is a product of at least three elements of `K` and `K³ = 0`.  At
`p = 2` the cross term `k k'` is itself the polarisation of a quadratic expression in the
coefficients of `u` and `v`, and adding that expression to `δ_p` gives an operation satisfying
all three hypotheses and still sending `x²` to `u` and `y²` to `v`; this is
`DividedPowers.TorsionWitness.dividedPowers`, so the restriction on the prime is removed rather
than recorded. `tau_eq_algebraMap_envelopeTau` reduces the nonvanishing question to the envelope
before completion.

## References

* [Stacks Project, Tag 07LJ](https://stacks.math.columbia.edu/tag/07LJ)
* [Stacks Project, Tag 07GM](https://stacks.math.columbia.edu/tag/07GM)
* [Stacks Project, Tag 07GS](https://stacks.math.columbia.edu/tag/07GS)
* [Stacks Project, Tag 07H8](https://stacks.math.columbia.edu/tag/07H8)
* [Stacks Project, Tag 07KD](https://stacks.math.columbia.edu/tag/07KD)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public section

universe u v

namespace Crystalline

/-! ### Leibniz rules for the divided power differential -/

section Differential

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] {J : Ideal B}
  (hJ : DividedPowers J)

/-- The Leibniz rule for the divided power differential of a square. -/
theorem dividedPowerDifferential_sq (a : B) :
    dividedPowerDifferential (A := A) hJ (a ^ 2) =
      (a + a) • dividedPowerDifferential (A := A) hJ a := by
  rw [sq, dividedPowerDifferential_mul, add_smul]

/-- If `b²` and `c = ab` lie in a divided power ideal, then `aⁿ δ_n(b²) = bⁿ δ_n(c)`: both sides
are `δ_n(ab²)`. -/
private theorem pow_mul_dpow_sq_eq_pow_mul_dpow {n : ℕ} {a b c : B} (hb : b ^ 2 ∈ J) (hc : c ∈ J)
    (habc : a * b = c) : a ^ n * hJ.dpow n (b ^ 2) = b ^ n * hJ.dpow n c := by
  rw [← hJ.dpow_mul hb, ← habc, show a * b ^ 2 = b * (a * b) by ring, hJ.dpow_mul (habc ▸ hc)]

/-- The computation behind [Stacks, Tag 07LJ]: if `x²`, `xy` and `y²` lie in a divided power
ideal, if `xⁿ δ_n(y²) = yⁿ δ_n(xy)` and `yⁿ δ_n(x²) = xⁿ δ_n(xy)`, and if `(n − 1)!` is
invertible, then `δ_n(x²) δ_n(y²) − δ_n(xy)²` is killed by the divided power differential.

Writing `n = q + 1`, the divided power relation `d δ_{q+1}(z) = δ_q(z) dz` and the Leibniz rule
express the differential as a combination of `dx` and `dy`, and multiplying the two coefficients
by `q!` turns every divided power of index `q` into a power by the factorial identity; the two
hypotheses then cancel the coefficients outright. -/
theorem dividedPowerDifferential_dpow_mul_sub_sq_eq_zero {n : ℕ} (hn : n ≠ 0) {X Y : B}
    (hx : X ^ 2 ∈ J) (hy : Y ^ 2 ∈ J) (hz : X * Y ∈ J)
    (hswapx : X ^ n * hJ.dpow n (Y ^ 2) = Y ^ n * hJ.dpow n (X * Y))
    (hswapy : Y ^ n * hJ.dpow n (X ^ 2) = X ^ n * hJ.dpow n (X * Y))
    (hunit : IsUnit (((n - 1).factorial : B))) :
    dividedPowerDifferential (A := A) hJ
      (hJ.dpow n (X ^ 2) * hJ.dpow n (Y ^ 2) - hJ.dpow n (X * Y) ^ 2) = 0 := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hunit
  have hdg : ∀ z ∈ J, dividedPowerDifferential (A := A) hJ (hJ.dpow (q + 1) z) =
      hJ.dpow q z • dividedPowerDifferential (A := A) hJ z := fun z hz => by
    simpa using dividedPowerDifferential_dpow (A := A) hJ ⟨z, hz⟩ q
  have hexp : dividedPowerDifferential (A := A) hJ
        (hJ.dpow (q + 1) (X ^ 2) * hJ.dpow (q + 1) (Y ^ 2) - hJ.dpow (q + 1) (X * Y) ^ 2) =
      (hJ.dpow (q + 1) (Y ^ 2) * hJ.dpow q (X ^ 2) * (X + X) -
          (hJ.dpow (q + 1) (X * Y) + hJ.dpow (q + 1) (X * Y)) * hJ.dpow q (X * Y) * Y) •
            dividedPowerDifferential (A := A) hJ X +
        (hJ.dpow (q + 1) (X ^ 2) * hJ.dpow q (Y ^ 2) * (Y + Y) -
          (hJ.dpow (q + 1) (X * Y) + hJ.dpow (q + 1) (X * Y)) * hJ.dpow q (X * Y) * X) •
            dividedPowerDifferential (A := A) hJ Y := by
    rw [dividedPowerDifferential_sub, dividedPowerDifferential_mul,
      dividedPowerDifferential_sq (hJ := hJ) (hJ.dpow (q + 1) (X * Y)), hdg _ hx, hdg _ hy,
      hdg _ hz, dividedPowerDifferential_sq (hJ := hJ) X, dividedPowerDifferential_sq (hJ := hJ) Y,
      dividedPowerDifferential_mul]
    module
  have hcoeff : ∀ a b c : B, a ^ 2 ∈ J → c ∈ J → a * b = c →
      a ^ (q + 1) * hJ.dpow (q + 1) (b ^ 2) = b ^ (q + 1) * hJ.dpow (q + 1) c →
      ((q.factorial : B)) * (hJ.dpow (q + 1) (b ^ 2) * hJ.dpow q (a ^ 2) * (a + a) -
        (hJ.dpow (q + 1) c + hJ.dpow (q + 1) c) * hJ.dpow q c * b) = 0 := by
    intro a b c ha hc habc hs
    subst habc
    linear_combination (hJ.dpow (q + 1) (b ^ 2) * (a + a)) * hJ.factorial_mul_dpow_eq_pow ha -
      ((hJ.dpow (q + 1) (a * b) + hJ.dpow (q + 1) (a * b)) * b) *
        hJ.factorial_mul_dpow_eq_pow hc + (2 * a ^ q) * hs
  have hsmul : ((q.factorial : B)) • dividedPowerDifferential (A := A) hJ
      (hJ.dpow (q + 1) (X ^ 2) * hJ.dpow (q + 1) (Y ^ 2) - hJ.dpow (q + 1) (X * Y) ^ 2) = 0 := by
    rw [hexp, smul_add, smul_smul, smul_smul, hcoeff X Y (X * Y) hx hz rfl hswapx,
      hcoeff Y X (X * Y) hy hz (mul_comm Y X) hswapy, zero_smul, zero_smul, add_zero]
  obtain ⟨u, hu⟩ := hunit
  have hinv := congrArg (fun m => ((u⁻¹ : Bˣ) : B) • m) hsmul
  simpa only [smul_smul, ← hu, Units.inv_mul, one_smul, smul_zero] using hinv

end Differential

namespace TorsionExample

variable (p : ℕ) [Fact p.Prime]

/-! ### The presentation `C = P/J` -/

/-- The polynomial ring `P = ℤ_[p][x, y]` of the presentation. -/
abbrev polynomial : Type := MvPolynomial (Fin 2) ℤ_[p]

/-- The variable `x` of `P = ℤ_[p][x, y]`. -/
noncomputable abbrev polynomialX : polynomial p := MvPolynomial.X 0

/-- The variable `y` of `P = ℤ_[p][x, y]`. -/
noncomputable abbrev polynomialY : polynomial p := MvPolynomial.X 1

/-- The ideal `J = (p, x², xy, y²)` of `P`, chosen so that `P/J = 𝐅_p[x, y]/(x², xy, y²)`. -/
noncomputable def relations : Ideal (polynomial p) :=
  Ideal.span ({(p : polynomial p), polynomialX p ^ 2,
    polynomialX p * polynomialY p, polynomialY p ^ 2} : Set (polynomial p))

/-- The ring `C = 𝐅_p[x, y]/(x², xy, y²)`, presented as `P/J`. -/
abbrev quotientRing : Type := polynomial p ⧸ relations p

/-- The polynomial ring `𝐅_p[x, y]`. -/
abbrev residuePolynomial : Type := MvPolynomial (Fin 2) (ZMod p)

/-- The variable `x` of `𝐅_p[x, y]`. -/
noncomputable abbrev residueX : residuePolynomial p := MvPolynomial.X 0

/-- The variable `y` of `𝐅_p[x, y]`. -/
noncomputable abbrev residueY : residuePolynomial p := MvPolynomial.X 1

/-- The ideal `(x², xy, y²)` of `𝐅_p[x, y]`. -/
noncomputable def residueRelations : Ideal (residuePolynomial p) :=
  Ideal.span ({residueX p ^ 2, residueX p * residueY p,
    residueY p ^ 2} : Set (residuePolynomial p))

/-- The ring `𝐅_p[x, y]/(x², xy, y²)` on the nose. -/
abbrev residueQuotient : Type := residuePolynomial p ⧸ residueRelations p

/-- Reduction of coefficients `P = ℤ_[p][x, y] → 𝐅_p[x, y]` along `ℤ_[p] → 𝐅_p`. -/
noncomputable def reduceCoefficients : polynomial p →+* residuePolynomial p :=
  MvPolynomial.map (PadicInt.toZMod (p := p))

/-- Coefficient reduction is surjective, `ℤ_[p] → 𝐅_p` being so. -/
theorem reduceCoefficients_surjective : Function.Surjective (reduceCoefficients p) :=
  MvPolynomial.map_surjective _ fun z => ⟨(z.val : ℤ_[p]), by simp⟩

/-- The kernel of coefficient reduction is `(p)`: a polynomial reduces to zero exactly when
every one of its coefficients lies in `ker(ℤ_[p] → 𝐅_p) = (p)`. -/
theorem ker_reduceCoefficients :
    RingHom.ker (reduceCoefficients p) = Ideal.span {(p : polynomial p)} := by
  have hC : (p : polynomial p) = MvPolynomial.C (p : ℤ_[p]) := by simp
  have hdvd : ∀ a : ℤ_[p], PadicInt.toZMod a = 0 ↔ (p : ℤ_[p]) ∣ a := fun a => by
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton]
  ext f
  rw [RingHom.mem_ker, MvPolynomial.ext_iff, Ideal.mem_span_singleton, hC,
    MvPolynomial.C_dvd_iff_dvd_coeff]
  simp only [reduceCoefficients, MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero,
    Finsupp.zero_apply, hdvd]

/-- Coefficient reduction carries the three quadratic generators of `J` onto the three
generators of `(x², xy, y²) ⊆ 𝐅_p[x, y]`. -/
theorem map_reduceCoefficients_squares :
    Ideal.map (reduceCoefficients p)
        (Ideal.span ({polynomialX p ^ 2, polynomialX p * polynomialY p,
          polynomialY p ^ 2} : Set (polynomial p))) = residueRelations p := by
  rw [Ideal.map_span, residueRelations]
  congr 1
  simp [reduceCoefficients, Set.image_insert_eq]

/-- The presentation map `P = ℤ_[p][x, y] → 𝐅_p[x, y]/(x², xy, y²)`: reduce the coefficients
modulo `p`, then pass to the quotient by `(x², xy, y²)`. -/
noncomputable def presentationMap : polynomial p →+* residueQuotient p :=
  (Ideal.Quotient.mk (residueRelations p)).comp (reduceCoefficients p)

/-- The presentation map is surjective, being a surjection followed by a quotient map. -/
theorem presentationMap_surjective : Function.Surjective (presentationMap p) :=
  Ideal.Quotient.mk_surjective.comp (reduceCoefficients_surjective p)

/-- The kernel of the presentation map is exactly `J = (p, x², xy, y²)`.

The kernel is the contraction of `(x², xy, y²)` along coefficient reduction, and coefficient
reduction is surjective, so that contraction is the sum of `(x², xy, y²)` with the kernel
`(p)`. -/
theorem ker_presentationMap : RingHom.ker (presentationMap p) = relations p := by
  have hcomap : RingHom.ker (presentationMap p) =
      Ideal.comap (reduceCoefficients p) (residueRelations p) := by
    ext f
    simp [presentationMap, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap]
  rw [hcomap, ← map_reduceCoefficients_squares,
    Ideal.comap_map_of_surjective _ (reduceCoefficients_surjective p),
    ← RingHom.ker_eq_comap_bot, ker_reduceCoefficients, relations, ← Ideal.span_union]
  congr 1
  ext z
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- **The presentation of [Stacks, Tag 07LJ].**  Coefficient reduction induces a ring
isomorphism

`P/J = ℤ_[p][x, y]/(p, x², xy, y²) ≅ 𝐅_p[x, y]/(x², xy, y²) = C`

carrying the class of `x` to `x` and the class of `y` to `y`, which is the identification the
example writes as `C = P/J`.  Its effect on classes is `quotientRingEquiv_mk`. -/
@[stacks 07LJ "the example's presentation C = P/J: reduction of coefficients \
ZZ_p[x, y] -> F_p[x, y] induces a ring isomorphism ZZ_p[x, y]/(p, x^2, xy, y^2) = \
F_p[x, y]/(x^2, xy, y^2), carrying the class of each variable to that variable"]
noncomputable def quotientRingEquiv : quotientRing p ≃+* residueQuotient p :=
  (Ideal.quotEquivOfEq (ker_presentationMap p).symm).trans
    (RingHom.quotientKerEquivOfSurjective (presentationMap_surjective p))

/-- The presentation isomorphism sends the class of `f ∈ P` to the class of the reduction of
`f` modulo `p`. -/
@[simp]
theorem quotientRingEquiv_mk (f : polynomial p) :
    quotientRingEquiv p (Ideal.Quotient.mk (relations p) f) =
      Ideal.Quotient.mk (residueRelations p) (reduceCoefficients p f) := rfl

/-- The presentation isomorphism carries the class of `x` to `x`. -/
theorem quotientRingEquiv_mk_polynomialX :
    quotientRingEquiv p (Ideal.Quotient.mk (relations p) (polynomialX p)) =
      Ideal.Quotient.mk (residueRelations p) (residueX p) := by
  rw [quotientRingEquiv_mk]
  simp [reduceCoefficients]

/-- The presentation isomorphism carries the class of `y` to `y`. -/
theorem quotientRingEquiv_mk_polynomialY :
    quotientRingEquiv p (Ideal.Quotient.mk (relations p) (polynomialY p)) =
      Ideal.Quotient.mk (residueRelations p) (residueY p) := by
  rw [quotientRingEquiv_mk]
  simp [reduceCoefficients]

/-- The base divided power ring `(A, I, γ) = (ℤ_[p], (p), γ)`. -/
noncomputable abbrev base : DividedPowerRing :=
  DividedPowerRing.of ℤ_[p] (Ideal.span {(p : ℤ_[p])}) (PadicInt.dividedPowers p)

/-- **The base of [Stacks, Tag 07LJ] is uniquely divided.**  The divided powers `γ` on the ideal
`(p) ⊆ ℤ_[p]` are the only ones: `ℤ_[p]` is torsion free as a `ℤ`-module, so `n! γ_n(a) = aⁿ`
determines `γ_n(a)`, which is the uniqueness half of [Stacks, Tag 07GM]. -/
@[stacks 07LJ "the example's base: the ideal (p) of ZZ_p has exactly one divided power \
structure, so gamma is determined"]
theorem base_dividedPowers_unique (γ : DividedPowers (Ideal.span {(p : ℤ_[p])})) :
    γ = PadicInt.dividedPowers p :=
  Subsingleton.elim _ _

/-- The base divided power ideal `(p)` maps into `J`, as `J` was chosen to contain `p`. -/
theorem baseIdeal_le_relations :
    (base p).ideal.map (algebraMap (base p) (polynomial p)) ≤ relations p := by
  rw [Ideal.map_le_iff_le_comap]
  show Ideal.span {(p : ℤ_[p])} ≤ _
  rw [Ideal.span_le]
  intro z hz
  simp only [Set.mem_singleton_iff] at hz
  subst z
  show algebraMap ℤ_[p] (polynomial p) (p : ℤ_[p]) ∈ relations p
  exact Ideal.subset_span (by simp)

/-! ### The divided power envelope and its `p`-adic completion -/

/-- The divided power envelope `D_{P, γ}(J)` of the presentation, [Stacks, Tag 07H8]. -/
noncomputable def envelope :
    DividedPowerEnvelope (base p) (algebraMap (base p) (polynomial p)) (relations p)
      (baseIdeal_le_relations p) :=
  dividedPowerEnvelope (base p) (algebraMap (base p) (polynomial p)) (relations p)
    (baseIdeal_le_relations p)

/-- The image in the envelope of an element of `J` lies in the divided power ideal. -/
theorem envelope_image_mem {z : polynomial p} (hz : z ∈ relations p) :
    (envelope p).algebraMap.toRingHom z ∈ (envelope p).object.ideal :=
  (envelope p).algebraMap.ideal_comp
    (Ideal.mem_map_of_mem (envelope p).algebraMap.toRingHom hz)

/-- The prime `p` is nilpotent in the quotient of the envelope by its divided power ideal:
it is already zero there, because `p ∈ J`. -/
theorem prime_nilpotent_mod_envelope :
    IsNilpotent (Ideal.Quotient.mk (envelope p).object.ideal
      (p : (envelope p).object)) := by
  refine ⟨1, ?_⟩
  have hp : (p : (envelope p).object) ∈ (envelope p).object.ideal := by
    have hpbase : (p : base p) ∈ (base p).ideal := by
      show (p : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p])}
      exact Ideal.subset_span (by simp)
    have hmap := Ideal.mem_map_of_mem (envelope p).structureMap.toRingHom hpbase
    have hle := (envelope p).structureMap.ideal_comp
    simpa using hle hmap
  simpa only [pow_one] using Ideal.Quotient.eq_zero_iff_mem.mpr hp

/-- The `p`-adically completed divided power envelope `D = D_{P, γ}(J)^∧`. -/
noncomputable abbrev completedEnvelope : Type :=
  AdicCompletion (DividedPowers.pAdicIdeal (A := (envelope p).object) p) (envelope p).object

/-- The divided power ideal `J̄` of `D`, [Stacks, Tag 07KD]. -/
noncomputable abbrev completedIdeal : Ideal (completedEnvelope p) :=
  DividedPowers.completionIdeal (envelope p).object.ideal p (prime_nilpotent_mod_envelope p)

/-- The divided powers `γ̄` on `J̄ ⊆ D`, [Stacks, Tag 07KD]. -/
noncomputable def completedGamma : DividedPowers (completedIdeal p) :=
  (DividedPowers.completedDividedPowers (envelope p).object.ideal
    (envelope p).object.dividedPowers p (prime_nilpotent_mod_envelope p)).1

/-- The completed envelope is an algebra over the base `ℤ_[p]`, through the structure map of the
envelope. -/
noncomputable instance instAlgebraBaseCompletedEnvelope : Algebra ℤ_[p] (completedEnvelope p) :=
  ((algebraMap (envelope p).object (completedEnvelope p)).comp
    (envelope p).structureMap.toRingHom).toAlgebra

/-- The image in `D` of an element of the divided power ideal of the envelope lies in `J̄`. -/
theorem algebraMap_mem_completedIdeal {w : (envelope p).object}
    (hw : w ∈ (envelope p).object.ideal) :
    algebraMap (envelope p).object (completedEnvelope p) w ∈ completedIdeal p := by
  have hmap : AdicCompletion.map (DividedPowers.pAdicIdeal (A := (envelope p).object) p)
      (envelope p).object.ideal.subtype
      (AdicCompletion.of (DividedPowers.pAdicIdeal (A := (envelope p).object) p)
        (envelope p).object.ideal ⟨w, hw⟩) =
      algebraMap (envelope p).object (completedEnvelope p) w := by
    rw [AdicCompletion.algebraMap_apply]
    simpa using AdicCompletion.map_of
      (DividedPowers.pAdicIdeal (A := (envelope p).object) p)
      (envelope p).object.ideal.subtype ⟨w, hw⟩
  rw [← hmap]
  exact DividedPowers.completion_map_subtype_mem (envelope p).object.ideal p
    (prime_nilpotent_mod_envelope p) _

/-- The completed divided powers of the image of an element of the divided power ideal of the
envelope are the image of its divided powers, [Stacks, Tag 07KD]. -/
theorem completedGamma_dpow_algebraMap (n : ℕ) {w : (envelope p).object}
    (hw : w ∈ (envelope p).object.ideal) :
    (completedGamma p).dpow n (algebraMap (envelope p).object (completedEnvelope p) w) =
      algebraMap (envelope p).object (completedEnvelope p)
        ((envelope p).object.dividedPowers.dpow n w) :=
  (DividedPowers.completedDividedPowers (envelope p).object.ideal
    (envelope p).object.dividedPowers p (prime_nilpotent_mod_envelope p)).2 n w hw
      ⟨algebraMap (envelope p).object (completedEnvelope p) w,
        algebraMap_mem_completedIdeal p hw⟩ rfl

/-! ### The variables and the element `τ` -/

/-- The image of the variable `x` in the divided power envelope. -/
noncomputable def envelopeX : (envelope p).object :=
  (envelope p).algebraMap.toRingHom (polynomialX p)

/-- The image of the variable `y` in the divided power envelope. -/
noncomputable def envelopeY : (envelope p).object :=
  (envelope p).algebraMap.toRingHom (polynomialY p)

/-- `x²` lies in the divided power ideal of the envelope. -/
theorem envelopeX_sq_mem : envelopeX p ^ 2 ∈ (envelope p).object.ideal := by
  rw [envelopeX, ← map_pow]
  exact envelope_image_mem p (Ideal.subset_span (by simp))

/-- `xy` lies in the divided power ideal of the envelope. -/
theorem envelopeX_mul_envelopeY_mem :
    envelopeX p * envelopeY p ∈ (envelope p).object.ideal := by
  rw [envelopeX, envelopeY, ← map_mul]
  exact envelope_image_mem p (Ideal.subset_span (by simp))

/-- `y²` lies in the divided power ideal of the envelope. -/
theorem envelopeY_sq_mem : envelopeY p ^ 2 ∈ (envelope p).object.ideal := by
  rw [envelopeY, ← map_pow]
  exact envelope_image_mem p (Ideal.subset_span (by simp))

/-- The image of the variable `x` in `D`. -/
noncomputable def completedX : completedEnvelope p :=
  algebraMap (envelope p).object (completedEnvelope p) (envelopeX p)

/-- The image of the variable `y` in `D`. -/
noncomputable def completedY : completedEnvelope p :=
  algebraMap (envelope p).object (completedEnvelope p) (envelopeY p)

/-- `x²` lies in the divided power ideal `J̄` of `D`. -/
theorem completedX_sq_mem : completedX p ^ 2 ∈ completedIdeal p := by
  rw [completedX, ← map_pow]
  exact algebraMap_mem_completedIdeal p (envelopeX_sq_mem p)

/-- `xy` lies in the divided power ideal `J̄` of `D`. -/
theorem completedX_mul_completedY_mem : completedX p * completedY p ∈ completedIdeal p := by
  rw [completedX, completedY, ← map_mul]
  exact algebraMap_mem_completedIdeal p (envelopeX_mul_envelopeY_mem p)

/-- `y²` lies in the divided power ideal `J̄` of `D`. -/
theorem completedY_sq_mem : completedY p ^ 2 ∈ completedIdeal p := by
  rw [completedY, ← map_pow]
  exact algebraMap_mem_completedIdeal p (envelopeY_sq_mem p)

/-- The element `γ_p(x²) γ_p(y²) − γ_p(xy)²` of the divided power envelope, before
completion. -/
noncomputable def envelopeTau : (envelope p).object :=
  (envelope p).object.dividedPowers.dpow p (envelopeX p ^ 2) *
      (envelope p).object.dividedPowers.dpow p (envelopeY p ^ 2) -
    (envelope p).object.dividedPowers.dpow p (envelopeX p * envelopeY p) ^ 2

/-- The element `τ = γ̄_p(x²) γ̄_p(y²) − γ̄_p(xy)²` of `D`. -/
noncomputable def tau : completedEnvelope p :=
  (completedGamma p).dpow p (completedX p ^ 2) * (completedGamma p).dpow p (completedY p ^ 2) -
    (completedGamma p).dpow p (completedX p * completedY p) ^ 2

/-- `τ` is the image of the envelope-level element `envelopeTau`: the three divided powers
entering `τ` are taken of elements already defined in the envelope, so `τ ≠ 0` is exactly the
statement that `envelopeTau` survives `p`-adic completion. -/
theorem tau_eq_algebraMap_envelopeTau :
    tau p = algebraMap (envelope p).object (completedEnvelope p) (envelopeTau p) := by
  rw [tau, envelopeTau, completedX, completedY, map_sub, map_mul, map_pow, ← map_pow, ← map_pow,
    ← map_mul, completedGamma_dpow_algebraMap p p (envelopeX_sq_mem p),
    completedGamma_dpow_algebraMap p p (envelopeY_sq_mem p),
    completedGamma_dpow_algebraMap p p (envelopeX_mul_envelopeY_mem p)]

/-! ### `p τ = 0` -/

/-- `(p − 1)!` is invertible in `ℤ_[p]`. -/
private theorem isUnit_factorial_pred : IsUnit (((p - 1).factorial : ℤ_[p])) := by
  have hp : p.Prime := Fact.out
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  exact Nat.Prime.coprime_factorial_of_lt hp (by have := hp.pos; omega)

/-- `(p − 1)!` is invertible in `D`, being the image of a unit of `ℤ_[p]`. -/
private theorem isUnit_factorial_pred_completedEnvelope :
    IsUnit (((p - 1).factorial : completedEnvelope p)) := by
  simpa only [map_natCast] using
    (isUnit_factorial_pred p).map (algebraMap ℤ_[p] (completedEnvelope p))

/-- `p! = p · (p − 1)!` in any commutative ring. -/
private theorem factorial_eq_prime_mul {R : Type*} [CommRing R] :
    (p.factorial : R) = (p : R) * ((p - 1).factorial : R) := by
  have hp : p.Prime := Fact.out
  have hs : p = (p - 1) + 1 := by have := hp.pos; omega
  rw [hs, Nat.factorial_succ, Nat.cast_mul]
  norm_num

/-- `p! τ = 0`: both products in `p! τ` equal `γ̄_p(x²y²)`. -/
private theorem factorial_mul_tau_eq_zero :
    (p.factorial : completedEnvelope p) * tau p = 0 := by
  have hz := completedX_mul_completedY_mem p
  have hfacx := (completedGamma p).factorial_mul_dpow_eq_pow (n := p) (completedX_sq_mem p)
  have hfacz := (completedGamma p).factorial_mul_dpow_eq_pow (n := p) hz
  have hmulx := (completedGamma p).dpow_mul (n := p) (a := completedX p ^ 2) (completedY_sq_mem p)
  have hmulz := (completedGamma p).dpow_mul (n := p) (a := completedX p * completedY p) hz
  rw [tau, mul_sub, sq ((completedGamma p).dpow p (completedX p * completedY p)), ← mul_assoc,
    ← mul_assoc, hfacx, hfacz, ← hmulx, ← hmulz,
    show completedX p ^ 2 * completedY p ^ 2 =
      (completedX p * completedY p) * (completedX p * completedY p) by ring, sub_self]

/-- **`p τ = 0`.**  Multiplying `τ` by `p!` gives
`γ̄_p(x²y²) − γ̄_p((xy)(xy)) = 0`, and `p! = p (p − 1)!` with `(p − 1)!` invertible. -/
@[stacks 07LJ "the example's identity p τ = 0 in D, for \
τ = gammabar_p(x^2) gammabar_p(y^2) - gammabar_p(xy)^2, by the example's own display \
p! gammabar_p(x^2) gammabar_p(y^2) = x^{2p} gammabar_p(y^2) = gammabar_p(x^2 y^2) = \
x^p y^p gammabar_p(xy) = p! gammabar_p(xy)^2 together with the invertibility of (p-1)! in D"]
theorem prime_mul_tau_eq_zero : (p : completedEnvelope p) * tau p = 0 := by
  refine (isUnit_factorial_pred_completedEnvelope p).mul_right_eq_zero.mp ?_
  rw [← mul_assoc, mul_comm ((p - 1).factorial : completedEnvelope p),
    ← factorial_eq_prime_mul p, factorial_mul_tau_eq_zero]

/-! ### `dτ = 0` -/

/-- **`dτ = 0` in `Ω¹_{D/A, γ̄}`.**  This is the displayed computation of [Stacks, Tag 07LJ]: the
divided power relation `d γ̄_n(z) = γ̄_{n-1}(z) dz` turns `dτ` into
`2 (p − 1)!⁻¹ (x^{2p−1} γ̄_p(y²) dx + y^{2p−1} γ̄_p(x²) dy
  − x^{p−1} y^p γ̄_p(xy) dx − x^p y^{p−1} γ̄_p(xy) dy)`,
and both brackets vanish by `x^p γ̄_p(y²) = y^p γ̄_p(xy)` and `y^p γ̄_p(x²) = x^p γ̄_p(xy)`. -/
theorem dividedPowerDifferential_tau :
    dividedPowerDifferential (A := ℤ_[p]) (completedGamma p) (tau p) = 0 := by
  have hp : p.Prime := Fact.out
  rw [tau]
  exact dividedPowerDifferential_dpow_mul_sub_sq_eq_zero (A := ℤ_[p]) (completedGamma p)
    hp.ne_zero (completedX_sq_mem p) (completedY_sq_mem p) (completedX_mul_completedY_mem p)
    (pow_mul_dpow_sq_eq_pow_mul_dpow _ (completedY_sq_mem p) (completedX_mul_completedY_mem p) rfl)
    (pow_mul_dpow_sq_eq_pow_mul_dpow _ (completedX_sq_mem p) (completedX_mul_completedY_mem p)
      (mul_comm _ _))
    (isUnit_factorial_pred_completedEnvelope p)

end TorsionExample

end Crystalline

end
