module

public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# The primitive polynomial cutting out a primitive element

Step C of the proof of Stacks Tag 0559, over the base of the transcendence basis. Let `R` be a
GCD domain with fraction field `F`, let `L/F` be a field extension and let `θ ∈ L` be algebraic
over `F`. Clearing the denominators of the minimal polynomial of `θ` and dividing out the
content produces a *primitive* polynomial `q ∈ R[T]` which is irreducible both in `R[T]` and
over `F`, and which generates the kernel of `R[T] ⟶ L`, `T ↦ θ`.

In the application of Tag 0559, `R` is the polynomial ring in a separating transcendence basis
`x₁, …, x_r` of the function field `L` of the generic fibre, `F = K(x₁, …, x_r)` and
`θ = x_{r+1}` is the primitive element supplied by Step B; the polynomial `q` is the `P` of the
source, and the presentation `R[T]/(q) ↪ L` with `L` as its fraction field is what Step D turns
into a scheme over the base.

## Main results

* `IsFractionRing.exists_isPrimitive_irreducible_aeval_eq_zero_iff_dvd`: existence of `q`, with
  its primitivity, its irreducibility in `R[T]` and over `F`, the characterization of the
  elements of `R[T]` vanishing at `θ` as the multiples of `q`, and the kernel of the evaluation
  as the ideal it generates.

## Implementation notes

`q` is `(IsLocalization.integerNormalization R⁰ (minpoly F θ)).primPart`: the integer
normalization clears the denominators and the primitive part divides out the content, which is
what makes Gauss's lemma (`Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map`)
and the descent of divisibility
(`Polynomial.IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map`) available. The source says
only "clearing denominators"; dividing out the content is needed because over a GCD domain it
is primitivity, not monicity, that transfers irreducibility and divisibility between `R[T]` and
`F[T]`.

The conclusion records the divisibility characterization as well as the equality of ideals: the
former is what the construction of the quotient ring uses, the latter is the statement that the
quotient is a domain with `L` as its fraction field.

`R` carries `NormalizedGCDMonoid`, which is how `Polynomial.content` and
`Polynomial.primPart` are available; a unique factorization domain can be given one by
`UniqueFactorizationMonoid.toNormalizedGCDMonoid`.

No Stacks tag is attached: Step C is not itself a tag of the source.

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559), Step C of the first
  proof
-/

@[expose] public section

open scoped nonZeroDivisors

open Polynomial

namespace IsFractionRing

variable {R F L : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field L] [Algebra R L] [Algebra F L] [IsScalarTower R F L]

omit [Algebra R L] [IsScalarTower R F L] in
/-- The primitive part of the integer normalization of the minimal polynomial of `θ` is
associated, over `F`, to that minimal polynomial. -/
private theorem associated_primPart_integerNormalization_minpoly {θ : L} (hθ : IsIntegral F θ) :
    Associated (minpoly F θ)
      ((IsLocalization.integerNormalization R⁰ (minpoly F θ)).primPart.map
        (algebraMap R F)) := by
  set p : F[X] := minpoly F θ with hp
  set q₀ : R[X] := IsLocalization.integerNormalization R⁰ p with hq₀
  have hp0 : p ≠ 0 := minpoly.ne_zero hθ
  have hq₀0 : q₀ ≠ 0 := fun h ↦ hp0 (IsFractionRing.integerNormalization_eq_zero_iff.mp h)
  obtain ⟨b, hb, hbmap⟩ := IsLocalization.integerNormalization_spec R⁰ p
  have hb0 : algebraMap R F b ≠ 0 := by
    have : (b : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
    simpa [IsFractionRing.to_map_eq_zero_iff] using this
  have hc0 : algebraMap R F q₀.content ≠ 0 := by
    have : q₀.content ≠ 0 := fun h ↦ hq₀0 (content_eq_zero_iff.mp h)
    simpa [IsFractionRing.to_map_eq_zero_iff] using this
  have hsplit : C (algebraMap R F b) * p =
      C (algebraMap R F q₀.content) * q₀.primPart.map (algebraMap R F) := by
    calc C (algebraMap R F b) * p = q₀.map (algebraMap R F) := by
          rw [hbmap, Algebra.smul_def, algebraMap_apply]
      _ = C (algebraMap R F q₀.content) * q₀.primPart.map (algebraMap R F) := by
          conv_lhs => rw [q₀.eq_C_content_mul_primPart]
          rw [Polynomial.map_mul, map_C]
  have hub : IsUnit (C (algebraMap R F b) : F[X]) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr hb0)
  have huc : IsUnit (C (algebraMap R F q₀.content) : F[X]) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0)
  refine (associated_unit_mul_left p _ hub).symm.trans ?_
  rw [hsplit]
  exact associated_unit_mul_left _ _ huc

/-- **Step C of Stacks Tag 0559.** Let `R` be a GCD domain with fraction field `F`, let `L` be a
field extension of `F` and let `θ ∈ L` be algebraic over `F`. Then there is a primitive
polynomial `q ∈ R[T]` which is irreducible in `R[T]`, whose image in `F[T]` is irreducible, and
whose multiples are exactly the polynomials over `R` vanishing at `θ`; equivalently, `q`
generates the kernel of evaluation at `θ`. -/
theorem exists_isPrimitive_irreducible_aeval_eq_zero_iff_dvd {θ : L} (hθ : IsIntegral F θ) :
    ∃ q : R[X], q.IsPrimitive ∧ Irreducible q ∧ Irreducible (q.map (algebraMap R F)) ∧
      (∀ g : R[X], aeval θ g = 0 ↔ q ∣ g) ∧
      RingHom.ker (aeval θ : R[X] →ₐ[R] L).toRingHom = Ideal.span {q} := by
  set p : F[X] := minpoly F θ with hp
  set q : R[X] := (IsLocalization.integerNormalization R⁰ p).primPart with hq
  have hprim : q.IsPrimitive := isPrimitive_primPart _
  have hassoc : Associated p (q.map (algebraMap R F)) :=
    associated_primPart_integerNormalization_minpoly hθ
  have hirrF : Irreducible (q.map (algebraMap R F)) :=
    hassoc.irreducible (minpoly.irreducible hθ)
  have hdvd : ∀ g : R[X], aeval θ g = 0 ↔ q ∣ g := by
    intro g
    rw [hprim.dvd_iff_fraction_map_dvd_fraction_map F, ← hassoc.dvd_iff_dvd_left,
      ← Polynomial.aeval_map_algebraMap (A := F) θ g]
    exact ⟨fun h ↦ minpoly.dvd F θ h, fun ⟨k, hk⟩ ↦ by
      rw [hk, map_mul, minpoly.aeval, zero_mul]⟩
  refine ⟨q, hprim, hprim.irreducible_iff_irreducible_map_fraction_map.mpr hirrF, hirrF, hdvd, ?_⟩
  ext g
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  exact hdvd g

end IsFractionRing

end
