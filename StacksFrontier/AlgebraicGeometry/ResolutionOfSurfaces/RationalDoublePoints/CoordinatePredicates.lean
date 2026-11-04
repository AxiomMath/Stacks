module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.GoodCoordinate
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.CaseOneChart
public import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!
# Good and special coordinates of a rational double point

Let `B` be a local ring with maximal ideal `𝔪`. For an element `x₁` of `𝔪` we consider two
conditions:

* **`x₁` is a good coordinate** (case I): `x₁` is the first of three generators `x₁, x₂, x₃` of
  the maximal ideal satisfying a quadratic relation `Σ aᵢⱼ xᵢxⱼ ∈ 𝔪³` whose quadratic form `q`
  has `q(0, t₂, t₃)` not a scalar times a square;
* **`x₁` is a special coordinate**: there are generators `x₁, x₂, x₃` with
  `x₃² + x₁(a x₂² + b x₂x₃ + c x₃²) ∈ 𝔪⁴`.

The singularity itself is in **case I** when some quadratic relation among three generators has a
quadratic form which is not a scalar times a square.

All three are carried along any local homomorphism `B → B'` extending the maximal ideal of `B`
to that of `B'` and inducing an isomorphism of residue fields, in particular along ring
isomorphisms and to the completion.

## Main definitions

* `AlgebraicGeometry.IsFirstGeneratorOfGoodRelation`: a good coordinate, in the form without the
  clause that some coefficient of the relation is a unit (that clause follows from the form, see
  `AlgebraicGeometry.exists_notMem_maximalIdeal_of_isGoodCoordinateForm`).
* `AlgebraicGeometry.IsSpecialCoordinate`: a special coordinate.

Case I is `AlgebraicGeometry.IsCaseOne`.

## Main results

* `AlgebraicGeometry.IsFirstGeneratorOfGoodRelation.map`,
  `AlgebraicGeometry.IsSpecialCoordinate.map`, `AlgebraicGeometry.IsCaseOne.map_of_bijective`:
  the three conditions are carried along such a homomorphism.
-/

@[expose] public section

open IsLocalRing

universe u v

namespace AlgebraicGeometry

section Defs

variable (B : Type u) [CommRing B] [IsLocalRing B]

/-- `e` is a good coordinate of the local ring `B`: it is the first of three generators of the
maximal ideal satisfying a quadratic relation modulo `𝔪³` whose quadratic form `q` has
`q(0, t₂, t₃)` not a scalar times the square of a linear form. -/
def IsFirstGeneratorOfGoodRelation (e : B) : Prop :=
  ∃ (x : Fin 3 → B) (a : Fin 3 → Fin 3 → B), x 0 = e ∧
    Ideal.span (Set.range x) = maximalIdeal B ∧ (∀ p q, q < p → a p q = 0) ∧
    (∑ p, ∑ q, a p q * (x p * x q)) ∈ maximalIdeal B ^ 3 ∧
    IsGoodCoordinateForm (fun p q => residue B (a p q))

/-- `e` is a special coordinate of the local ring `B`: there are generators `e = x₁, x₂, x₃` of
the maximal ideal with `x₃² + x₁(a x₂² + b x₂x₃ + c x₃²) ∈ 𝔪⁴`. -/
def IsSpecialCoordinate (e : B) : Prop :=
  ∃ (x : Fin 3 → B) (a b c : B), x 0 = e ∧ Ideal.span (Set.range x) = maximalIdeal B ∧
    x 2 * x 2 + x 0 * (a * (x 1 * x 1) + b * (x 1 * x 2) + c * (x 2 * x 2)) ∈
      maximalIdeal B ^ 4

end Defs

/-- Being a scalar times the square of a linear form is invariant under a bijective ring
homomorphism of the coefficients. -/
theorem isScalarSqLinear_map_iff_of_bijective {k k' : Type*} [CommRing k] [CommRing k'] {n : ℕ}
    (f : k →+* k') (hf : Function.Bijective f) (a : Fin n → Fin n → k) :
    IsScalarSqLinear (fun p q => f (a p q)) ↔ IsScalarSqLinear a := by
  constructor
  · rintro ⟨c', l', hdiag, hoff⟩
    obtain ⟨c, rfl⟩ := hf.2 c'
    choose l hl using fun p => hf.2 (l' p)
    refine ⟨c, l, fun p => hf.1 ?_, fun p q hpq => hf.1 ?_⟩
    · simpa only [map_mul, hl] using hdiag p
    · simpa only [map_add, map_mul, map_ofNat, hl] using hoff p q hpq
  · rintro ⟨c, l, hdiag, hoff⟩
    refine ⟨f c, fun p => f (l p), fun p => ?_, fun p q hpq => ?_⟩
    · simp only [hdiag p, map_mul]
    · rw [← map_add, hoff p q hpq]; simp [map_ofNat]

/-- Being a good coordinate form is invariant under a bijective ring homomorphism of the
coefficients. -/
theorem isGoodCoordinateForm_map_iff {k k' : Type*} [CommRing k] [CommRing k'] {n : ℕ}
    (f : k →+* k') (hf : Function.Bijective f) (a : Fin (n + 1) → Fin (n + 1) → k) :
    IsGoodCoordinateForm (fun p q => f (a p q)) ↔ IsGoodCoordinateForm a := by
  unfold IsGoodCoordinateForm restrictFirstVar
  exact not_congr (isScalarSqLinear_map_iff_of_bijective f hf _)

section Transfer

variable {B : Type u} [CommRing B] [IsLocalRing B] {B' : Type v} [CommRing B'] [IsLocalRing B']
  (φ : B →+* B') [IsLocalHom φ] (hmax : Ideal.map φ (maximalIdeal B) = maximalIdeal B')
  (hres : Function.Bijective (ResidueField.map φ))
include hmax hres

omit [IsLocalHom φ] hres in
/-- Three generators of the maximal ideal of `B` map to three generators of the maximal ideal of
`B'`. -/
theorem span_range_map_eq_maximalIdeal {x : Fin 3 → B}
    (hx : Ideal.span (Set.range x) = maximalIdeal B) :
    Ideal.span (Set.range (fun i => φ (x i))) = maximalIdeal B' := by
  rw [← hmax, ← hx, Ideal.map_span, ← Set.range_comp]
  rfl

omit [IsLocalHom φ] hres in
/-- An element of `𝔪_B ^ n` maps into `𝔪_{B'} ^ n`. -/
theorem map_mem_maximalIdeal_pow_of_map_eq {n : ℕ} {r : B} (hr : r ∈ maximalIdeal B ^ n) :
    φ r ∈ maximalIdeal B' ^ n := by
  rw [← hmax, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem φ hr

omit hmax hres in
/-- The residue of `φ r` is the image of the residue of `r` under the induced map of residue
fields. -/
theorem residue_map_apply (r : B) :
    residue B' (φ r) = ResidueField.map φ (residue B r) := by
  rw [ResidueField.map_residue]

/-- A good coordinate is carried along the homomorphism. -/
theorem IsFirstGeneratorOfGoodRelation.map {e : B} (h : IsFirstGeneratorOfGoodRelation B e) :
    IsFirstGeneratorOfGoodRelation B' (φ e) := by
  obtain ⟨x, a, hx0, hspan, hupper, hrel, hgood⟩ := h
  refine ⟨fun i => φ (x i), fun p q => φ (a p q), by simp [hx0],
    span_range_map_eq_maximalIdeal φ hmax hspan, fun p q hpq => by simp [hupper p q hpq], ?_, ?_⟩
  · simpa [map_sum, map_mul] using map_mem_maximalIdeal_pow_of_map_eq φ hmax hrel
  · simp only [residue_map_apply φ]
    exact (isGoodCoordinateForm_map_iff _ hres _).mpr hgood

omit [IsLocalHom φ] hres in
/-- A special coordinate is carried along the homomorphism. -/
theorem IsSpecialCoordinate.map {e : B} (h : IsSpecialCoordinate B e) :
    IsSpecialCoordinate B' (φ e) := by
  obtain ⟨x, a, b, c, hx0, hspan, hrel⟩ := h
  refine ⟨fun i => φ (x i), φ a, φ b, φ c, by simp [hx0],
    span_range_map_eq_maximalIdeal φ hmax hspan, ?_⟩
  simpa [map_add, map_mul] using map_mem_maximalIdeal_pow_of_map_eq φ hmax hrel

/-- Case I is carried along the homomorphism. -/
theorem IsCaseOne.map_of_bijective (h : IsCaseOne B) : IsCaseOne B' := by
  obtain ⟨x, a, hspan, hupper, ⟨p₀, q₀, hpq, hunit⟩, hrel, hcase⟩ := h
  refine ⟨fun i => φ (x i), fun p q => φ (a p q),
    span_range_map_eq_maximalIdeal φ hmax hspan, fun p q hpq => by simp [hupper p q hpq],
    ⟨p₀, q₀, hpq, notMem_maximalIdeal.mpr ((notMem_maximalIdeal.mp hunit).map φ)⟩, ?_, ?_⟩
  · simpa [map_sum, map_mul] using map_mem_maximalIdeal_pow_of_map_eq φ hmax hrel
  · simp only [residue_map_apply φ]
    exact fun h' => hcase ((isScalarSqLinear_map_iff_of_bijective _ hres _).mp h')

end Transfer

end AlgebraicGeometry

end
