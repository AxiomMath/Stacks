module

import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.Separable
import StacksCore.Tactic.StacksAttribute

/-! # Criterion for being a p-th power -/

@[expose] public section

add_to_stacks 09H0 "first part" Polynomial.separable_iff_derivative_ne_zero

open Polynomial AdjoinRoot

/-- **Stacks 031V** (part 2 — the general statement).
Let `K` be a field of characteristic `p > 0`, `L/K` a field extension, and `x ∈ L`.
If `f ∈ K[X]` satisfies
  (a) `x` is a root of `f`,
  (b) `f` is a separable polynomial, and
  (c) every coefficient of `f` is a `p`-th power in `K`,
then `x` is a `p`-th power in `L`. -/
@[stacks 031V "2, without assuming L/K separable"]
theorem Polynomial.Separable.exists_pow_eq_of_coeff {p : ℕ}
    {K L : Type*} [Field K] [CharP K p] [Field L] [Algebra K L] {x : L} {f : Polynomial K}
    (h₁ : f.Separable) (h₂ : f.aeval x = 0) (h₃ : ∀ i, ∃ b : K, b ^ p = f.coeff i) :
    ∃ y, y ^ p = x := by
  by_contra! hx
  have hp : p.Prime := (CharP.char_is_prime_or_zero K p).resolve_right <| fun hp0 ↦ by
    simpa [hp0] using h₃ (f.natDegree + 1)
  have := Fact.mk hp
  have := charP_of_injective_algebraMap' K (A := L) p
  obtain ⟨f, rfl⟩ : f ∈ lifts (frobenius K p) := by simpa [lifts_iff_coeff_lifts, frobenius_def]
  rw [coe_mapRingHom] at h₁ h₂
  rw [separable_map, ← separable_map (algebraMap K L)] at h₁
  have := Fact.mk (X_pow_sub_C_irreducible_of_prime hp hx)
  set y := AdjoinRoot.root (X ^ p - C x)
  have := charP_of_injective_algebraMap' L (A := AdjoinRoot (X ^ p - C x)) p
  have hyx : y ^ p = x := by
    have := eval₂_root (X ^ p - C x)
    simpa [eval₂_sub, sub_eq_zero]
  have hmy : minpoly L y = X ^ p - C x := by
    simp [y, minpoly_root (X_pow_sub_C_ne_zero hp.pos _), leadingCoeff_X_pow_sub_C hp.pos]
  have hfy : f.aeval y = 0 := eq_zero_of_pow_eq_zero (n := p) <| by
    rw [← frobenius_def p (f.aeval y),
      map_aeval_eq_aeval_map (φ := frobenius K p) (by ext; simp [frobenius_def]),
      frobenius_def, hyx, ← coe_ofAlgHom (S := K), aeval_algHom, AlgHom.comp_apply, h₂, map_zero]
  have hdvd : X ^ p - C x ∣ f.map (algebraMap K L) :=
    hmy ▸ minpoly.dvd _ _ (by simpa [aeval_map_algebraMap])
  replace h₁ := h₁.of_dvd hdvd
  have hx0 : x ≠ 0 := fun hx0 ↦ hx 0 (by simp [hx0, hp.ne_zero])
  rw [X_pow_sub_C_separable_iff hp.pos hx0] at h₁
  exact h₁ (CharP.cast_eq_zero _ _)

/-- Specialisation of `Polynomial.Separable.exists_pow_eq_of_coeff` to the minimal polynomial:
let `K` be a field of characteristic `p > 0` and `L/K` a field extension. If `x ∈ L` is
separable over `K` and every coefficient of the minimal polynomial of `x` over `K` is a
`p`-th power in `K`, then `x` is a `p`-th power in `L`. -/
theorem IsSeparable.exists_pow_eq_of_minpoly_coeff {p : ℕ}
    {K : Type*} [Field K] [CharP K p] {L : Type*} [Field L] [Algebra K L]
    {x : L} (h₁ : IsSeparable K x) (h₂ : ∀ i, ∃ b : K, b ^ p = (minpoly K x).coeff i) :
    ∃ y, y ^ p = x :=
  h₁.exists_pow_eq_of_coeff (minpoly.aeval _ _) h₂

/-- **Stacks 031V** (part 1).
Let `K` be a field of characteristic `p > 0`, `L/K` a separable extension, and `x ∈ L`.
If every coefficient of the minimal polynomial of `x` over `K` is a `p`-th power in `K`,
then `x` is a `p`-th power in `L`. -/
@[stacks 031V "1"]
theorem exists_pow_eq_of_minpoly_coeff_of_separable {p : ℕ}
    {K : Type*} [Field K] [CharP K p] {L : Type*} [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    {x : L} (h₁ : ∀ i, ∃ b : K, b ^ p = (minpoly K x).coeff i) :
    ∃ y, y ^ p = x :=
  (Algebra.IsSeparable.isSeparable K x).exists_pow_eq_of_minpoly_coeff h₁

/-- **Stacks 09H0** (second part).
If a field `K` admits an irreducible polynomial that is not separable, then `K` has prime
characteristic: there is a prime `p` with `CharP K p`. -/
@[stacks 09H0 "second part"]
theorem charP_prime_of_not_separable
    {K : Type*} [Field K] {f : K[X]} (hfi : Irreducible f) (hfs : ¬f.Separable) :
    ∃ p, p.Prime ∧ CharP K p := by
  suffices ¬CharZero K by grind [CharP.exists', Fact.out]
  rintro _
  exact hfs hfi.separable

namespace IsSeparable

/-- An element of `S` in the image of `algebraMap R S` is separable over `R`. -/
@[simp]
theorem algebraMap {R : Type*} (S : Type*) [CommRing R] [Ring S] [Algebra R S] (r : R) :
    IsSeparable R (algebraMap R S r) := by
  have hm : (minpoly R (Algebra.algebraMap R S r)).Monic := minpoly.monic isIntegral_algebraMap
  have h := minpoly.min R (Algebra.algebraMap R S r) (monic_X_sub_C r) (by simp)
  replace h : _ ≤ 1 := natDegree_le_of_degree_le <| h.trans (degree_X_sub_C_le r)
  rw [Nat.le_one_iff_eq_zero_or_eq_one] at h
  unfold IsSeparable
  obtain h | h := h
  · rw [eq_one_of_monic_natDegree_zero hm h]
    exact separable_one
  · rw [hm.eq_X_add_C h]
    exact separable_X_add_C _

/-- `0` is separable over `R`. -/
@[simp]
theorem zero (R S : Type*) [CommRing R] [Ring S] [Algebra R S] : IsSeparable R (0 : S) := by
  convert algebraMap S (0 : R); simp

/-- `1` is separable over `R`. -/
@[simp]
theorem one (R S : Type*) [CommRing R] [Ring S] [Algebra R S] : IsSeparable R (1 : S) := by
  convert algebraMap S (1 : R); simp

/-- If `S` is a subsingleton, every element is separable over `R`. -/
@[simp]
theorem of_subsingleton (R : Type*) {S : Type*} [CommRing R] [Ring S] [Algebra R S]
    [Subsingleton S] (x : S) : IsSeparable R x := by simp [Subsingleton.elim x 0]

/-- If `R` is a subsingleton, every element of `S` is separable over `R`. -/
@[simp]
theorem of_subsingleton' (R : Type*) {S : Type*} [CommRing R] [Ring S] [Algebra R S]
    [Subsingleton R] (x : S) : IsSeparable R x := by
  have := MulActionWithZero.subsingleton R S
  simp [Subsingleton.elim x 0]

/-- Adding an element of the base field to a separable element yields a separable element. -/
@[simp]
theorem add_algebraMap {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    {x : A} (hx : IsSeparable K x) (b : K) : IsSeparable K (x + Algebra.algebraMap K A b) := by
  rw [IsSeparable, Separable] at hx
  convert hx.map (Polynomial.compRingHom (X - C b))
  simp [IsSeparable, minpoly.add_algebraMap, Separable, derivative_comp]

end IsSeparable

/-- The image of an `F`-algebra map `f : K →ₐ[F] L` from a separable extension `K/F` is
itself separable over `F`. -/
instance (F K L : Type*) [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
    [Algebra.IsSeparable F K] (f : K →ₐ[F] L) : Algebra.IsSeparable F f.fieldRange :=
  AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField f)
