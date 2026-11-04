module

public import StacksFrontier.RingTheory.Blowup.Defs

@[expose] public section

/-!
# The affine blowup algebra as a quotient of a polynomial algebra

Let `R` be a ring, let `a : R`, let `b : ι → R` and let `I = (a, bᵢ : i ∈ ι)`.  Let `Rₐ` be
the localization of `R` at `a` and let `φ : R[xᵢ : i ∈ ι] → Rₐ` be the `R`-algebra map with
`φ xᵢ · a = bᵢ`.  This file proves that the range of `φ` is the affine blowup algebra
`R[I/a] = {x/aⁿ : x ∈ Iⁿ}` and that `φ f = 0` exactly when `aⁿ f` lies in the ideal of
relations `J = (a xᵢ - bᵢ : i ∈ ι)` for some `n`.

The whole proof rests on one congruence: `a xᵢ ≡ bᵢ (mod J)`, so that for every polynomial `f`
there are `d : ℕ` and `g ∈ I ^ d` with `aᵈ f ≡ g (mod J)`.  Both halves of the statement follow
from it, because `a` is a unit in `Rₐ`:

* `φ` kills `J`, so the congruence reads `φ f · aᵈ = g` in `Rₐ`; with `g ∈ Iᵈ` this puts the
  range of `φ` inside `R[I/a]`, and `aⁿ f ∈ J` forces `aⁿ · φ f = 0`, hence `φ f = 0`;
* if `φ f = 0` then `g` dies in `Rₐ`, so `aᴺ g = 0` in `R` for some `N`, and multiplying the
  congruence by `aᴺ` puts `a^{N+d} f` in `J`;
* the other inclusion of ranges holds because `x/a` lies in the range of `φ` for every `x ∈ I`,
  and an element of `Iⁿ` is a sum of products of `n` elements of `I`.

## Main results

* `Stacks.Blowup.PolynomialPresentation.solution`: Stacks 0G8S, as stated in
  `Ideal.range_eq_affineBlowup_and_ker_eq_saturation`.

## Implementation notes

The source proves 0G8S by base change along `ℤ[t₁, …, t_n] → R` (Example 0G8R together with
Lemma 0BIP).  Neither is used here: inside `Rₐ` the element `a` is invertible, which is the
only thing the base-change argument buys, so the congruence above proves the lemma over `R`
directly.  Finiteness of the index type is never needed.

## References

* [StackProject 0G8S](https://stacks.math.columbia.edu/tag/0G8S)
-/

namespace Stacks.Blowup.PolynomialPresentation

open MvPolynomial

section Congruence

variable {R : Type*} [CommRing R] {ι : Type*} {a : R} {b : ι → R} {I : Ideal R}
  {f : MvPolynomial ι R} {g : R} {d : ℕ}

/-- Multiplying a congruence `aᵈ f ≡ g (mod a xᵢ - bᵢ)` by `aᵏ` gives `a^{k+d} f ≡ aᵏ g`. -/
private theorem C_pow_add_mul_sub_C_mem_span_of_mem_span (k : ℕ)
    (h : C a ^ d * f - C g ∈ Ideal.span (Set.range fun i ↦ C a * X i - C (b i))) :
    C a ^ (k + d) * f - C (a ^ k * g) ∈ Ideal.span (Set.range fun i ↦ C a * X i - C (b i)) := by
  have key : C a ^ (k + d) * f - C (a ^ k * g) = C a ^ k * (C a ^ d * f - C g) := by
    rw [map_mul, map_pow]; ring
  rw [key]
  exact Ideal.mul_mem_left _ _ h

/-- A congruence `aᵈ f ≡ g (mod a xᵢ - bᵢ)` with `g ∈ Iᵈ` can be raised to any higher power of
`a`, by multiplying it by `a^{e-d}`. -/
private theorem exists_mem_pow_and_C_pow_mul_sub_C_mem_span_of_le (ha : a ∈ I) {e : ℕ}
    (hde : d ≤ e) (hg : g ∈ I ^ d)
    (h : C a ^ d * f - C g ∈ Ideal.span (Set.range fun i ↦ C a * X i - C (b i))) :
    ∃ g' ∈ I ^ e, C a ^ e * f - C g' ∈ Ideal.span (Set.range fun i ↦ C a * X i - C (b i)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hde
  exact ⟨a ^ k * g, pow_add I k d ▸ Ideal.mul_mem_mul (Ideal.pow_mem_pow ha k) hg,
    C_pow_add_mul_sub_C_mem_span_of_mem_span k h⟩

/-- Every polynomial becomes a constant after multiplication by a power of `a`, modulo the
relations `a xᵢ - bᵢ`, and the constant can be taken in the corresponding power of an ideal `I`
containing `a` and the `bᵢ`.  This is the congruence `a xᵢ ≡ bᵢ`, applied once for each variable
in each monomial of `f`. -/
private theorem exists_mem_pow_and_C_pow_mul_sub_C_mem_span (ha : a ∈ I) (hb : ∀ i, b i ∈ I)
    (f : MvPolynomial ι R) :
    ∃ d : ℕ, ∃ g ∈ I ^ d,
      C a ^ d * f - C g ∈ Ideal.span (Set.range fun i ↦ C a * X i - C (b i)) := by
  induction f using MvPolynomial.induction_on with
  | C r => exact ⟨0, r, by simp, by simp⟩
  | add p q hp hq =>
    obtain ⟨d₁, g₁, hg₁, h₁⟩ := hp
    obtain ⟨d₂, g₂, hg₂, h₂⟩ := hq
    obtain ⟨g₁, hg₁, h₁⟩ :=
      exists_mem_pow_and_C_pow_mul_sub_C_mem_span_of_le ha (le_max_left d₁ d₂) hg₁ h₁
    obtain ⟨g₂, hg₂, h₂⟩ :=
      exists_mem_pow_and_C_pow_mul_sub_C_mem_span_of_le ha (le_max_right d₁ d₂) hg₂ h₂
    refine ⟨max d₁ d₂, g₁ + g₂, add_mem hg₁ hg₂, ?_⟩
    have key : C a ^ max d₁ d₂ * (p + q) - C (g₁ + g₂)
        = C a ^ max d₁ d₂ * p - C g₁ + (C a ^ max d₁ d₂ * q - C g₂) := by rw [map_add]; ring
    rw [key]
    exact add_mem h₁ h₂
  | mul_X p i hp =>
    obtain ⟨d, g, hg, h⟩ := hp
    refine ⟨d + 1, g * b i, by rw [pow_succ]; exact Ideal.mul_mem_mul hg (hb i), ?_⟩
    have key : C a ^ (d + 1) * (p * X i) - C (g * b i)
        = C a ^ d * p * (C a * X i - C (b i)) + (C a ^ d * p - C g) * C (b i) := by
      rw [map_mul]; ring
    rw [key]
    exact add_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))
      (Ideal.mul_mem_right _ _ h)

/-- A congruence `aᵈ f ≡ g` whose constant is killed by `aᴺ` says that `a^{N+d} f` is itself a
relation. -/
private theorem smul_mem_span_of_mul_eq_zero {N : ℕ}
    (h : C a ^ d * f - C g ∈ Ideal.span (Set.range fun i ↦ C a * X i - C (b i)))
    (hN : a ^ N * g = 0) :
    a ^ (N + d) • f ∈ Ideal.span (Set.range fun i ↦ C a * X i - C (b i)) := by
  have hm := C_pow_add_mul_sub_C_mem_span_of_mem_span N h
  rwa [hN, map_zero, sub_zero, ← map_pow, ← MvPolynomial.smul_eq_C_mul] at hm

end Congruence

section Localization

variable {R : Type*} [CommRing R] {ι : Type*} {Rₐ : Type*} [CommRing Rₐ] [Algebra R Rₐ]
  {a : R} {b : ι → R} (φ : MvPolynomial ι R →ₐ[R] Rₐ)
  (hφ : ∀ i, φ (X i) * algebraMap R Rₐ a = algebraMap R Rₐ (b i))

include hφ

/-- The relations `a xᵢ - bᵢ` are in the kernel of `φ`. -/
private theorem span_le_ker : Ideal.span (Set.range fun i ↦ C a * X i - C (b i)) ≤
    RingHom.ker (φ : MvPolynomial ι R →+* Rₐ) := by
  rw [Ideal.span_le]
  rintro p ⟨i, rfl⟩
  simp only [SetLike.mem_coe, RingHom.mem_ker, RingHom.coe_coe, map_sub, map_mul,
    MvPolynomial.algHom_C, mul_comm (algebraMap R Rₐ a), hφ i, sub_self]

/-- A congruence `aᵈ f ≡ g (mod a xᵢ - bᵢ)` read in `Rₐ`, where the relations die: the fraction
`φ f` is `g/aᵈ`. -/
private theorem apply_mul_pow_eq_algebraMap {f : MvPolynomial ι R} {g : R} {d : ℕ}
    (h : C a ^ d * f - C g ∈ Ideal.span (Set.range fun i ↦ C a * X i - C (b i))) :
    φ f * algebraMap R Rₐ a ^ d = algebraMap R Rₐ g := by
  have h0 : φ (C a ^ d * f - C g) = 0 := span_le_ker φ hφ h
  rw [map_sub, map_mul, map_pow, MvPolynomial.algHom_C, MvPolynomial.algHom_C, sub_eq_zero] at h0
  rw [mul_comm]
  exact h0

/-- Every element of `I = (a, bᵢ)`, divided by `a`, is in the range of `φ`: this is clear for the
generators, since `a/a = φ 1` and `bᵢ/a = φ xᵢ`. -/
private theorem exists_apply_mul_eq_algebraMap_of_mem {x : R}
    (hx : x ∈ Ideal.span (insert a (Set.range b))) :
    ∃ f : MvPolynomial ι R, φ f * algebraMap R Rₐ a = algebraMap R Rₐ x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain rfl | ⟨i, rfl⟩ := hx
    · exact ⟨1, by simp⟩
    · exact ⟨X i, hφ i⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨f₁, h₁⟩ := hx
    obtain ⟨f₂, h₂⟩ := hy
    exact ⟨f₁ + f₂, by rw [map_add, add_mul, h₁, h₂, map_add]⟩
  | smul r x _ hx =>
    obtain ⟨f, h⟩ := hx
    exact ⟨C r * f, by rw [map_mul, MvPolynomial.algHom_C, mul_assoc, h, smul_eq_mul, map_mul]⟩

/-- Every element of `Iⁿ`, divided by `aⁿ`, is in the range of `φ`: an element of `Iⁿ` is a sum
of products of `n` elements of `I`, and each factor contributes one power of `a`. -/
private theorem exists_apply_mul_pow_eq_algebraMap_of_mem_pow (n : ℕ) :
    ∀ x ∈ Ideal.span (insert a (Set.range b)) ^ n,
      ∃ f : MvPolynomial ι R, φ f * algebraMap R Rₐ a ^ n = algebraMap R Rₐ x := by
  induction n with
  | zero => exact fun x _ ↦ ⟨C x, by simp [MvPolynomial.algHom_C]⟩
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun y hy z hz ↦ ?_) fun y z hy hz ↦ ?_
    · obtain ⟨f₁, h₁⟩ := ih y hy
      obtain ⟨f₂, h₂⟩ := exists_apply_mul_eq_algebraMap_of_mem φ hφ hz
      exact ⟨f₁ * f₂, by rw [map_mul, map_mul, ← h₁, ← h₂, pow_succ]; ring⟩
    · obtain ⟨f₁, h₁⟩ := hy
      obtain ⟨f₂, h₂⟩ := hz
      exact ⟨f₁ + f₂, by rw [map_add, add_mul, h₁, h₂, map_add]⟩

end Localization

open MvPolynomial in
public theorem solution
    {R : Type*} [CommRing R] {ι : Type*} {Rₐ : Type*} [CommRing Rₐ] [Algebra R Rₐ]
    {a : R} {b : ι → R} {I : Ideal R} [IsLocalization.Away a Rₐ]
    (hI : I = Ideal.span (insert a (Set.range b)))
    (φ : MvPolynomial ι R →ₐ[R] Rₐ)
    (hφ : ∀ i, φ (X i) * algebraMap R Rₐ a = algebraMap R Rₐ (b i)) :
    Set.range φ =
        {y : Rₐ | ∃ n : ℕ, ∃ x ∈ I ^ n, y * algebraMap R Rₐ a ^ n = algebraMap R Rₐ x} ∧
      ∀ f : MvPolynomial ι R, φ f = 0 ↔
        ∃ n : ℕ, a ^ n • f ∈ Ideal.span (Set.range fun i ↦ C a * X i - C (b i)) := by
  subst hI
  have ha : a ∈ Ideal.span (insert a (Set.range b)) := Ideal.subset_span (Set.mem_insert _ _)
  have hb : ∀ i, b i ∈ Ideal.span (insert a (Set.range b)) := fun i ↦
    Ideal.subset_span (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
  have hA : IsUnit (algebraMap R Rₐ a) := IsLocalization.Away.algebraMap_isUnit a
  refine ⟨Set.ext fun y ↦ ⟨?_, ?_⟩, fun f ↦ ⟨fun hf ↦ ?_, fun ⟨n, hn⟩ ↦ ?_⟩⟩
  · rintro ⟨f, rfl⟩
    obtain ⟨d, g, hg, h⟩ := exists_mem_pow_and_C_pow_mul_sub_C_mem_span ha hb f
    exact ⟨d, g, hg, apply_mul_pow_eq_algebraMap φ hφ h⟩
  · rintro ⟨n, x, hx, hy⟩
    obtain ⟨f, hf⟩ := exists_apply_mul_pow_eq_algebraMap_of_mem_pow φ hφ n x hx
    exact ⟨f, (hA.pow n).mul_right_cancel (hf.trans hy.symm)⟩
  · obtain ⟨d, g, -, h⟩ := exists_mem_pow_and_C_pow_mul_sub_C_mem_span ha hb f
    have hg : algebraMap R Rₐ g = 0 := by
      rw [← apply_mul_pow_eq_algebraMap φ hφ h, hf, zero_mul]
    obtain ⟨N, hN⟩ := IsLocalization.Away.exists_of_eq (x := a) (hg.trans (map_zero _).symm)
    exact ⟨N + d, smul_mem_span_of_mul_eq_zero h (by simpa using hN)⟩
  · have h0 : φ (a ^ n • f) = 0 := span_le_ker φ hφ hn
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.algHom_C, map_pow] at h0
    exact ((hA.pow n).mul_right_eq_zero).1 h0

end Stacks.Blowup.PolynomialPresentation

/-!
# The affine blowup algebra as a quotient of a polynomial algebra

Let `R` be a ring, let `b : ι → R` be a family of elements, let `a : R`, and let
`I = (a, bᵢ : i ∈ ι)` be the ideal they generate.  The affine blowup algebra
`R[I/a]` is the subring `{x/aⁿ : n ∈ ℕ, x ∈ Iⁿ}` of the localization `Rₐ` of `R`
at `a`.

The `R`-algebra map `φ : R[xᵢ : i ∈ ι] → Rₐ` determined by `φ xᵢ = bᵢ/a` has image
exactly `R[I/a]`, and `φ f = 0` holds if and only if `aⁿ f` lies in the ideal of
relations `(a xᵢ - bᵢ : i ∈ ι)` for some `n`.  Equivalently, `φ` induces a
surjection `R[xᵢ : i ∈ ι]/(a xᵢ - bᵢ : i ∈ ι) → R[I/a]` whose kernel is the
`a`-power torsion of the source.

## Main results

* `Ideal.range_eq_affineBlowup_and_ker_eq_saturation`: the two assertions above,
  for every `R`-algebra map `φ` with `φ xᵢ · a = bᵢ`.

## Implementation notes

The affine blowup algebra is spelled by the description that follows its
definition in the source: an element of `R[I/a]` is `x/aⁿ` with `x ∈ Iⁿ`, and
`x/aⁿ = y/aᵐ` exactly when `aᵏ(aᵐx - aⁿy) = 0` for some `k`.  That is precisely
equality in the localization `Rₐ` of `R` at `a`, so `R[I/a]` is the subset
`{y : Rₐ | ∃ n, ∃ x ∈ Iⁿ, y · aⁿ = x}` of `Rₐ`, and the surjection of the source
is the assertion that this subset is the range of `φ`.  The localization is taken
abstractly, as any `Rₐ` with `IsLocalization.Away a Rₐ`.

The conclusion about the kernel is stated on the polynomial algebra rather than on
the quotient `R[xᵢ]/(a xᵢ - bᵢ)`: `φ f = 0 ↔ ∃ n, aⁿ • f ∈ (a xᵢ - bᵢ)`.  Taking
`n = 0` gives `(a xᵢ - bᵢ) ≤ ker φ`, so this says exactly that the induced map on
the quotient has kernel the `a`-power torsion, which is the form the source
states.

The map is not merely asserted to exist: the conclusion is proved for *every*
`R`-algebra map `φ` with `φ xᵢ · a = bᵢ` for all `i`, and there is only one, since
`a` is invertible in `Rₐ` and `R[xᵢ : i ∈ ι]` is free on the `xᵢ`; concretely
`φ = MvPolynomial.aeval fun i ↦ IsLocalization.mk' Rₐ (b i) ⟨a, Submonoid.mem_powers a⟩`.
Both the base `R` and the scalars are the source's: `φ` is `R`-linear and `Rₐ` is
viewed as an `R`-algebra.

The generating family is an arbitrary indexed family `b : ι → R` rather than a
finite list `a₂, …, a_n`, and the source's distinguished generator `a = a₁` is a
separate argument; finiteness of `ι` is used nowhere.  Both hypotheses are used by
the conclusion: `hI` pins the ideal `I` occurring in the description of `R[I/a]`,
and `hφ` pins `φ`.  A nondegenerate instance: `R = ℤ`, `ι = Unit`, `a = 2`,
`b = 3`, where `I = (2, 3) = ℤ`, the source is `ℤ[x]/(2x - 3) ≃ ℤ[1/2]`, the
target is `ℤ[I/2] = ℤ[1/2]`, and the kernel is zero.

## References

* [StackProject 0G8S](https://stacks.math.columbia.edu/tag/0G8S)
-/

open MvPolynomial in
/-- **Stacks 0G8S.** Let `R` be a ring, let `I = (a, bᵢ : i ∈ ι)` be an ideal of
`R` generated by `a` together with a family `b : ι → R`, and let `Rₐ` be the
localization of `R` at `a`.  Let `φ : R[xᵢ : i ∈ ι] → Rₐ` be the `R`-algebra map
with `φ xᵢ = bᵢ/a`.  Then the range of `φ` is the affine blowup algebra
`R[I/a] = {x/aⁿ : x ∈ Iⁿ}`, and `φ f = 0` if and only if `aⁿ f` lies in the ideal
of relations `(a xᵢ - bᵢ)` for some `n`; that is, `φ` induces a surjection
`R[xᵢ]/(a xᵢ - bᵢ) → R[I/a]` whose kernel is the `a`-power torsion of the
source. -/
@[stacks 0G8S]
public theorem Ideal.range_eq_affineBlowup_and_ker_eq_saturation
    {R : Type*} [CommRing R] {ι : Type*} {Rₐ : Type*} [CommRing Rₐ] [Algebra R Rₐ]
    {a : R} {b : ι → R} {I : Ideal R} [IsLocalization.Away a Rₐ]
    (hI : I = Ideal.span (insert a (Set.range b)))
    (φ : MvPolynomial ι R →ₐ[R] Rₐ)
    (hφ : ∀ i, φ (X i) * algebraMap R Rₐ a = algebraMap R Rₐ (b i)) :
    Set.range φ =
        {y : Rₐ | ∃ n : ℕ, ∃ x ∈ I ^ n, y * algebraMap R Rₐ a ^ n = algebraMap R Rₐ x} ∧
      ∀ f : MvPolynomial ι R, φ f = 0 ↔
        ∃ n : ℕ, a ^ n • f ∈ Ideal.span (Set.range fun i ↦ C a * X i - C (b i)) :=
    by exact Stacks.Blowup.PolynomialPresentation.solution hI φ hφ

/-!
# Adding a principal component to an affine blowup algebra: surjectivity

Let `R` be a ring, `I ⊆ R` an ideal and `a f : R`. Let `A` be a localization of `R` away from `a`
and let `B` be a localization of `R` away from `f * a`, an `A`-algebra over `R`; the canonical
`R`-algebra map `A → B` is `IsScalarTower.toAlgHom R A B`. This file proves that this map carries
the affine blowup algebra `R[I/a] ⊆ A` onto `R[fI/(fa)] ⊆ B`.

Both blowup algebras are `Algebra.adjoin R` of their fractions with a single denominator, so
`AlgHom.map_adjoin` reduces the statement to the equality of those two generating sets, which is
`image_setOf_mk'_mem`. That equality is the source's formula `y/a = (f y)/(f a)`, proved as
`algebraMap_mk'_eq_mk'_mul` and used in both directions: the image of the generator `y/a`, `y ∈ I`,
is the generator `(f y)/(f a)` of the target, and every generator of the target has this shape
because every element of `fI` is a product `f x` with `x ∈ I`.

## Main results

* `Stacks.Blowup.PrincipalComponent.solution`: Stacks 0BBI, surjectivity, as stated in
  `IsLocalization.Away.map_affineBlowupAlgebra`.

## Implementation notes

The source deduces surjectivity from the description of `R''` as the ring of fractions
`x/(fa)ⁿ`, `x ∈ (fI)ⁿ`, which needs `a ∈ I` and, for the kernel half of the lemma, that `fa` is a
nonzerodivisor in `R''` (Lemma 07Z3). Neither is used here: with both algebras presented as
`Algebra.adjoin R` of their degree-one fractions, the image is computed generator by generator, so
no relation between `a`, `f` and `I` is needed and `a ∈ I` is absent from the statement.

The formula `y/a = (f y)/(f a)` is about the two localizations alone, so it is stated over
commutative semirings, the generality of Mathlib's `IsLocalization` API; only the passage to the
blowup algebras, which are subalgebras cut out by an ideal, works over a commutative ring.

## References

* [Stacks project, Tag 0BBI](https://stacks.math.columbia.edu/tag/0BBI), with Definition 052Q for
  the affine blowup algebra.
-/

namespace Stacks.Blowup.PrincipalComponent

open IsLocalization

section Fraction

variable {R : Type*} [CommSemiring R] (a f : R) (A : Type*) [CommSemiring A] [Algebra R A]
  [IsLocalization.Away a A] (B : Type*) [CommSemiring B] [Algebra R B] [Algebra A B]
  [IsScalarTower R A B] [IsLocalization.Away (f * a) B]

/-- The formula `y/a = (f y)/(f a)` of the source, read in a localization `B` of `R` away from
`f * a`: the canonical map from a localization `A` of `R` away from `a` to `B` sends the fraction
`y/a` to `(f y)/(f a)`. -/
private theorem algebraMap_mk'_eq_mk'_mul (y : R) :
    algebraMap A B (mk' A y ⟨a, Submonoid.mem_powers a⟩) =
      mk' B (f * y) ⟨f * a, Submonoid.mem_powers (f * a)⟩ := by
  have hB : algebraMap A B (mk' A y ⟨a, Submonoid.mem_powers a⟩) * algebraMap R B a
      = algebraMap R B y := by
    rw [IsScalarTower.algebraMap_apply R A B, ← map_mul, mk'_spec,
      ← IsScalarTower.algebraMap_apply]
  rw [eq_mk'_iff_mul_eq, map_mul, map_mul, mul_left_comm, hB]

end Fraction

section Blowup

variable {R : Type*} [CommRing R] (I : Ideal R) (a f : R) (A : Type*) [CommRing A] [Algebra R A]
  [IsLocalization.Away a A] (B : Type*) [CommRing B] [Algebra R B] [Algebra A B]
  [IsScalarTower R A B] [IsLocalization.Away (f * a) B]

/-- The canonical `R`-algebra map `A → B` carries the fractions `y/a`, `y ∈ I`, which generate
`R[I/a]`, onto the fractions `z/(fa)`, `z ∈ fI`, which generate `R[fI/(fa)]`: forwards because
`y/a = (f y)/(f a)` with `f y ∈ fI`, backwards because every `z ∈ fI` is a product `f x` with
`x ∈ I`, so that `z/(fa)` is the image of `x/a`. -/
private theorem image_setOf_mk'_mem :
    IsScalarTower.toAlgHom R A B ''
        {z : A | ∃ y ∈ I, z = mk' A y ⟨a, Submonoid.mem_powers a⟩} =
      {z : B | ∃ y ∈ Ideal.span {f} * I, z = mk' B y ⟨f * a, Submonoid.mem_powers (f * a)⟩} := by
  ext z
  simp only [Set.mem_image, IsScalarTower.coe_toAlgHom']
  constructor
  · rintro ⟨-, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨f * y, Ideal.mul_mem_mul (Ideal.mem_span_singleton_self f) hy,
      algebraMap_mk'_eq_mk'_mul a f A B y⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := Ideal.mem_span_singleton_mul.mp hy
    exact ⟨_, ⟨x, hx, rfl⟩, algebraMap_mk'_eq_mk'_mul a f A B x⟩

/-- **Stacks 0BBI**, surjectivity. Let `R` be a ring, `I ⊆ R` an ideal and `a f : R`. The canonical
`R`-algebra map from a localization `A` of `R` away from `a` to a localization `B` of `R` away from
`f * a` maps the affine blowup algebra `R[I/a] ⊆ A` onto the affine blowup algebra
`R[fI/(fa)] ⊆ B`. -/
public theorem solution :
    (affineBlowupAlgebra I a A).map (IsScalarTower.toAlgHom R A B) =
      affineBlowupAlgebra (Ideal.span {f} * I) (f * a) B := by
  rw [affineBlowupAlgebra, affineBlowupAlgebra, AlgHom.map_adjoin, image_setOf_mk'_mem I a f A B]

end Blowup

end Stacks.Blowup.PrincipalComponent

/-!
# Adding a principal component to an affine blowup algebra

Let `R` be a ring, `I ⊆ R` an ideal, `a ∈ I` and `f ∈ R`, and write `R' = R[I/a]` and
`R'' = R[fI/(fa)]` for the affine blowup algebras of `(I, a)` and of `(fI, f * a)`. In the form
`affineBlowupAlgebra` gives them, `R'` is the `R`-subalgebra of a localization `A` of `R` away from
`a` generated by the fractions `x/a` with `x ∈ I`, and `R''` is the `R`-subalgebra of a localization
`B` of `R` away from `f * a` generated by the fractions `x/(f * a)` with `x ∈ fI`.

Since `x/a = (f * x)/(f * a)`, the map `x/aⁿ ↦ fⁿx/(fa)ⁿ` of the source is the restriction to `R'`
of the canonical `R`-algebra map `A → B`. This file states that this map carries `R'` onto `R''`,
and that it kills exactly the `f`-power torsion, so that `R''` is `R'` modulo its `f`-power torsion.

The second assertion is about the localization `A → B` alone, not about blowup algebras: when `B`
is a localization of `A` away from the image of `f`, an element of `A` dies in `B` exactly when
some power of `f` kills it. The kernel of `R' → R''` is that description restricted to `R'`,
because the `f`-power torsion of the subalgebra `R'` is its intersection with the `f`-power torsion
of `A`.

## Main results

* `IsLocalization.Away.map_affineBlowupAlgebra`: the canonical `R`-algebra map `A → B` from a
  localization of `R` away from `a` to a localization of `R` away from `f * a` maps `R[I/a]` onto
  `R[fI/(fa)]`.
* `IsLocalization.Away.map_eq_zero_iff`: an element of `A` maps to `0` in a localization of `A`
  away from the image of `f` if and only if some power of `f` kills it.

## Implementation notes

* The two assertions are independent — one computes an image, the other a kernel, and the kernel
  computation involves neither `I` nor `a` — so they are two statements rather than a conjunction,
  each with the hypotheses it uses.
* The source's hypothesis `a ∈ I` is used by neither, so it is dropped: `affineBlowupAlgebra I a A`
  is defined for every `a : R`, and since `a/a = 1` lies in every `R`-subalgebra it is the affine
  blowup algebra of `(I + (a), a)`, while `affineBlowupAlgebra (fI) (f * a) B` is that of
  `(fI + (fa), f * a)`; as `f(I + (a)) = fI + (fa)`, for `a ∈ I` the two are the source's `R'` and
  `R''`.
* The kernel is described for every `y : A`, not only for `y ∈ R'`: membership is unused, and the
  general statement is the one the source's assertion about `R'` specializes to. For the same
  reason it is stated over commutative semirings, the generality of Mathlib's `IsLocalization` API
  and of `IsLocalization.map_eq_zero_iff`, which it specializes to the powers of `f`; the image is
  stated over commutative rings, as `affineBlowupAlgebra` is.
* The kernel statement asks of `B` only that it be an `A`-algebra localizing `A` away from the
  image of `f`: neither an `R`-algebra structure on `B` nor a tower is needed, since `f ^ n • y` is
  computed in `A` and the map is `algebraMap A B`. The image statement instead needs `B` to be a
  localization of `R` away from `f * a`, which is what names `R''`, together with the tower making
  `A → B` an `R`-algebra map. For the source's `B = (R_a)_f` both hypotheses hold, the localization
  of `R` away from `f * a` by `IsLocalization.Away.mul A B a f`.
* The base of the image statement is the source's `R`: the two blowup algebras are `R`-subalgebras
  and the map is the `R`-algebra map `IsScalarTower.toAlgHom R A B`, which is `algebraMap A B`, not
  an `A`-algebra map. It is pinned rather than asserted to exist: the content is that this one
  canonical map has image `R''`.
* `A` and `B` are arbitrary localizations rather than `Localization.Away a` and
  `Localization.Away (f * a)`, so the statements apply to every model of `Rₐ` and of `R_(f * a)`.
* Neither assertion is vacuous: for `R = ℤ[s, t]`, `I = (s, t)`, `a = s` and `f = t` one has
  `R[I/a] = ℤ[s, t/s]` and the map is injective, while for `R = ℤ/9`, `I = R`, `a = 1` and `f = 3`
  the ring `B` is zero and the kernel is all of `R[I/a] = ℤ/9`.

## References

* [Stacks project, Tag 0BBI](https://stacks.math.columbia.edu/tag/0BBI), with Definition 052Q for
  the affine blowup algebra.
-/

/-- **Stacks 0BBI**, surjectivity. Let `R` be a ring, `I ⊆ R` an ideal and `a f : R`. The canonical
`R`-algebra map from a localization `A` of `R` away from `a` to a localization `B` of `R` away from
`f * a` maps the affine blowup algebra `R[I/a] ⊆ A` onto the affine blowup algebra
`R[fI/(fa)] ⊆ B`. -/
@[stacks 0BBI]
public theorem IsLocalization.Away.map_affineBlowupAlgebra {R : Type*} [CommRing R]
    (I : Ideal R) (a f : R) (A : Type*) [CommRing A] [Algebra R A] [IsLocalization.Away a A]
    (B : Type*) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [IsLocalization.Away (f * a) B] :
    (affineBlowupAlgebra I a A).map (IsScalarTower.toAlgHom R A B) =
      affineBlowupAlgebra (Ideal.span {f} * I) (f * a) B :=
    by apply Stacks.Blowup.PrincipalComponent.solution

/-- **Stacks 0BBI**, the kernel. Let `A` be an algebra over a commutative semiring `R`, let `f : R`
and let `B` be a localization of `A` away from the image of `f`. Then `y : A` maps to `0` in `B` if
and only if `y` is `f`-power torsion. Restricted to the affine blowup algebra `R[I/a] ⊆ A` this
describes the kernel of the map `R[I/a] → R[fI/(fa)]` of
`IsLocalization.Away.map_affineBlowupAlgebra`. -/
@[stacks 0BBI]
public theorem IsLocalization.Away.map_eq_zero_iff {R : Type*} [CommSemiring R] {A : Type*}
    [CommSemiring A] [Algebra R A] {B : Type*} [CommSemiring B] [Algebra A B]
    (f : R) [IsLocalization.Away (algebraMap R A f) B] (y : A) :
    algebraMap A B y = 0 ↔ ∃ n : ℕ, f ^ n • y = 0 := by
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap R A f))]
  constructor
  · rintro ⟨⟨m, n, hn⟩, hm⟩
    exact ⟨n, by simpa [Algebra.smul_def, hn] using hm⟩
  · rintro ⟨n, hn⟩
    exact ⟨⟨_, n, rfl⟩, by simpa [Algebra.smul_def] using hn⟩
