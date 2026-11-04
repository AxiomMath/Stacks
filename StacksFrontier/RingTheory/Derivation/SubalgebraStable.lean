module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.Tactic.LinearCombination

/-!
# Subalgebras preserved by a derivation

Let `L` be an algebra over a commutative ring `A` and let `E` be a derivation of `L` (over any
base). The elements `z` of a subalgebra `B` of `L` with `E z ∈ B` form a subalgebra of `L`
again, by the Leibniz rule: this is `Derivation.stableSubalgebra`, the subalgebra counterpart of
`Derivation.stableSubideal`. Consequently `E` maps the whole of `B` into `B` as soon as it maps
a set of `A`-algebra generators of `B` into `B`.

The second half of the file says when a *single* generator is handled, and it is the only place
where anything is computed. If `y` satisfies a polynomial relation `p (y) = 0` with coefficients
in `A` whose formal derivative `p' (y)` is invertible in `B`, then `E y` is forced:

`E (p (y)) = p' (y) · E y + Σ_n y ^ n · E (algebraMap A L (coeff p n))`,

so `p' (y) · E y` is the negative of a sum of elements of `B`. The identity is
`Derivation.apply_aeval_sub_mul_apply`, and its right-hand side depends on `E` only through the
values of `E` on the image of `A`; that is why the same identity yields both that `E y` lies in
`B` and that two derivations agreeing on the image of `A` agree at `y`.

Taken together: a derivation of `L` extending a derivation of `A` maps a subalgebra `B` into
itself, and is determined on `B`, once `B` is generated over `A` by elements with a polynomial
relation of invertible derivative. This is the ring-theoretic mechanism behind extending a
vector field across a singularity whose normalization is monogenic with invertible discriminant,
with no locality hypothesis on `A`.

## Main definitions

* `Derivation.stableSubalgebra` — the elements of a subalgebra preserved by a derivation.

## Main results

* `Derivation.apply_aeval_sub_mul_apply` — the value of a derivation on `p (y)`, split into the
  term `p' (y) · E y` and a term depending only on `E` along `A`.
* `Derivation.apply_mem_of_isUnit_aeval_derivative` — `E y ∈ B` for a single generator with
  invertible derivative.
* `Derivation.apply_mem_of_adjoin_eq` — `E` maps `B` into `B` when it does so on generators.
* `Derivation.eq_of_isUnit_aeval_derivative` — two derivations agreeing along `A` agree at such
  a generator.
* `Derivation.ext_of_adjoin_eq` — and therefore agree on all of `B`.
-/

@[expose] public noncomputable section

open Polynomial

universe u v w

namespace Derivation

section Aeval

variable {R : Type u} {A : Type v} {C : Type w} [CommRing R] [CommRing A] [CommRing C]
variable [Algebra R C] [Algebra A C]

/-- The elementary identity behind every extension of a derivation across an integral element.
For `E` a derivation of `C`, `y : C` and `p` a polynomial with coefficients in `A`, the value of
`E` at `p (y)` is `p' (y) * E y` plus a term built only from the values of `E` on the image of
`A`:

`E (p (y)) - p' (y) * E y = Σ_n y ^ n * E (algebraMap A C (coeff p n))`.

The right-hand side does not mention `E y`, and depends on `E` only along `algebraMap A C`. -/
public theorem apply_aeval_sub_mul_apply (E : Derivation R C C) (y : C) (p : A[X]) :
    E (aeval y p) - aeval y (derivative p) * E y =
      p.sum fun n a => y ^ n * E (algebraMap A C a) := by
  have hf : ∀ i : ℕ, y ^ i * E (algebraMap A C (0 : A)) = 0 := fun _ => by
    rw [map_zero, map_zero, mul_zero]
  have hadd : ∀ (i : ℕ) (a b : A), y ^ i * E (algebraMap A C (a + b)) =
      y ^ i * E (algebraMap A C a) + y ^ i * E (algebraMap A C b) := fun _ _ _ => by
    rw [map_add, map_add, mul_add]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.sum_add_index p q _ hf hadd]
    simp only [map_add]
    linear_combination hp + hq
  | monomial n a =>
    have h₁ : E (algebraMap A C a * y ^ n) =
        algebraMap A C a * E (y ^ n) + y ^ n * E (algebraMap A C a) := by
      rw [E.leibniz, smul_eq_mul, smul_eq_mul]
    have h₂ : E (y ^ n) = (n : C) * (y ^ (n - 1) * E y) := by
      rw [E.leibniz_pow, nsmul_eq_mul, smul_eq_mul]
    have h₃ : algebraMap A C (a * (n : A)) = algebraMap A C a * (n : C) := by
      rw [map_mul]
      simp
    rw [Polynomial.sum_monomial_index a _ (hf n), aeval_monomial, derivative_monomial,
      aeval_monomial, h₁, h₂, h₃]
    ring

/-- If `p (y) = 0`, then `p' (y) * E y` is minus the term of `apply_aeval_sub_mul_apply`. -/
private theorem aeval_derivative_mul_apply_of_aeval_eq_zero (E : Derivation R C C) {y : C}
    (p : A[X]) (hp : aeval y p = 0) :
    aeval y (derivative p) * E y = -(p.sum fun n a => y ^ n * E (algebraMap A C a)) := by
  have h := apply_aeval_sub_mul_apply E y p
  rw [hp, map_zero, zero_sub] at h
  linear_combination -h

/-- **A derivation is forced at an integral element with invertible derivative.** If `y` lies in
a subalgebra `B` of `C`, satisfies a polynomial relation `p (y) = 0` with coefficients in `A`,
and `p' (y)` has an inverse in `B`, then `E y ∈ B` as soon as `E` carries the image of `A` into
`B`. No finiteness or locality hypothesis is needed. -/
public theorem apply_mem_of_isUnit_aeval_derivative (E : Derivation R C C) (B : Subalgebra A C)
    (hE : ∀ a : A, E (algebraMap A C a) ∈ B) {y : C} (hy : y ∈ B) (p : A[X])
    (hp : aeval y p = 0) {w : C} (hw : w ∈ B) (hwu : w * aeval y (derivative p) = 1) :
    E y ∈ B := by
  have hsum : (p.sum fun n a => y ^ n * E (algebraMap A C a)) ∈ B := by
    rw [Polynomial.sum_def]
    exact B.sum_mem fun n _ => B.mul_mem (B.pow_mem hy n) (hE _)
  rw [show E y = w * (aeval y (derivative p) * E y) by rw [← mul_assoc, hwu, one_mul],
    aeval_derivative_mul_apply_of_aeval_eq_zero E p hp]
  exact B.mul_mem hw (neg_mem hsum)

/-- **Two derivations agreeing along the base agree at an integral element with invertible
derivative.** The inverse of `p' (y)` is not required to lie in any subalgebra here. -/
public theorem eq_of_isUnit_aeval_derivative (E₁ E₂ : Derivation R C C)
    (hE : ∀ a : A, E₁ (algebraMap A C a) = E₂ (algebraMap A C a)) (y : C) (p : A[X])
    (hp : aeval y p = 0) {w : C} (hwu : w * aeval y (derivative p) = 1) :
    E₁ y = E₂ y := by
  have h₁ := aeval_derivative_mul_apply_of_aeval_eq_zero E₁ p hp
  have h₂ := aeval_derivative_mul_apply_of_aeval_eq_zero E₂ p hp
  have hsum : (p.sum fun n a => y ^ n * E₁ (algebraMap A C a)) =
      p.sum fun n a => y ^ n * E₂ (algebraMap A C a) := by
    rw [Polynomial.sum_def, Polynomial.sum_def]
    exact Finset.sum_congr rfl fun n _ => by rw [hE]
  linear_combination w * (h₁ - h₂ - hsum) + (E₂ y - E₁ y) * hwu

end Aeval

section Stable

variable {R : Type u} {A : Type v} {L : Type w} [CommRing R] [CommRing A] [CommRing L]
variable [Algebra R L] [Algebra A L]

/-- The elements of a subalgebra `B` whose image under a derivation again lies in `B`.  The
Leibniz rule makes this set a subalgebra, provided the derivation carries the image of the base
ring into `B`.  This is the subalgebra counterpart of `Derivation.stableSubideal`. -/
public def stableSubalgebra (E : Derivation R L L) (B : Subalgebra A L)
    (hE : ∀ a : A, E (algebraMap A L a) ∈ B) : Subalgebra A L where
  carrier := {z | z ∈ B ∧ E z ∈ B}
  add_mem' ha hb := ⟨B.add_mem ha.1 hb.1, by rw [map_add]; exact B.add_mem ha.2 hb.2⟩
  zero_mem' := ⟨B.zero_mem, by rw [map_zero]; exact B.zero_mem⟩
  mul_mem' ha hb := by
    refine ⟨B.mul_mem ha.1 hb.1, ?_⟩
    rw [E.leibniz, smul_eq_mul, smul_eq_mul]
    exact B.add_mem (B.mul_mem ha.1 hb.2) (B.mul_mem hb.1 ha.2)
  one_mem' := ⟨B.one_mem, by rw [E.map_one_eq_zero]; exact B.zero_mem⟩
  algebraMap_mem' a := ⟨B.algebraMap_mem a, hE a⟩

/-- Membership in `Derivation.stableSubalgebra` is membership in `B` together with membership of
the image. -/
public theorem mem_stableSubalgebra_iff (E : Derivation R L L) (B : Subalgebra A L)
    (hE : ∀ a : A, E (algebraMap A L a) ∈ B) (z : L) :
    z ∈ stableSubalgebra E B hE ↔ z ∈ B ∧ E z ∈ B := Iff.rfl

/-- **A derivation preserves a subalgebra as soon as it preserves a generating set.** If `B` is
generated as an `A`-algebra by a set `S`, the derivation `E` carries the image of `A` into `B`,
and `E y ∈ B` for every `y ∈ S`, then `E` maps the whole of `B` into `B`. -/
public theorem apply_mem_of_adjoin_eq (E : Derivation R L L) (B : Subalgebra A L)
    (hE : ∀ a : A, E (algebraMap A L a) ∈ B) (S : Set L) (hS : Algebra.adjoin A S = B)
    (hgen : ∀ y ∈ S, E y ∈ B) {z : L} (hz : z ∈ B) : E z ∈ B := by
  have hle : Algebra.adjoin A S ≤ stableSubalgebra E B hE :=
    Algebra.adjoin_le fun y hy => ⟨hS ▸ Algebra.subset_adjoin hy, hgen y hy⟩
  rw [hS] at hle
  exact (hle hz).2

/-- **The same, with the generators handled by their polynomial relations.** If every generator
of `B` satisfies a polynomial relation over `A` whose formal derivative at that generator is
invertible in `B`, then `E` maps `B` into `B`. -/
public theorem apply_mem_of_adjoin_eq_of_isUnit_aeval_derivative (E : Derivation R L L)
    (B : Subalgebra A L) (hE : ∀ a : A, E (algebraMap A L a) ∈ B) (S : Set L)
    (hS : Algebra.adjoin A S = B)
    (hgen : ∀ y ∈ S, ∃ p : A[X], aeval y p = 0 ∧
      ∃ w ∈ B, w * aeval y (derivative p) = 1) {z : L} (hz : z ∈ B) : E z ∈ B := by
  refine apply_mem_of_adjoin_eq E B hE S hS (fun y hy => ?_) hz
  obtain ⟨p, hp, w, hw, hwu⟩ := hgen y hy
  exact apply_mem_of_isUnit_aeval_derivative E B hE (hS ▸ Algebra.subset_adjoin hy) p hp hw hwu

end Stable

section Ext

variable {R : Type u} {A : Type v} {L : Type w} [CommRing R] [CommRing A] [CommRing L]
variable [Algebra R L] [Algebra A L] [Algebra R A] [IsScalarTower R A L]

/-- **A derivation of a subalgebra is determined by its values along the base and on a
generating set.** Here the two derivations are derivations of `↥B` itself, which is the shape in
which an extension of a derivation to a subalgebra is produced. -/
public theorem ext_of_adjoin_eq (B : Subalgebra A L) (S : Set L) (hS : Algebra.adjoin A S = B)
    (E₁ E₂ : Derivation R ↥B ↥B)
    (hE : ∀ a : A, E₁ (algebraMap A ↥B a) = E₂ (algebraMap A ↥B a))
    (hgen : ∀ t : ↥B, (t : L) ∈ S → E₁ t = E₂ t) : E₁ = E₂ := by
  let Q : Subalgebra A ↥B :=
    { carrier := {t | E₁ t = E₂ t}
      add_mem' := fun ha hb => by
        show E₁ _ = E₂ _
        rw [map_add, map_add, ha, hb]
      zero_mem' := by
        show E₁ _ = E₂ _
        rw [map_zero, map_zero]
      mul_mem' := fun {a b} ha hb => by
        show E₁ _ = E₂ _
        rw [E₁.leibniz, E₂.leibniz]
        show a • E₁ b + b • E₁ a = a • E₂ b + b • E₂ a
        rw [show E₁ b = E₂ b from hb, show E₁ a = E₂ a from ha]
      one_mem' := by
        show E₁ _ = E₂ _
        rw [E₁.map_one_eq_zero, E₂.map_one_eq_zero]
      algebraMap_mem' := hE }
  have hle : Algebra.adjoin A S ≤ Q.map B.val :=
    Algebra.adjoin_le fun y hy =>
      ⟨⟨y, hS ▸ Algebra.subset_adjoin hy⟩, hgen ⟨y, hS ▸ Algebra.subset_adjoin hy⟩ hy, rfl⟩
  rw [hS] at hle
  refine Derivation.ext fun t => ?_
  obtain ⟨t', ht', hteq⟩ := hle t.2
  exact (Subtype.ext hteq : t' = t) ▸ ht'

/-- **The same, with the generators handled by their polynomial relations.** -/
public theorem ext_of_adjoin_eq_of_isUnit_aeval_derivative (B : Subalgebra A L) (S : Set L)
    (hS : Algebra.adjoin A S = B) (E₁ E₂ : Derivation R ↥B ↥B)
    (hE : ∀ a : A, E₁ (algebraMap A ↥B a) = E₂ (algebraMap A ↥B a))
    (hgen : ∀ t : ↥B, (t : L) ∈ S → ∃ p : A[X], aeval t p = 0 ∧
      ∃ w : ↥B, w * aeval t (derivative p) = 1) : E₁ = E₂ := by
  refine ext_of_adjoin_eq B S hS E₁ E₂ hE fun t ht => ?_
  obtain ⟨p, hp, w, hwu⟩ := hgen t ht
  exact eq_of_isUnit_aeval_derivative E₁ E₂ hE t p hp hwu

end Ext

end Derivation

end
