module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.QuotSMulTop

/-!
# Relations between two elements of a flat module

Let `N` be a flat module over a commutative ring `A` and let `r t : A`. If `x y : N` satisfy
`t • x = r • y`, then `x` is a finite `A`-linear combination of elements of `N` whose
coefficients `c` all satisfy `t * c ∈ (r)`. In other words, the colon ideal `(r : t)` captures
every such relation: the submodule of elements `x` with `t • x ∈ r • N` is `(r : t) • N`.

This is the form in which flatness is used to compare regular sequences on a module with
regular sequences on the base ring: it transports the division statement
"`t * u ∈ (r)` implies `u ∈ (r)`", which is regularity of `t` on `A ⧸ (r)`, from `A` to `N`.
Taking `r = 0` gives the corresponding statement for annihilators.

## Main results

* `Stacks.RingTheory.Flat.exists_smul_repr_of_smul_eq_smul`: the coefficient form of the
  relation `t • x = r • y` in a flat module.
* `Stacks.RingTheory.Flat.exists_smul_repr_of_smul_eq_zero`: the special case `r = 0`.
* `Stacks.RingTheory.Flat.exists_smul_repr_of_smul_eq_smul_of_tower`: the version used in
  practice, where flatness over `A` is deduced from a flat intermediate ring.

## References

* [Stacks Project, Tag 00HK](https://stacks.math.columbia.edu/tag/00HK)
-/

@[expose] public section

namespace Stacks.RingTheory.Flat

variable {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]

/-- Let `N` be a flat `A`-module and let `r t : A`. Any relation `t • x = r • y` in `N` is
witnessed by coefficients lying in the colon ideal `(r : t)`: there are finitely many
`c j : A` with `t * c j ∈ (r)` and elements `m j : N` with `x = ∑ j, c j • m j`.

This is the equational criterion for flatness, [Stacks, Tag 00HK], applied to the relation
`t • x + (-r) • y = 0`. -/
public theorem exists_smul_repr_of_smul_eq_smul [Module.Flat A N] (r t : A) (x y : N)
    (h : t • x = r • y) :
    ∃ (k : ℕ) (c : Fin k → A) (v : Fin k → A) (m : Fin k → N),
      (∀ j, t * c j = r * v j) ∧ x = ∑ j, c j • m j := by
  have h0 : ∑ i : Fin 2, (![t, -r] i) • (![x, y] i) = 0 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      neg_smul, h, add_neg_cancel]
  obtain ⟨k, a, m, hx, hf⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero h0
  refine ⟨k, a 0, a 1, m, fun j => ?_, hx 0⟩
  have hj := hf j
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at hj
  rwa [neg_mul, add_neg_eq_zero] at hj

/-- The special case `r = 0` of `exists_smul_repr_of_smul_eq_smul`: an element of a flat
module annihilated by `r` is a finite linear combination with coefficients annihilated
by `r`. -/
public theorem exists_smul_repr_of_smul_eq_zero [Module.Flat A N] (r : A) (x : N)
    (h : r • x = 0) :
    ∃ (k : ℕ) (c : Fin k → A) (m : Fin k → N), (∀ j, r * c j = 0) ∧ x = ∑ j, c j • m j := by
  obtain ⟨k, c, v, m, hc, hx⟩ :=
    exists_smul_repr_of_smul_eq_smul (0 : A) r x 0 (by simpa using h)
  exact ⟨k, c, m, fun j => by simpa using hc j, hx⟩

/-- `exists_smul_repr_of_smul_eq_smul` for a module that is flat over a flat intermediate
ring, which is how flatness over the sections of an affine open is obtained from flatness
over a stalk. -/
public theorem exists_smul_repr_of_smul_eq_smul_of_tower (R : Type*) [CommRing R] [Algebra A R]
    [Module R N] [IsScalarTower A R N] [Module.Flat A R] [Module.Flat R N]
    (r t : A) (x y : N) (h : t • x = r • y) :
    ∃ (k : ℕ) (c : Fin k → A) (v : Fin k → A) (m : Fin k → N),
      (∀ j, t * c j = r * v j) ∧ x = ∑ j, c j • m j :=
  have : Module.Flat A N := Module.Flat.trans A R N
  exists_smul_repr_of_smul_eq_smul r t x y h

/-- `exists_smul_repr_of_smul_eq_zero` for a module that is flat over a flat intermediate
ring. -/
public theorem exists_smul_repr_of_smul_eq_zero_of_tower (R : Type*) [CommRing R] [Algebra A R]
    [Module R N] [IsScalarTower A R N] [Module.Flat A R] [Module.Flat R N]
    (r : A) (x : N) (h : r • x = 0) :
    ∃ (k : ℕ) (c : Fin k → A) (m : Fin k → N), (∀ j, r * c j = 0) ∧ x = ∑ j, c j • m j :=
  have : Module.Flat A N := Module.Flat.trans A R N
  exists_smul_repr_of_smul_eq_zero r x h

end Stacks.RingTheory.Flat

namespace Stacks.RingTheory

open Pointwise

/-- If `b` is a nonzerodivisor on `R ⧸ (a)`, then `b * u ∈ (a)` forces `u ∈ (a)`. -/
public theorem exists_mul_eq_of_isSMulRegular_quotSMulTop {R : Type*} [CommRing R] (a b : R)
    (hb : IsSMulRegular (QuotSMulTop a R) b) (u v : R) (h : b * u = a * v) :
    ∃ w, u = a * w := by
  have hmem : u ∈ a • (⊤ : Submodule R R) := by
    have hz : Submodule.Quotient.mk (p := a • (⊤ : Submodule R R)) (b * u) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr
        ((Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨v, Submodule.mem_top, h.symm⟩)
    have h0 : b • Submodule.Quotient.mk (p := a • (⊤ : Submodule R R)) u =
        b • (0 : QuotSMulTop a R) := by
      rw [← Submodule.Quotient.mk_smul, smul_zero, smul_eq_mul]
      exact hz
    exact (Submodule.Quotient.mk_eq_zero _).mp (hb h0)
  obtain ⟨w, -, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists u a _).mp hmem
  exact ⟨w, hw.symm⟩

end Stacks.RingTheory
