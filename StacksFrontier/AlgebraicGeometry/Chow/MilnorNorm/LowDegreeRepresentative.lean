module

public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.BassTate

/-!
# The low-degree representative of a class in a simple extension

Let `k` be a field and `φ ∈ k[X]` monic with `φ ≠ 1`, generating a maximal ideal, so that
`κ = k[X] ⧸ φ` is a simple extension of `k`. By
`Stacks.Chow.exists_natDegree_lt_of_quotient_ne_zero` every nonzero class of `κ` is the class of
a nonzero polynomial of degree below `deg φ`, and that polynomial is **unique**: two of them
differ by a multiple of `φ` of degree below `deg φ`, hence by zero
(`Stacks.Chow.eq_of_natDegree_lt_of_dvd_sub`).

So there is a canonical function `Stacks.Chow.polyRep` from `κˣ` to `k[X]`, and this file records
the three properties of it that the inverse of the residue map is built from:

* it is a representative of degree below `deg φ`, and it is the identity on the classes of such
  polynomials (`Stacks.Chow.polyRep_eq_of_mk_eq`);
* it is multiplicative **up to a multiple of `φ`** — `rep(u) rep(v) ≡ rep(uv)` — and no better,
  the product of two polynomials of degree below `deg φ` having degree up to `2 deg φ - 2`
  (`Stacks.Chow.dvd_polyRep_mul_sub_polyRep_mul`);
* it is additive **on the nose** where the Steinberg relation needs it: if `u + v = 1` in `κ` then
  `rep(u) + rep(v) = 1` in `k[X]` (`Stacks.Chow.polyRep_add_polyRep_eq_one`), because a sum of
  two polynomials of degree below `deg φ` again has degree below `deg φ`, so the congruence
  modulo `φ` is an equality.

The contrast between the last two is the whole reason the construction of the inverse map needs a
quotient: the Steinberg relations of `κ` lift exactly, while multiplicativity lifts only modulo a
defect, which has to be killed.

## Main definitions

* `Stacks.Chow.polyRep` — the representative of degree below `deg φ`.

## Main results

* `Stacks.Chow.natDegree_pos_of_monic_ne_one` — a monic polynomial other than `1` has positive
  degree.
* `Stacks.Chow.eq_of_natDegree_lt_of_dvd_sub` — **the representative is unique.**
* `Stacks.Chow.polyRep_ne_zero`, `Stacks.Chow.natDegree_polyRep_lt`,
  `Stacks.Chow.mk_polyRep` — it is a representative of degree below `deg φ`.
* `Stacks.Chow.polyRep_eq_of_mk_eq` — it is the identity on the class of a low-degree polynomial.
* `Stacks.Chow.polyRep_one` — `rep(1) = 1`.
* `Stacks.Chow.dvd_polyRep_mul_sub_polyRep_mul` — multiplicativity modulo `φ`.
* `Stacks.Chow.polyRep_add_polyRep_eq_one` — **the Steinberg relation lifts exactly.**

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Stacks.Chow

/- The quotient of `k[X]` by a maximal ideal is a field; the statements below speak of its unit
group. In `Mathlib` this is a definition rather than a global instance. -/
attribute [local instance] Ideal.Quotient.field

variable {k : Type u} [Field k]

/-! ### Uniqueness of the low-degree representative -/

/-- A monic polynomial other than `1` has positive degree: a monic polynomial of degree zero is
its leading coefficient, which is `1`. -/
theorem natDegree_pos_of_monic_ne_one {φ : Polynomial k} (hφ : φ.Monic) (hφ1 : φ ≠ 1) :
    0 < φ.natDegree := by
  refine Nat.pos_of_ne_zero fun h ↦ hφ1 ?_
  have hc : φ.coeff 0 = 1 := by
    have hlead := hφ.leadingCoeff
    rwa [Polynomial.leadingCoeff, h] at hlead
  rw [Polynomial.eq_C_of_natDegree_eq_zero h, hc, map_one]

/-- **Two polynomials of degree below `deg φ` congruent modulo `φ` are equal.** Their difference
is a multiple of `φ` of degree below `deg φ`, hence zero. -/
theorem eq_of_natDegree_lt_of_dvd_sub {φ f g : Polynomial k} (hf : f.natDegree < φ.natDegree)
    (hg : g.natDegree < φ.natDegree) (hdvd : φ ∣ f - g) : f = g := by
  by_contra hne
  have hsub : f - g ≠ 0 := sub_ne_zero.mpr hne
  have hle : φ.natDegree ≤ (f - g).natDegree := Polynomial.natDegree_le_of_dvd hdvd hsub
  have hmax : (f - g).natDegree ≤ max f.natDegree g.natDegree := Polynomial.natDegree_sub_le f g
  omega

/-- Two polynomials whose classes in `k[X] ⧸ φ` agree differ by a multiple of `φ`. -/
theorem dvd_sub_of_mk_eq {φ f g : Polynomial k}
    (h : Ideal.Quotient.mk (Ideal.span {φ}) f = Ideal.Quotient.mk (Ideal.span {φ}) g) :
    φ ∣ f - g :=
  Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem f g).mp h)

/-! ### The representative -/

/-- **The representative of degree below `deg φ` of a unit of `k[X] ⧸ φ`.** It exists by division
with remainder (`Stacks.Chow.exists_natDegree_lt_of_quotient_ne_zero`) and is unique by
`Stacks.Chow.eq_of_natDegree_lt_of_dvd_sub`. -/
def polyRep {φ : Polynomial k} (hφ : φ.Monic) (hφ1 : φ ≠ 1) [(Ideal.span {φ}).IsMaximal]
    (u : (Polynomial k ⧸ Ideal.span {φ})ˣ) : Polynomial k :=
  (exists_natDegree_lt_of_quotient_ne_zero hφ hφ1 (Units.ne_zero u)).choose

variable {φ : Polynomial k} (hφ : φ.Monic) (hφ1 : φ ≠ 1) [(Ideal.span {φ}).IsMaximal]

/-- The representative `Stacks.Chow.polyRep hφ hφ1 u` is nonzero. -/
theorem polyRep_ne_zero (u : (Polynomial k ⧸ Ideal.span {φ})ˣ) : polyRep hφ hφ1 u ≠ 0 :=
  (exists_natDegree_lt_of_quotient_ne_zero hφ hφ1 (Units.ne_zero u)).choose_spec.1

/-- The representative `Stacks.Chow.polyRep hφ hφ1 u` has degree below `deg φ`. -/
theorem natDegree_polyRep_lt (u : (Polynomial k ⧸ Ideal.span {φ})ˣ) :
    (polyRep hφ hφ1 u).natDegree < φ.natDegree :=
  (exists_natDegree_lt_of_quotient_ne_zero hφ hφ1 (Units.ne_zero u)).choose_spec.2.1

/-- The class of `Stacks.Chow.polyRep hφ hφ1 u` in `k[X] ⧸ φ` is `u`. -/
@[simp]
theorem mk_polyRep (u : (Polynomial k ⧸ Ideal.span {φ})ˣ) :
    Ideal.Quotient.mk (Ideal.span {φ}) (polyRep hφ hφ1 u) =
      (u : Polynomial k ⧸ Ideal.span {φ}) :=
  (exists_natDegree_lt_of_quotient_ne_zero hφ hφ1 (Units.ne_zero u)).choose_spec.2.2

/-- **The representative is the identity on the class of a nonzero polynomial of degree below
`deg φ`.** -/
theorem polyRep_eq_of_mk_eq {u : (Polynomial k ⧸ Ideal.span {φ})ˣ} {f : Polynomial k}
    (hfd : f.natDegree < φ.natDegree)
    (hmk : Ideal.Quotient.mk (Ideal.span {φ}) f = (u : Polynomial k ⧸ Ideal.span {φ})) :
    polyRep hφ hφ1 u = f :=
  eq_of_natDegree_lt_of_dvd_sub (natDegree_polyRep_lt hφ hφ1 u) hfd
    (dvd_sub_of_mk_eq ((mk_polyRep hφ hφ1 u).trans hmk.symm))

/-- The representative of `1` is the constant polynomial `1`. -/
@[simp]
theorem polyRep_one : polyRep hφ hφ1 (1 : (Polynomial k ⧸ Ideal.span {φ})ˣ) = 1 :=
  polyRep_eq_of_mk_eq hφ hφ1
    (by rw [Polynomial.natDegree_one]; exact natDegree_pos_of_monic_ne_one hφ hφ1)
    (by rw [map_one, Units.val_one])

/-! ### Multiplicativity modulo `φ` -/

/-- **The representative is multiplicative modulo `φ`:** `rep(u) rep(v) ≡ rep(u v)`. It is not
multiplicative on the nose — the product of two polynomials of degree below `deg φ` has degree up
to `2 deg φ - 2`, while `rep(u v)` has degree below `deg φ`. -/
theorem dvd_polyRep_mul_sub_polyRep_mul (u v : (Polynomial k ⧸ Ideal.span {φ})ˣ) :
    φ ∣ polyRep hφ hφ1 u * polyRep hφ hφ1 v - polyRep hφ hφ1 (u * v) :=
  dvd_sub_of_mk_eq (by
    rw [map_mul, mk_polyRep, mk_polyRep, mk_polyRep, Units.val_mul])

/-! ### The Steinberg relation lifts exactly -/

/-- **The Steinberg relation lifts to `k[X]` without any defect:** if `u + v = 1` in `k[X] ⧸ φ`
then `rep(u) + rep(v) = 1` in `k[X]`. The sum of two polynomials of degree below `deg φ` again
has degree below `deg φ`, so a congruence modulo `φ` between it and `1` is an equality. -/
theorem polyRep_add_polyRep_eq_one {u v : (Polynomial k ⧸ Ideal.span {φ})ˣ}
    (h : (u : Polynomial k ⧸ Ideal.span {φ}) + (v : Polynomial k ⧸ Ideal.span {φ}) = 1) :
    polyRep hφ hφ1 u + polyRep hφ hφ1 v = 1 := by
  have hdeg : (polyRep hφ hφ1 u + polyRep hφ hφ1 v).natDegree < φ.natDegree := by
    have hmax := Polynomial.natDegree_add_le (polyRep hφ hφ1 u) (polyRep hφ hφ1 v)
    have h1 := natDegree_polyRep_lt hφ hφ1 u
    have h2 := natDegree_polyRep_lt hφ hφ1 v
    omega
  rw [← polyRep_one hφ hφ1]
  exact (polyRep_eq_of_mk_eq hφ hφ1 hdeg (by simp [h])).symm

end Stacks.Chow

end
