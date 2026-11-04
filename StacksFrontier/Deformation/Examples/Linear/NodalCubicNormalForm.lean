module

public import StacksFrontier.Deformation.Examples.Linear.NodalCubicBase

/-!
# The nodal cubic in normal form over `𝔽₂[Y]`

`Deformation.Examples.ArtinSchreier.NC = 𝔽₂[Y, Z]/(Z² + Y·Z + Y³)` is presented in
`StacksFrontier.Deformation.Examples.Linear.NodalCubicBase` as a quotient of `𝔽₂[Y, Z]`, which makes
`IsNoetherianRing` free but hides the one structural fact that a *thickening* of `NC` needs: the
defining equation is monic of degree two in `Z`, so `NC` is free of rank two over `𝔽₂[Y]` with
basis `1, Z`. This file proves exactly that, in the elementary form

  every `u : NC` is `a(Y) + b(Y)·Z` for a unique pair `a, b ∈ 𝔽₂[Y]`,

and draws from it two facts about squares, used in
`StacksFrontier.Deformation.Examples.Linear.NodalCubicWittBase` for the *smooth* form of
Stacks 0DZ2 (`Deformation.FlatModuleLiftBaseChangeStatementSmooth`).

Uniqueness is not formal: it is the only place where the geometry of the curve enters, and it is
proved by pushing a relation `a(Y) + b(Y)·Z = 0` through the normalisation
`Deformation.Examples.ArtinSchreier.ncToAmb : NC → 𝔽₂[s]`, `Y ↦ s² + s`, `Z ↦ s³ + s²`. There
`a(Y)` has even degree `2·deg a` and `b(Y)·Z` has odd degree `2·deg b + 3`, so neither can cancel
the other and both vanish.

## Main definitions

* `Deformation.Examples.ArtinSchreier.ncFromY`: the coefficient inclusion `𝔽₂[Y] → NC`,
  `Y ↦ ncY`.

## Main results

* `Deformation.Examples.ArtinSchreier.exists_ncFromY_repr`: **`1` and `Z` span `NC` over
  `𝔽₂[Y]`**, by induction on the quotient's representatives using `Z² = Y·Z + Y³`.
* `Deformation.Examples.ArtinSchreier.eq_zero_of_ncFromY_add`: **`1` and `Z` are independent over
  `𝔽₂[Y]`**, by the parity-of-degree argument through the normalisation.
* `Deformation.Examples.ArtinSchreier.eq_zero_of_mul_self_eq_zero`: **`NC` has no non-zero
  element of square zero.**
* `Deformation.Examples.ArtinSchreier.eq_one_of_mul_self_eq_one`: **`1` is the only square root
  of `1` in `NC`.** This is what pins a square root of a unit congruent to `1` in a thickening of
  `NC` to the form `1 + 2·b`, which is where the Artin–Schreier obstruction appears.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
-/

@[expose] public noncomputable section

open Polynomial

namespace Deformation.Examples.ArtinSchreier

/-- The two elements of `𝔽₂`. -/
private theorem zmod_two_cases (r : ZMod 2) : r = 0 ∨ r = 1 := by revert r; decide

/-- **The coefficient inclusion `𝔽₂[Y] → NC`**, `Y ↦ ncY`. Together with `ncZ` it presents `NC`
as a free module of rank two over `𝔽₂[Y]`; see
`Deformation.Examples.ArtinSchreier.exists_ncFromY_repr` and
`Deformation.Examples.ArtinSchreier.eq_zero_of_ncFromY_add`. -/
def ncFromY : Polynomial (ZMod 2) →+* NC := (Polynomial.aeval ncY).toRingHom

/-- The coefficient inclusion sends the variable `Y` to `ncY`. -/
@[simp] theorem ncFromY_X : ncFromY X = ncY := by simp [ncFromY]

/-- The defining relation, solved for `Z²` in characteristic two. -/
theorem ncZ_mul_ncZ : ncZ * ncZ = ncY ^ 3 + ncY * ncZ := by
  linear_combination ncRel' - ncY * ncZ * two_eq_zero_nc

/-- The normalisation sends a constant of `NC` to the same constant of `𝔽₂[s]`. -/
theorem ncToAmb_algebraMap (r : ZMod 2) : ncToAmb (algebraMap (ZMod 2) NC r) = C r := by
  rcases zmod_two_cases r with rfl | rfl
  · rw [map_zero, map_zero, Polynomial.C_0]
  · rw [map_one, map_one, Polynomial.C_1]

/-- **The normalisation, in coordinates.** `ncFromY a` is sent to the composite `a(s² + s)`. -/
theorem ncToAmb_ncFromY (a : Polynomial (ZMod 2)) :
    ncToAmb (ncFromY a) = a.comp (X ^ 2 + X) := by
  have hcomp : ((ncToAmb : NC →+* Amb).comp (algebraMap (ZMod 2) NC)) = (C : ZMod 2 →+* Amb) :=
    RingHom.ext fun r => ncToAmb_algebraMap r
  have h : ncToAmb (ncFromY a) = a.eval₂ ((ncToAmb : NC →+* Amb).comp
      (algebraMap (ZMod 2) NC)) (ncToAmb ncY) :=
    Polynomial.hom_eval₂ a (algebraMap (ZMod 2) NC) ncToAmb ncY
  rw [h, ncToAmb_ncY, hcomp]
  rfl

/-! ### `1` and `Z` span -/

/-- **`1` and `Z` span `NC` over `𝔽₂[Y]`.** Every element of the nodal cubic is `a(Y) + b(Y)·Z`.
The induction is over a representative in `𝔽₂[Y, Z]`; the only step with content is
multiplication by `Z`, folded back by the defining relation `Z² = Y·Z + Y³`
(`Deformation.Examples.ArtinSchreier.ncZ_mul_ncZ`). -/
theorem exists_ncFromY_repr (u : NC) :
    ∃ a b : Polynomial (ZMod 2), u = ncFromY a + ncFromY b * ncZ := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective u
  induction f using MvPolynomial.induction_on with
  | C r =>
      refine ⟨C r, 0, ?_⟩
      rw [map_zero, zero_mul, add_zero]
      rcases zmod_two_cases r with rfl | rfl
      · simp
      · simp
  | add p q hp hq =>
      obtain ⟨a₁, b₁, h₁⟩ := hp
      obtain ⟨a₂, b₂, h₂⟩ := hq
      refine ⟨a₁ + a₂, b₁ + b₂, ?_⟩
      rw [map_add, h₁, h₂, map_add, map_add]
      ring
  | mul_X p i hp =>
      obtain ⟨a, b, h⟩ := hp
      have key : ∀ y : NC, y = ncY ∨ y = ncZ →
          ∃ a' b' : Polynomial (ZMod 2),
            (ncFromY a + ncFromY b * ncZ) * y = ncFromY a' + ncFromY b' * ncZ := by
        intro y hy
        rcases hy with rfl | rfl
        · exact ⟨a * X, b * X, by rw [map_mul, map_mul, ncFromY_X]; ring⟩
        · refine ⟨b * X ^ 3, a + b * X, ?_⟩
          rw [map_mul, map_pow, map_add, map_mul, ncFromY_X]
          linear_combination (ncFromY b) * ncZ_mul_ncZ
      have hi : Ideal.Quotient.mk (Ideal.span {ncEq}) (MvPolynomial.X i) = ncY ∨
          Ideal.Quotient.mk (Ideal.span {ncEq}) (MvPolynomial.X i) = ncZ := by
        fin_cases i
        · exact Or.inl rfl
        · exact Or.inr rfl
      rw [map_mul, h]
      exact key _ hi

/-! ### `1` and `Z` are independent -/

/-- The degree of `X ^ n + X ^ m` is `n` when `m < n`. -/
private theorem natDegree_X_pow_add_X_pow {m n : ℕ} (h : m < n) :
    (X ^ n + X ^ m : Amb).natDegree = n := by
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt, Polynomial.natDegree_X_pow]
  rwa [Polynomial.natDegree_X_pow, Polynomial.natDegree_X_pow]

private theorem natDegree_sq_add : (X ^ 2 + X : Amb).natDegree = 2 := by
  simpa using natDegree_X_pow_add_X_pow (show 1 < 2 by norm_num)

private theorem natDegree_cube_add : (X ^ 3 + X ^ 2 : Amb).natDegree = 3 :=
  natDegree_X_pow_add_X_pow (by norm_num)

private theorem leadingCoeff_sq_add : (X ^ 2 + X : Amb).leadingCoeff = 1 := by
  rw [Polynomial.leadingCoeff, natDegree_sq_add]
  simp [Polynomial.coeff_X, Polynomial.coeff_X_pow]

private theorem natDegree_comp_sq_add (a : Polynomial (ZMod 2)) :
    (a.comp (X ^ 2 + X)).natDegree = 2 * a.natDegree := by
  rw [Polynomial.natDegree_comp, natDegree_sq_add, mul_comm]

private theorem comp_sq_add_eq_zero_iff (a : Polynomial (ZMod 2)) :
    a.comp (X ^ 2 + X) = 0 ↔ a = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, Polynomial.zero_comp]⟩
  have hd : (X ^ 2 + X : Amb).natDegree ≠ 0 := by rw [natDegree_sq_add]; omega
  have hlc : (a.comp (X ^ 2 + X)).leadingCoeff = a.leadingCoeff := by
    rw [Polynomial.leadingCoeff_comp hd, leadingCoeff_sq_add, one_pow, mul_one]
  rw [h, Polynomial.leadingCoeff_zero] at hlc
  exact Polynomial.leadingCoeff_eq_zero.mp hlc.symm

/-- **`1` and `Z` are independent over `𝔽₂[Y]`.** If `a(Y) + b(Y)·Z = 0` in the nodal cubic then
`a = b = 0`.

This is the one step that uses the curve rather than its presentation. Pushing the relation
through the normalisation `Y ↦ s² + s`, `Z ↦ s³ + s²` turns it into
`a(s² + s) + b(s² + s)·(s³ + s²) = 0` in `𝔽₂[s]`, where the first summand has degree `2·deg a`
and the second degree `2·deg b + 3`. Two polynomials whose degrees have different parity cannot
cancel, so both vanish; and a composite with the degree-two `s² + s` vanishes only for the zero
polynomial. -/
theorem eq_zero_of_ncFromY_add {a b : Polynomial (ZMod 2)}
    (h : ncFromY a + ncFromY b * ncZ = 0) : a = 0 ∧ b = 0 := by
  have hamb : a.comp (X ^ 2 + X) + b.comp (X ^ 2 + X) * (X ^ 3 + X ^ 2) = 0 := by
    have hc := congrArg ncToAmb h
    rwa [map_add, map_mul, ncToAmb_ncFromY, ncToAmb_ncFromY, ncToAmb_ncZ, map_zero] at hc
  have hb : b = 0 := by
    by_contra hb0
    have hbc : b.comp (X ^ 2 + X) ≠ 0 := fun hc => hb0 ((comp_sq_add_eq_zero_iff b).mp hc)
    have hXX : (X ^ 3 + X ^ 2 : Amb) ≠ 0 := by
      intro hz
      have hd := natDegree_cube_add
      rw [hz, Polynomial.natDegree_zero] at hd
      omega
    have heq : a.comp (X ^ 2 + X) = -(b.comp (X ^ 2 + X) * (X ^ 3 + X ^ 2)) := by
      linear_combination hamb
    have hdeg := congrArg Polynomial.natDegree heq
    rw [natDegree_comp_sq_add, Polynomial.natDegree_neg, Polynomial.natDegree_mul hbc hXX,
      natDegree_comp_sq_add, natDegree_cube_add] at hdeg
    omega
  refine ⟨?_, hb⟩
  rw [hb, Polynomial.zero_comp, zero_mul, add_zero] at hamb
  exact (comp_sq_add_eq_zero_iff a).mp hamb

/-- **Coordinates are determined.** Two normal forms of the same element of `NC` agree. -/
theorem ncFromY_add_inj {a b a' b' : Polynomial (ZMod 2)}
    (h : ncFromY a + ncFromY b * ncZ = ncFromY a' + ncFromY b' * ncZ) : a = a' ∧ b = b' := by
  have h0 : ncFromY (a - a') + ncFromY (b - b') * ncZ = 0 := by
    rw [map_sub, map_sub]
    linear_combination h
  obtain ⟨h1, h2⟩ := eq_zero_of_ncFromY_add h0
  exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩

/-! ### Consequences for squares -/

/-- **The nodal cubic has no non-zero element of square zero.** In coordinates
`u = a(Y) + b(Y)·Z` one has `u² = (a² + b²Y³) + (b²Y)·Z` in characteristic two, so `u² = 0`
forces `b²Y = 0` and then `a² = 0`, and `𝔽₂[Y]` is a domain. -/
theorem eq_zero_of_mul_self_eq_zero {u : NC} (h : u * u = 0) : u = 0 := by
  obtain ⟨a, b, rfl⟩ := exists_ncFromY_repr u
  have hexp : ncFromY (a * a + b * b * X ^ 3) + ncFromY (b * b * X) * ncZ = 0 := by
    simp only [map_add, map_mul, map_pow, ncFromY_X]
    linear_combination h - (ncFromY b) * (ncFromY b) * ncZ_mul_ncZ -
      (ncFromY a) * (ncFromY b) * ncZ * two_eq_zero_nc
  obtain ⟨h1, h2⟩ := eq_zero_of_ncFromY_add hexp
  have hb : b = 0 := by
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact mul_self_eq_zero.mp h3
    · exact absurd h3 Polynomial.X_ne_zero
  have ha : a = 0 := by
    rw [hb, zero_mul, zero_mul, add_zero] at h1
    exact mul_self_eq_zero.mp h1
  simp [ha, hb]

/-- **`1` is the only square root of `1` in the nodal cubic.** In characteristic two `u² = 1`
reads `(u + 1)² = 0`, and `Deformation.Examples.ArtinSchreier.eq_zero_of_mul_self_eq_zero` forces
`u = 1`. -/
theorem eq_one_of_mul_self_eq_one {u : NC} (h : u * u = 1) : u = 1 := by
  have h0 : (u + 1) * (u + 1) = 0 := by
    linear_combination h + (u + 1) * two_eq_zero_nc
  have h1 := eq_zero_of_mul_self_eq_zero h0
  linear_combination h1 - two_eq_zero_nc

end Deformation.Examples.ArtinSchreier

end
