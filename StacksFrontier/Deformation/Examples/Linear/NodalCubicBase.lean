module

public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import StacksFrontier.Deformation.Examples.Linear.ArtinSchreierLocalGlobal

/-!
# The nodal cubic as a quotient, and its Artin–Schreier class

`StacksFrontier.Deformation.Examples.Linear.ArtinSchreierLocalGlobal` presents the base of the
Stacks 0DZ2 counterexample as the *subring* `{f ∈ 𝔽₂[s] : f(0) = f(1)}` of `𝔽₂[s]`. That
presentation makes the class `ω = s² + s` easy to handle but makes `IsNoetherianRing` into real
work: one has to exhibit the subring as a finitely generated `𝔽₂`-algebra.

This file gives the same ring as a *quotient*, which is the presentation the instantiation of
`Deformation.FlatModuleLiftBaseChangeStatement` wants:

`NC = 𝔽₂[Y, Z]/(Z² + Y·Z + Y³)`,  `ω = Y`.

`NC` is the affine nodal cubic. `IsNoetherianRing` is then immediate, and the two Artin–Schreier
facts come out even more cheaply than before:

* `exists_isASSol_of_isUnit_ncY`: whenever `Y` becomes a **unit**, `α = Z/Y` solves
  `α² + α = Y`, because `Z² + Y·Z = Y³` *is* the defining relation. In particular the class dies
  on `D(Y)`, hence on `D(g)` for every `g ∈ (Y)`.
* `not_isASSol_ncY`: the class does **not** die on `NC`. The ring map `NC → 𝔽₂[s]` with
  `Y ↦ s² + s` and `Z ↦ s³ + s²` is well defined — the relation holds, as `ncToAmbPre_ncEq`
  records — and its image lies in the subring `nodal`, while the only two solutions
  of `b² + b = s² + s` over `𝔽₂[s]` are `s` and `s + 1`
  (`Deformation.Examples.ArtinSchreier.eq_or_eq_of_isASSol_amb`), neither of which lies in
  `nodal`.

So this file is the subring file's content transported to a presentation with free
Noetherianness, and nothing beyond it is needed from the subring presentation: the subring
survives only as the recipient of the normalisation map, which is what makes the
non-solvability argument work.

## Main definitions

* `Deformation.Examples.ArtinSchreier.NC`: the affine nodal cubic `𝔽₂[Y, Z]/(Z² + Y·Z + Y³)`.
* `Deformation.Examples.ArtinSchreier.ncY`, `Deformation.Examples.ArtinSchreier.ncZ`: the two
  coordinates.
* `Deformation.Examples.ArtinSchreier.ncToAmb`: the normalisation `NC → 𝔽₂[s]`.

## Main results

* `Deformation.Examples.ArtinSchreier.ncRel`: the defining relation, as an identity in `NC`.
* `Deformation.Examples.ArtinSchreier.exists_isASSol_of_isUnit_ncY`: **the class dies wherever
  `Y` is a unit**, by `α = Z/Y`.
* `Deformation.Examples.ArtinSchreier.ncToAmb_mem_nodal`: the normalisation lands in the nodal
  subring.
* `Deformation.Examples.ArtinSchreier.not_isASSol_ncY`: **the class does not die on `NC`.**

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Deformation.Examples.ArtinSchreier

/-! ### The nodal cubic -/

/-- The polynomial ring `𝔽₂[Y, Z]`. -/
abbrev NCAmb : Type := MvPolynomial (Fin 2) (ZMod 2)

/-- `Y`, the coordinate that will carry the Artin–Schreier class. -/
def ncYpoly : NCAmb := MvPolynomial.X 0

/-- `Z`, the other coordinate. -/
def ncZpoly : NCAmb := MvPolynomial.X 1

/-- The defining equation `Z² + Y·Z + Y³` of the affine nodal cubic. -/
def ncEq : NCAmb := ncZpoly * ncZpoly + ncYpoly * ncZpoly + ncYpoly ^ 3

/-- **The affine nodal cubic** `𝔽₂[Y, Z]/(Z² + Y·Z + Y³)`, the base of the Stacks 0DZ2
counterexample, presented as a quotient so that `IsNoetherianRing` is immediate. -/
abbrev NC : Type := NCAmb ⧸ Ideal.span {ncEq}

/-- `Y` in the nodal cubic. -/
def ncY : NC := Ideal.Quotient.mk _ ncYpoly

/-- `Z` in the nodal cubic. -/
def ncZ : NC := Ideal.Quotient.mk _ ncZpoly

/-- **The defining relation**, as an identity in `NC`. -/
theorem ncRel : ncZ * ncZ + ncY * ncZ + ncY ^ 3 = 0 := by
  have h : Ideal.Quotient.mk (Ideal.span {ncEq})
      (ncZpoly * ncZpoly + ncYpoly * ncZpoly + ncYpoly ^ 3) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  rw [map_add, map_add, map_mul, map_mul, map_pow] at h
  exact h

/-- `2 = 0` in the nodal cubic. -/
theorem two_eq_zero_nc : (2 : NC) = 0 := by
  have h2 : (2 : NCAmb) = 0 := by
    have h := CharP.cast_eq_zero NCAmb 2
    exact_mod_cast h
  rw [← map_ofNat (Ideal.Quotient.mk (Ideal.span {ncEq})) 2, h2, map_zero]

/-- The relation in the form the Artin–Schreier witness uses: `Z² + Y·Z = Y³`. -/
theorem ncRel' : ncZ * ncZ + ncY * ncZ = ncY ^ 3 := by
  linear_combination ncRel - ncY ^ 3 * two_eq_zero_nc

/-! ### The class dies wherever `Y` is a unit -/

/-- **The Artin–Schreier class of `Y` dies wherever `Y` becomes a unit.** For a ring
homomorphism `φ` out of the nodal cubic with `φ Y` a unit, `α = φ Z · (φ Y)⁻¹` solves
`α · α + α = φ Y`: multiplying through by `(φ Y)²` turns the equation into
`Z² + Y·Z = Y³`, which is the defining relation. -/
theorem exists_isASSol_of_isUnit_ncY {S : Type*} [CommRing S] (φ : NC →+* S)
    (hu : IsUnit (φ ncY)) : ∃ b : S, IsASSol (φ ncY) b := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  refine ⟨φ ncZ * v, ?_⟩
  have hrel : φ ncZ * φ ncZ + φ ncY * φ ncZ = φ ncY ^ 3 := by
    have := congrArg φ ncRel'
    simpa [map_add, map_mul, map_pow] using this
  unfold IsASSol
  linear_combination (v * v) * hrel +
    (φ ncY * φ ncY * v + φ ncY - φ ncZ * v) * hv

/-! ### The class does not die on the nodal cubic -/

/-- The normalisation `𝔽₂[Y, Z] → 𝔽₂[s]`, `Y ↦ s² + s`, `Z ↦ s³ + s²`. -/
def ncToAmbPre : NCAmb →+* Amb :=
  (MvPolynomial.aeval (R := ZMod 2) (fun i : Fin 2 => if i = 0 then X ^ 2 + X
    else X ^ 3 + X ^ 2)).toRingHom

/-- The defining equation is killed by the normalisation: `(s³+s²)² + (s²+s)(s³+s²) + (s²+s)³`
vanishes in `𝔽₂[s]`. This is what makes the nodal cubic the ring of functions on `𝔽₂[s]` with
the two points `s = 0` and `s = 1` glued. -/
theorem ncToAmbPre_ncEq : ncToAmbPre ncEq = 0 := by
  have h2 : (2 : Amb) = 0 := CharTwo.two_eq_zero
  simp only [ncToAmbPre, ncEq, ncYpoly, ncZpoly, AlgHom.toRingHom_eq_coe, map_add, map_mul,
    map_pow, RingHom.coe_coe, MvPolynomial.aeval_X]
  norm_num
  linear_combination (X ^ 3 + 3 * X ^ 4 + 3 * X ^ 5 + X ^ 6 : Amb) * h2

/-- **The normalisation** `NC → 𝔽₂[s]`, `Y ↦ s² + s`, `Z ↦ s³ + s²`. -/
def ncToAmb : NC →+* Amb :=
  Ideal.Quotient.lift _ ncToAmbPre (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 ha
    rw [map_mul, ncToAmbPre_ncEq, zero_mul])

/-- The normalisation sends the variable `i` to `s² + s` if `i = 0` and to `s³ + s²` otherwise. -/
private theorem ncToAmbPre_X (i : Fin 2) :
    ncToAmbPre (MvPolynomial.X i) = (if i = 0 then X ^ 2 + X else X ^ 3 + X ^ 2 : Amb) := by
  simp [ncToAmbPre]

/-- The normalisation `ncToAmb` sends `Y` to `s² + s`. -/
theorem ncToAmb_ncY : ncToAmb ncY = X ^ 2 + X := by
  exact (ncToAmbPre_X 0).trans (by simp)

/-- The normalisation `ncToAmb` sends `Z` to `s³ + s²`. -/
theorem ncToAmb_ncZ : ncToAmb ncZ = X ^ 3 + X ^ 2 := by
  exact (ncToAmbPre_X 1).trans (by simp)

/-- **The normalisation lands in the nodal subring** `{f ∈ 𝔽₂[s] : f(0) = f(1)}`: both `s² + s`
and `s³ + s²` vanish at `0` and at `1`, so the whole image does, `nodal` being a subring. -/
theorem ncToAmb_mem_nodal (a : NC) : ncToAmb a ∈ nodal := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  change ncToAmbPre f ∈ nodal
  induction f using MvPolynomial.induction_on with
  | C r =>
      rw [show ncToAmbPre (MvPolynomial.C r) = Polynomial.C (algebraMap (ZMod 2) (ZMod 2) r) from
        by simp [ncToAmbPre]]
      rw [mem_nodal]
      simp
  | add p q hp hq =>
      rw [map_add]
      exact nodal.add_mem hp hq
  | mul_X p i hp =>
      rw [map_mul]
      refine nodal.mul_mem hp ?_
      rw [ncToAmbPre_X, mem_nodal]
      split <;> simp only [eval_add, eval_pow, eval_X] <;> decide

/-- **The Artin–Schreier class of `Y` does not die on the nodal cubic.** If `a · a + a = Y` in
`NC` then, pushing through the normalisation, `b · b + b = s² + s` in `𝔽₂[s]` for
`b = ncToAmb a`, so `b = s` or `b = s + 1` by
`Deformation.Examples.ArtinSchreier.eq_or_eq_of_isASSol_amb`; but `b` lies in the nodal subring
by `ncToAmb_mem_nodal`, and neither `s` nor `s + 1` takes the same value at `0` and at `1`. -/
theorem not_isASSol_ncY : ¬ ∃ a : NC, IsASSol ncY a := by
  rintro ⟨a, ha⟩
  have hb : IsASSol (X ^ 2 + X : Amb) (ncToAmb a) := by
    have := congrArg ncToAmb ha
    rw [ncToAmb_ncY] at this
    simpa [IsASSol, map_add, map_mul] using this
  have hmem : ncToAmb a ∈ nodal := ncToAmb_mem_nodal a
  rw [mem_nodal] at hmem
  rcases eq_or_eq_of_isASSol_amb hb with h | h
  all_goals
    rw [h] at hmem
    simp only [eval_add, eval_X, eval_one] at hmem
    exact absurd hmem (by decide)

end Deformation.Examples.ArtinSchreier

end
