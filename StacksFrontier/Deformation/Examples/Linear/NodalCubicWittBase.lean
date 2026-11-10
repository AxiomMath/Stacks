module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import StacksFrontier.Deformation.Examples.Linear.NodalCubicNormalForm

/-!
# A non-split nilpotent thickening of the nodal cubic, and its Artin–Schreier square root

Stacks 0DZ2 is false as stated — see
`Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatementFaithful` — and the one
form of it that survives, `Deformation.FlatModuleLiftBaseChangeStatementSmooth` (0DZ2 with `P'`
smooth over `A'`), is *proved* over a base `A' → A` admitting a ring section
(`Deformation.exists_flatModuleLift_iff_baseChange_of_ringHom_section`). So a counterexample to
the smooth form needs a base with **no** ring section, which the nodal-cubic witness
`NC[t]/t³ → NC` does not supply.

This file builds the base that the obstruction of that witness asks for:

  `A' = NCW = (ZMod 8)[Y, Z]/(Z² + Y·Z + Y³)`  over  `A = NC = 𝔽₂[Y, Z]/(Z² + Y·Z + Y³)`.

`NCW` is presented as `(ZMod 8)[Y][Z]/(Z² + Y·Z + Y³)`, i.e. as an
`AdjoinRoot` of a monic quadratic, so that it is free of rank two over `(ZMod 8)[Y]` and every
computation can be done in coordinates. The reduction `NCW → NC` reduces the coefficients
`ZMod 8 → ZMod 2`.

Everything 0DZ2 asks of the pair `A' → A` holds, and the one thing the split-base theorem asks
*not* to hold fails: there is no ring homomorphism `NC → NCW` whatsoever, because `2 = 0` in `NC`
while `2 ≠ 0` in `NCW`. The kernel is `(2)`, with `(2)³ = 0` and `(2)² ≠ 0`, so the thickening is
nilpotent and **not** square-zero — which is where the square-zero form of 0DZ2 already proved in
this library stops.

## The obstruction

The mechanism proposed for a counterexample over this base is the solvability of `w² = 1 + 4Y`
in `NCW`. Writing `w = 1 + 2b` gives `w² = 1 + 4(b² + b)`, so that equation holds exactly when
`b̄² + b̄ = Y` in `NC` — the Artin–Schreier obstruction the existing witness turns on. That
equivalence is `Deformation.Examples.ArtinSchreier.exists_sq_eq_iff_exists_isASSol`, and with
`Deformation.Examples.ArtinSchreier.not_isASSol_ncY` it gives
`Deformation.Examples.ArtinSchreier.not_exists_sq_eq_one_add_four_mul_ncwY`: **`1 + 4Y` is not a
square in `NCW`.**

Both directions are proved, and neither is formal. The hard direction needs two facts about the
coordinates: that `1` is the only square root of `1` in `NC`
(`Deformation.Examples.ArtinSchreier.eq_one_of_mul_self_eq_one`, which is what forces `w ≡ 1`
modulo `2` and hence `w = 1 + 2b`), and that an element of `NCW` killed by `4` is divisible by
`2` (`Deformation.Examples.ArtinSchreier.mem_span_two_of_four_mul_eq_zero`, which is freeness of
`NCW` over `ZMod 8` in the only form the argument uses).

## What this file does *not* contain

It does **not** contain a counterexample to
`Deformation.FlatModuleLiftBaseChangeStatementSmooth`. What is missing is a finite `A`-flat
`P`-module whose liftability over a smooth `P'` is *equivalent* to the square root above
existing; over a polynomial `P'` there are no relations to force such an equation, so the
obstruction would have to come from a commutator (relative dimension at least two) or from
non-surjectivity of `End_{A'}(M') → End_A(M)`. See the module documentation of
`StacksFrontier.Deformation.FlatModuleLiftSmoothBaseChange` for what else is forced about such a
module.

## Main definitions

* `Deformation.Examples.ArtinSchreier.NCW`: the thickening
  `(ZMod 8)[Y, Z]/(Z² + Y·Z + Y³)`, as `AdjoinRoot` of a monic quadratic over `(ZMod 8)[Y]`.
* `Deformation.Examples.ArtinSchreier.ncwY`, `Deformation.Examples.ArtinSchreier.ncwZ`: its two
  coordinates.
* `Deformation.Examples.ArtinSchreier.redW`: the reduction `NCW → NC`.

## Main results

* `Deformation.Examples.ArtinSchreier.redW_surjective`,
  `Deformation.Examples.ArtinSchreier.ker_redW`: the reduction is surjective with kernel `(2)`.
* `Deformation.Examples.ArtinSchreier.isNilpotent_ker_redW`,
  `Deformation.Examples.ArtinSchreier.ker_redW_pow_two_ne_bot`: the kernel is nilpotent,
  `(2)³ = 0`, and not square-zero, `(2)² ≠ 0`.
* `Deformation.Examples.ArtinSchreier.not_exists_ringHom_NC_NCW`: **there is no ring
  homomorphism `NC → NCW`**, so in particular `redW` has no ring section and the split-base
  theorem does not apply.
* `Deformation.Examples.ArtinSchreier.exists_sq_eq_iff_exists_isASSol`: `1 + 4Y` is a square in
  `NCW` if and only if the Artin–Schreier class of `Y` dies on `NC`.
* `Deformation.Examples.ArtinSchreier.not_exists_sq_eq_one_add_four_mul_ncwY`: **`1 + 4Y` is not
  a square in `NCW`.**

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
-/

@[expose] public noncomputable section

open Polynomial

namespace Deformation.Examples.ArtinSchreier

/-! ### Reduction of the coefficients -/

/-- `ZMod 8` is non-trivial. -/
private instance : Nontrivial (ZMod 8) := ⟨⟨0, 1, by decide⟩⟩

/-- The coefficient reduction `ZMod 8 → ZMod 2`. -/
def z8To2 : ZMod 8 →+* ZMod 2 := ZMod.castHom (by norm_num) (ZMod 2)

/-- The reduction `ZMod 8 → ZMod 2` is surjective. -/
theorem z8To2_surjective : Function.Surjective z8To2 := by decide

/-- The kernel of `ZMod 8 → ZMod 2` is `(2)`. -/
theorem ker_z8To2 : RingHom.ker z8To2 = Ideal.span {(2 : ZMod 8)} := by
  ext x
  rw [RingHom.mem_ker, Ideal.mem_span_singleton']
  revert x
  decide

/-- `4·c = 0` forces `c` even, in `ZMod 8`. -/
theorem z8To2_eq_zero_of_four_mul_eq_zero {c : ZMod 8} (h : 4 * c = 0) : z8To2 c = 0 := by
  revert h
  revert c
  decide

/-- The coefficient reduction `(ZMod 8)[Y] → 𝔽₂[Y]`. -/
def redCoeff : Polynomial (ZMod 8) →+* Polynomial (ZMod 2) := Polynomial.mapRingHom z8To2

/-- The coefficient reduction sends `Y` to `Y`. -/
@[simp] theorem redCoeff_X : redCoeff X = X := by simp [redCoeff]

/-- The coefficient reduction `(ZMod 8)[Y] → 𝔽₂[Y]` is surjective. -/
theorem redCoeff_surjective : Function.Surjective redCoeff :=
  Polynomial.map_surjective _ z8To2_surjective

/-- The kernel of the coefficient reduction `(ZMod 8)[Y] → 𝔽₂[Y]` is `(2)`. -/
theorem ker_redCoeff : RingHom.ker redCoeff = Ideal.span {(2 : Polynomial (ZMod 8))} := by
  have h : RingHom.ker redCoeff = (Ideal.span {(2 : ZMod 8)}).map (Polynomial.C) := by
    rw [redCoeff, Polynomial.ker_mapRingHom, ker_z8To2]
  rw [h, Ideal.map_span, Set.image_singleton, map_ofNat]

/-- **An element of `(ZMod 8)[Y]` killed by `4` is divisible by `2`.** Coefficientwise this is
the corresponding statement in `ZMod 8`. -/
theorem mem_span_two_of_four_mul_eq_zero_coeff {a : Polynomial (ZMod 8)} (h : 4 * a = 0) :
    a ∈ Ideal.span {(2 : Polynomial (ZMod 8))} := by
  rw [← ker_redCoeff, RingHom.mem_ker]
  refine Polynomial.ext fun n => ?_
  have hc : 4 * a.coeff n = 0 := by
    have := congrArg (fun p => Polynomial.coeff p n) h
    simpa [show (4 : Polynomial (ZMod 8)) = Polynomial.C 4 from (map_ofNat _ 4).symm,
      Polynomial.coeff_C_mul] using this
  rw [redCoeff, Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.coeff_zero]
  exact z8To2_eq_zero_of_four_mul_eq_zero hc

/-! ### The thickened nodal cubic -/

/-- The defining equation `Z² + Y·Z + Y³` of the thickened nodal cubic, as a monic quadratic in
`Z` over `(ZMod 8)[Y]`. -/
def ncwPoly : Polynomial (Polynomial (ZMod 8)) := X ^ 2 + (C X * X + C X ^ 3)

/-- The polynomial `ncwPoly` is monic in `Z`. -/
theorem ncwPoly_monic : ncwPoly.Monic := by
  refine Polynomial.monic_X_pow_add (n := 2) ?_
  refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) ?_
  refine max_lt (lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_) ?_
  · refine lt_of_le_of_lt (add_le_add Polynomial.degree_C_le Polynomial.degree_X_le) ?_
    norm_num
  · rw [← map_pow]
    exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)

/-- The polynomial `ncwPoly` has degree two in `Z`. -/
theorem natDegree_ncwPoly : ncwPoly.natDegree = 2 := by
  have h : (C X * X + C X ^ 3 : Polynomial (Polynomial (ZMod 8))).natDegree < 2 := by
    refine lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) ?_
    refine max_lt (lt_of_le_of_lt (Polynomial.natDegree_mul_le) ?_) ?_
    · rw [Polynomial.natDegree_C, Polynomial.natDegree_X]
      omega
    · rw [← map_pow, Polynomial.natDegree_C]
      omega
  rw [ncwPoly, Polynomial.natDegree_add_eq_left_of_natDegree_lt
    (by rwa [Polynomial.natDegree_X_pow]), Polynomial.natDegree_X_pow]

/-- **The `ZMod 8`-thickening of the nodal cubic**, `(ZMod 8)[Y, Z]/(Z² + Y·Z + Y³)`, presented
as `(ZMod 8)[Y][Z]/(Z² + Y·Z + Y³)` so that it is visibly free of rank two over `(ZMod 8)[Y]`. -/
abbrev NCW : Type := AdjoinRoot ncwPoly

/-- The coefficient inclusion `(ZMod 8)[Y] → NCW`. -/
def ncwFromY : Polynomial (ZMod 8) →+* NCW := AdjoinRoot.of ncwPoly

/-- `Z` in the thickened nodal cubic. -/
def ncwZ : NCW := AdjoinRoot.root ncwPoly

/-- `Y` in the thickened nodal cubic. -/
def ncwY : NCW := ncwFromY X

/-- **The defining relation**, as an identity in `NCW`. -/
theorem ncwRel : ncwZ * ncwZ + ncwY * ncwZ + ncwY ^ 3 = 0 := by
  have hcomb : ncwZ * ncwZ + ncwY * ncwZ + ncwY ^ 3
      = AdjoinRoot.mk ncwPoly (X * X + C X * X + C X ^ 3) := by
    rw [map_add, map_add, map_mul, map_mul, map_pow]
    rfl
  rw [hcomb, AdjoinRoot.mk_eq_zero]
  exact ⟨1, by rw [ncwPoly]; ring⟩

/-- The defining relation, solved for `Z²`. -/
theorem ncwZ_mul_ncwZ : ncwZ * ncwZ = -ncwY ^ 3 - ncwY * ncwZ := by
  linear_combination ncwRel

/-- The image of `a` under `ncwFromY` is the class of the constant polynomial `a`. -/
theorem ncwFromY_mk (a : Polynomial (ZMod 8)) :
    ncwFromY a = AdjoinRoot.mk ncwPoly (Polynomial.C a) := rfl

/-! ### Coordinates on the thickening -/

/-- **`1` and `Z` span `NCW` over `(ZMod 8)[Y]`.** -/
theorem exists_ncwFromY_repr (x : NCW) :
    ∃ a b : Polynomial (ZMod 8), x = ncwFromY a + ncwFromY b * ncwZ := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective (g := ncwPoly) x
  induction f using Polynomial.induction_on with
  | C a => exact ⟨a, 0, by rw [ncwFromY_mk, map_zero, zero_mul, add_zero]⟩
  | add p q hp hq =>
      obtain ⟨a₁, b₁, h₁⟩ := hp
      obtain ⟨a₂, b₂, h₂⟩ := hq
      refine ⟨a₁ + a₂, b₁ + b₂, ?_⟩
      rw [map_add, h₁, h₂, map_add, map_add]
      ring
  | monomial n a hn =>
      obtain ⟨a', b', h⟩ := hn
      refine ⟨-(b' * X ^ 3), a' - b' * X, ?_⟩
      have hstep : AdjoinRoot.mk ncwPoly (Polynomial.C a * Polynomial.X ^ (n + 1)) =
          AdjoinRoot.mk ncwPoly (Polynomial.C a * Polynomial.X ^ n) * ncwZ := by
        rw [ncwZ, ← AdjoinRoot.mk_X, ← map_mul]
        ring_nf
      rw [hstep, h, map_neg, map_mul, map_pow, map_sub, map_mul, show ncwFromY X = ncwY from rfl]
      linear_combination (ncwFromY b') * ncwZ_mul_ncwZ

/-- **`1` and `Z` are independent over `(ZMod 8)[Y]`.** A relation `a(Y) + b(Y)·Z = 0` lifts to a
polynomial of degree at most one divisible by the monic quadratic `ncwPoly`, hence to the zero
polynomial. -/
theorem eq_zero_of_ncwFromY_add {a b : Polynomial (ZMod 8)}
    (h : ncwFromY a + ncwFromY b * ncwZ = 0) : a = 0 ∧ b = 0 := by
  have h1 : AdjoinRoot.mk ncwPoly (Polynomial.C a + Polynomial.C b * Polynomial.X) = 0 := by
    rw [map_add, map_mul, AdjoinRoot.mk_X, ← ncwFromY_mk, ← ncwFromY_mk]
    exact h
  rw [AdjoinRoot.mk_eq_zero] at h1
  by_cases hz : Polynomial.C a + Polynomial.C b * Polynomial.X = 0
  · refine ⟨?_, ?_⟩
    · have := congrArg (fun p => Polynomial.coeff p 0) hz
      simpa using this
    · have := congrArg (fun p => Polynomial.coeff p 1) hz
      simpa using this
  · exfalso
    have hle := ncwPoly_monic.natDegree_le_of_dvd hz h1
    have hb : (Polynomial.C a + Polynomial.C b * Polynomial.X).natDegree ≤ 1 := by
      refine le_trans (Polynomial.natDegree_add_le _ _) ?_
      refine max_le ?_ ?_
      · rw [Polynomial.natDegree_C]; omega
      · refine le_trans Polynomial.natDegree_mul_le ?_
        rw [Polynomial.natDegree_C, Polynomial.natDegree_X]
    rw [natDegree_ncwPoly] at hle
    omega

/-- An element `a + b·Z` of `NCW` with both coordinates divisible by `2` is divisible by `2`. -/
private theorem ncwFromY_add_mul_mem_span_two {a b : Polynomial (ZMod 8)}
    (ha : a ∈ Ideal.span {(2 : Polynomial (ZMod 8))})
    (hb : b ∈ Ideal.span {(2 : Polynomial (ZMod 8))}) :
    ncwFromY a + ncwFromY b * ncwZ ∈ Ideal.span {(2 : NCW)} := by
  obtain ⟨a', rfl⟩ := Ideal.mem_span_singleton'.mp ha
  obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton'.mp hb
  refine Ideal.mem_span_singleton'.mpr ⟨ncwFromY a' + ncwFromY b' * ncwZ, ?_⟩
  simp only [map_mul, map_ofNat]
  ring

/-- **An element of `NCW` killed by `4` is divisible by `2`.** This is freeness of `NCW` over
`ZMod 8` in the only form the Artin–Schreier computation uses: in coordinates `4` kills each of
the two coefficients, and `mem_span_two_of_four_mul_eq_zero_coeff` divides each by `2`. -/
theorem mem_span_two_of_four_mul_eq_zero {x : NCW} (h : 4 * x = 0) :
    x ∈ Ideal.span {(2 : NCW)} := by
  obtain ⟨a, b, rfl⟩ := exists_ncwFromY_repr x
  have hexp : ncwFromY (4 * a) + ncwFromY (4 * b) * ncwZ = 0 := by
    simp only [map_mul, map_ofNat]
    linear_combination h
  obtain ⟨h1, h2⟩ := eq_zero_of_ncwFromY_add hexp
  exact ncwFromY_add_mul_mem_span_two (mem_span_two_of_four_mul_eq_zero_coeff h1)
    (mem_span_two_of_four_mul_eq_zero_coeff h2)

/-! ### Elementary non-degeneracy -/

/-- A nonzero constant of `ZMod 8` stays nonzero in `NCW`. -/
private theorem ncwFromY_C_ne_zero {c : ZMod 8} (hc : c ≠ 0) : ncwFromY (Polynomial.C c) ≠ 0 := by
  intro h
  have h0 : ncwFromY (Polynomial.C c) + ncwFromY 0 * ncwZ = 0 := by
    rw [map_zero, zero_mul, add_zero]
    exact h
  have := congrArg (fun p => Polynomial.coeff p 0) (eq_zero_of_ncwFromY_add h0).1
  simp only [Polynomial.coeff_C_zero, Polynomial.coeff_zero] at this
  exact hc this

/-- `2 ≠ 0` in `NCW`. -/
theorem two_ncw_ne_zero : (2 : NCW) ≠ 0 := by
  have := ncwFromY_C_ne_zero (c := (2 : ZMod 8)) (by decide)
  rwa [map_ofNat, map_ofNat] at this

/-- `4 ≠ 0` in `NCW`. -/
theorem four_ncw_ne_zero : (4 : NCW) ≠ 0 := by
  have := ncwFromY_C_ne_zero (c := (4 : ZMod 8)) (by decide)
  rwa [map_ofNat, map_ofNat] at this

/-- `8 = 0` in `NCW`. -/
theorem eight_ncw_eq_zero : (8 : NCW) = 0 := by
  have h8 : (8 : Polynomial (ZMod 8)) = 0 := by
    have : (8 : ZMod 8) = 0 := by decide
    rw [show (8 : Polynomial (ZMod 8)) = Polynomial.C 8 from (map_ofNat _ 8).symm, this,
      map_zero]
  rw [← map_ofNat ncwFromY 8, h8, map_zero]

/-- `NCW` is a nontrivial ring. -/
instance : Nontrivial NCW :=
  ⟨⟨2, 0, two_ncw_ne_zero⟩⟩

/-- `NCW` is a Noetherian ring. -/
theorem isNoetherianRing_NCW : IsNoetherianRing NCW := by
  change IsNoetherianRing (Polynomial (Polynomial (ZMod 8)) ⧸ Ideal.span {ncwPoly})
  infer_instance

/-! ### The reduction to the nodal cubic -/

/-- The reduction `(ZMod 8)[Y] → NC` of the coefficient ring. -/
def redWCoeff : Polynomial (ZMod 8) →+* NC := ncFromY.comp redCoeff

/-- `redWCoeff` is the coefficient reduction followed by `ncFromY`. -/
theorem redWCoeff_apply (a : Polynomial (ZMod 8)) : redWCoeff a = ncFromY (redCoeff a) := rfl

/-- `redWCoeff` sends `Y` to `ncY`. -/
@[simp] theorem redWCoeff_X : redWCoeff X = ncY := by
  rw [redWCoeff_apply, redCoeff_X, ncFromY_X]

/-- **The reduction `NCW → NC`**, reducing the coefficients `ZMod 8 → ZMod 2`. -/
def redW : NCW →+* NC :=
  AdjoinRoot.lift (f := ncwPoly) redWCoeff ncZ (by
    rw [ncwPoly]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, redWCoeff_X]
    linear_combination ncRel)

/-- The reduction sends `Z` to `ncZ`. -/
@[simp] theorem redW_ncwZ : redW ncwZ = ncZ := AdjoinRoot.lift_root _

/-- The reduction restricted to `(ZMod 8)[Y]` is `redWCoeff`. -/
@[simp] theorem redW_ncwFromY (a : Polynomial (ZMod 8)) : redW (ncwFromY a) = redWCoeff a := by
  rw [ncwFromY_mk, redW, AdjoinRoot.lift_mk, Polynomial.eval₂_C]

/-- The reduction sends `Y` to `ncY`. -/
@[simp] theorem redW_ncwY : redW ncwY = ncY := by rw [ncwY, redW_ncwFromY, redWCoeff_X]

/-- The reduction `NCW → NC` is surjective. -/
theorem redW_surjective : Function.Surjective redW := by
  intro u
  obtain ⟨a, b, rfl⟩ := exists_ncFromY_repr u
  obtain ⟨a', ha'⟩ := redCoeff_surjective a
  obtain ⟨b', hb'⟩ := redCoeff_surjective b
  refine ⟨ncwFromY a' + ncwFromY b' * ncwZ, ?_⟩
  rw [map_add, map_mul, redW_ncwFromY, redW_ncwFromY, redW_ncwZ, redWCoeff_apply,
    redWCoeff_apply, ha', hb']

/-- **The kernel of the reduction is `(2)`.** One inclusion is `2 = 0` in `NC`; the other reads
a kernel element in coordinates and divides each coefficient by `2`, which is
`Deformation.Examples.ArtinSchreier.ker_redCoeff` after
`Deformation.Examples.ArtinSchreier.eq_zero_of_ncFromY_add` has separated the two coordinates. -/
theorem ker_redW : RingHom.ker redW = Ideal.span {(2 : NCW)} := by
  refine le_antisymm (fun x hx => ?_) ?_
  · obtain ⟨a, b, rfl⟩ := exists_ncwFromY_repr x
    rw [RingHom.mem_ker, map_add, map_mul, redW_ncwFromY, redW_ncwFromY, redW_ncwZ,
      redWCoeff_apply, redWCoeff_apply] at hx
    obtain ⟨h1, h2⟩ := eq_zero_of_ncFromY_add hx
    exact ncwFromY_add_mul_mem_span_two (by rwa [← ker_redCoeff, RingHom.mem_ker])
      (by rwa [← ker_redCoeff, RingHom.mem_ker])
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      map_ofNat]
    exact two_eq_zero_nc

/-- **The thickening is nilpotent**: `(2)³ = 0`, because `8 = 0` in `NCW`. -/
theorem isNilpotent_ker_redW : IsNilpotent (RingHom.ker redW) := by
  refine ⟨3, ?_⟩
  rw [ker_redW, Ideal.span_singleton_pow]
  rw [show (2 : NCW) ^ 3 = 8 from by norm_num, eight_ncw_eq_zero]
  exact Ideal.span_zero

/-- **The thickening is not square-zero**: `(2)² = (4) ≠ 0`. This is what puts the base one step
past the square-zero form of 0DZ2, which is already proved in this library. -/
theorem ker_redW_pow_two_ne_bot : (RingHom.ker redW) ^ 2 ≠ ⊥ := by
  rw [ker_redW, Ideal.span_singleton_pow, Ne, Ideal.span_singleton_eq_bot]
  rw [show (2 : NCW) ^ 2 = 4 from by norm_num]
  exact four_ncw_ne_zero

/-- **There is no ring homomorphism from the nodal cubic to its `ZMod 8`-thickening**, because
`2 = 0` in `NC` and `2 ≠ 0` in `NCW`. In particular `redW` admits no ring section, so
`Deformation.exists_flatModuleLift_iff_baseChange_of_ringHom_section` — the theorem that proves
the smooth form of 0DZ2 over a split base — does not apply to this base. That is exactly the
property the nodal-cubic refutation of the general statement lacks. -/
theorem not_exists_ringHom_NC_NCW : ¬ ∃ _ : NC →+* NCW, True := by
  rintro ⟨s, -⟩
  have h1 : s (2 : NC) = (2 : NCW) := map_ofNat s 2
  rw [two_eq_zero_nc, map_zero] at h1
  exact two_ncw_ne_zero h1.symm

/-- `redW` has no ring section. -/
theorem not_exists_ringHom_section : ¬ ∃ s : NC →+* NCW, ∀ a : NC, redW (s a) = a := by
  rintro ⟨s, -⟩
  exact not_exists_ringHom_NC_NCW ⟨s, trivial⟩

/-! ### The square root of `1 + 4Y` -/

/-- A square root of `1 + 4Y` in `NCW` yields a solution of the Artin–Schreier equation for `Y`
on the nodal cubic. -/
theorem exists_isASSol_of_mul_self_eq {w : NCW} (hw : w * w = 1 + 4 * ncwY) :
    ∃ b : NC, IsASSol ncY b := by
  have hu : redW w * redW w = 1 := by
    have h4 : (4 : NC) = 0 := by linear_combination 2 * two_eq_zero_nc
    have := congrArg redW hw
    rwa [map_mul, map_add, map_mul, map_one, map_ofNat, redW_ncwY, h4, zero_mul, add_zero] at this
  have h1 : redW (w - 1) = 0 := by
    rw [map_sub, map_one, eq_one_of_mul_self_eq_one hu, sub_self]
  obtain ⟨β, hβ⟩ := Ideal.mem_span_singleton'.mp (by rwa [← ker_redW, RingHom.mem_ker])
  have hwβ : w = 1 + 2 * β := by linear_combination -hβ
  have hkey : 4 * (β * β + β - ncwY) = 0 := by
    rw [hwβ] at hw
    linear_combination hw
  obtain ⟨γ, hγ⟩ := Ideal.mem_span_singleton'.mp (mem_span_two_of_four_mul_eq_zero hkey)
  refine ⟨redW β, ?_⟩
  have := congrArg redW hγ
  rw [map_mul, map_ofNat, map_sub, map_add, map_mul, redW_ncwY] at this
  unfold IsASSol
  linear_combination -this + redW γ * two_eq_zero_nc

/-- A solution of the Artin–Schreier equation for `Y` on the nodal cubic lifts to a square root
of `1 + 4Y` in `NCW`. -/
theorem exists_mul_self_eq_of_isASSol {b : NC} (hb : IsASSol ncY b) :
    ∃ w : NCW, w * w = 1 + 4 * ncwY := by
  obtain ⟨β, hβ⟩ := redW_surjective b
  have h0 : redW (β * β + β - ncwY) = 0 := by
    rw [map_sub, map_add, map_mul, redW_ncwY, hβ]
    unfold IsASSol at hb
    linear_combination hb
  obtain ⟨γ, hγ⟩ := Ideal.mem_span_singleton'.mp (by rwa [← ker_redW, RingHom.mem_ker])
  refine ⟨1 + 2 * β, ?_⟩
  linear_combination -4 * hγ + γ * eight_ncw_eq_zero

/-- **`1 + 4Y` is a square in `NCW` if and only if the Artin–Schreier class of `Y` dies on the
nodal cubic.**

Writing `w = 1 + 2b` turns `w² = 1 + 4Y` into `4(b² + b) = 4Y`, which is `b̄² + b̄ = Y` in
`NC = NCW/(2)`; and conversely any solution of the Artin–Schreier equation lifts to such a `w`.

Neither direction is formal. The forward one uses that `1` is the only square root of `1` in
`NC` (`Deformation.Examples.ArtinSchreier.eq_one_of_mul_self_eq_one`), which is what forces
`w ≡ 1 mod 2` and hence the shape `w = 1 + 2b`, and that an element of `NCW` killed by `4` is
divisible by `2` (`Deformation.Examples.ArtinSchreier.mem_span_two_of_four_mul_eq_zero`), which
is what turns `4(b² + b - Y) = 0` into a congruence modulo `2`. The reverse one uses `8 = 0`. -/
theorem exists_sq_eq_iff_exists_isASSol :
    (∃ w : NCW, w * w = 1 + 4 * ncwY) ↔ (∃ b : NC, IsASSol ncY b) :=
  ⟨fun ⟨_, hw⟩ => exists_isASSol_of_mul_self_eq hw,
    fun ⟨_, hb⟩ => exists_mul_self_eq_of_isASSol hb⟩

/-- **`1 + 4Y` is not a square in the `ZMod 8`-thickening of the nodal cubic.** By
`Deformation.Examples.ArtinSchreier.exists_sq_eq_iff_exists_isASSol` this is
`Deformation.Examples.ArtinSchreier.not_isASSol_ncY`, the Artin–Schreier class of `Y` surviving
on the nodal cubic. -/
theorem not_exists_sq_eq_one_add_four_mul_ncwY : ¬ ∃ w : NCW, w * w = 1 + 4 * ncwY := fun h =>
  not_isASSol_ncY (exists_sq_eq_iff_exists_isASSol.mp h)

end Deformation.Examples.ArtinSchreier

end
