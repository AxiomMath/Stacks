module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.ProjectiveLine
public import StacksFrontier.AlgebraicGeometry.Curves.PlaneCurveGenus
public import StacksFrontier.AlgebraicGeometry.Curves.PlaneCurveIrreducibleEquation
public import StacksFrontier.FieldTheory.RatFuncIntDegree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The genus changes under a purely inseparable morphism

[Stacks, Tag 0CD1] is the example showing that **the genus is not preserved by a purely
inseparable morphism of nonsingular projective curves**. Let `k` be a field of characteristic
three containing an element `a` which is not a cube — the source suggests `k = 𝐅₃(a)` — and let
`X ⊆ 𝐏²_k` be the plane curve

```
F = T₁² T₀ - T₂³ + a T₀³ .
```

On `D₊(T₀)`, in the coordinates `x = T₁/T₀` and `y = T₂/T₀`, this is `x² - y³ + a = 0`, a
nonsingular affine curve; the point at infinity `(0 : 1 : 0)` is smooth as well, so `X` is a
nonsingular projective curve, of genus `1` by the degree formula of [Stacks, Tag 0BYD]. The
projection `f : X ⟶ 𝐏¹_k` sending `(x, y)` to `x` is then a morphism of proper nonsingular
curves over `k` inducing an **inseparable extension of function fields of degree `p = 3`**,
while the genus of `X` is `1` and the genus of `𝐏¹_k` is `0`.

(The source originally projected to the `y` coordinate; the 2022 erratum corrects this to the
`x` coordinate, and that is the morphism formalized here — the degree-three inseparable
extension is `k(x) ⊆ k(x)(y)` with `y³ = x² + a`.)

## What is proved here

Both genus values are **proved**, not assumed, and the example assumes no input beyond its own
data.

The statements below take the curve itself as input: a scheme `Z`, a closed immersion into
`𝐏²_k`, and the hypotheses that `Z` is nonempty, equidimensional of dimension one, without
embedded points, and cut out by `F`. That input is **constructed**, not merely hypothesised, in
`StacksFrontier/AlgebraicGeometry/Curves/InseparableGenusChangeCurve.lean` and
`StacksFrontier/AlgebraicGeometry/Curves/InseparableGenusChangeCurveDimension.lean`, at
`Z = Proj (k[T₀, T₁, T₂] ⧸ (F))`; all six hypotheses are discharged there. The example in one
statement, at that curve and for the projection `f` and the extension of function fields it
induces, is `Stacks.Curves.InseparableGenus.planeCubicProjection_inseparable_genus_change`, in
`StacksFrontier/AlgebraicGeometry/Curves/InseparableGenusChangeProperCurves.lean`.

* `genus X = 1` is the plane-curve genus formula of [Stacks, Tag 0BYD],
  `AlgebraicGeometry.ProjectiveSpectrum.Proj.genus_planeCurve`, applied to `Z` with the equation
  `F` of degree three: `(3 - 1)(3 - 2)/2 = 1`. Packaging `Z` and `F` as the plane-curve data that
  formula takes is `planeCubicData`.
* `genus 𝐏¹_k = 0` is `Stacks.Curves.genus_projToSpecCoeff_one`, which reads the
  vanishing `H¹(𝐏¹_k, 𝒪) = 0` of [Stacks, Tag 01XT] into the definition of the genus.

Everything else is proved: that the equation is homogeneous of degree three and irreducible, so
that `X` really is a curve over `k` by [Stacks, Tag 0BYC]; that the non-cube condition on `a` is
*exactly* what makes the fibre polynomial `y³ - a` of the affine equation squarefree, which is
the nonsingularity input; that the function field extension cut out by the `x`-projection is
purely inseparable of degree three; and that the hypotheses are satisfiable, by exhibiting
`𝐅₃(a)` with `a` the indeterminate.

## Main definitions

* `Stacks.Curves.InseparableGenus.planeCubic`: the homogeneous equation
  `F = T₁²T₀ - T₂³ + aT₀³`.
* `Stacks.Curves.InseparableGenus.cubicChart`: `F` read as a cubic in `T₂` over `k[T₀, T₁]`.
* `Stacks.Curves.InseparableGenus.curveFunctionField`: the function field `k(x)[y]/(y³ - x² - a)`
  of the curve, as an extension of the function field `k(x)` of the projective line.
* `Stacks.Curves.InseparableGenus.planeCubicData`: the curve together with its cubic equation, as
  the plane-curve data that the genus formula of [Stacks, Tag 0BYD] takes.

## Main results

* `Stacks.Curves.InseparableGenus.exists_charThree_notCube`: **the example is not vacuous** —
  a field of characteristic three with an element that is not a cube exists, namely `𝐅₃(a)`.
* `Stacks.Curves.InseparableGenus.squarefree_X_pow_three_sub_C_iff_forall_pow_ne`: the non-cube
  condition on `a` holds exactly when the fibre polynomial `y³ - a` is squarefree.
* `Stacks.Curves.InseparableGenus.planeCubic_irreducible`: `F` is irreducible.
* `Stacks.Curves.InseparableGenus.isPurelyInseparable_and_finrank_curveFunctionField`: the
  `x`-projection induces a purely inseparable extension of function fields of degree three.
* `Stacks.Curves.InseparableGenus.genus_planeCubic_eq_one`: the genus of `X` is `1`, from
  [Stacks, Tag 0BYD] at `deg F = 3`.
* `Stacks.Curves.InseparableGenus.isCurve_and_genus_ne_genus_projectiveLine`: **[Stacks, Tag
  0CD1]** — `X` is a curve over `k`, its genus is `1`, the genus of `𝐏¹_k` is `0`, these differ,
  and the function field extension is purely inseparable of degree three.

## Implementation notes

**The function field.** `X` is covered by `D₊(T₀)`, on which it is `x² - y³ + a = 0`; its
function field is therefore `k(x)` adjoined a cube root of `x² + a`, and the morphism `f` to
`𝐏¹_k` is precisely the inclusion of `k(x)`. That extension is modelled here as
`AdjoinRoot (Y³ - (x² + a))` over `RatFunc k`, which is the function field of the curve together
with the embedding `f` induces, so the degree and the inseparability are statements about the
extension the source names. The irreducibility of `Y³ - (x² + a)` over `k(x)` holds for every
`a`, by a degree count: `x² + a` has `x`-degree two, which is not a multiple of three.

**Nonsingularity.** Regularity of `X` as a scheme is not available: it would need the local rings
of the plane cubic, which this repository does not compute. What *is* proved is the input the
source uses, in the sharpest form — the affine equation is `x² = y³ - a`, a quadratic extension
of `k[y]` in characteristic three (so `2 ≠ 0`), and such an extension is nonsingular exactly when
`y³ - a` is squarefree, which by
`squarefree_X_pow_three_sub_C_iff_forall_pow_ne` happens exactly when `a` is not a cube. If `a`
were a cube, `y³ - a = (y - b)³` and the curve would acquire a cusp; that is why the hypothesis
is there.

**The two genus values are computed, not posited.** The value `1` comes out of the general
degree formula of [Stacks, Tag 0BYD] at `deg F = 3`, and the value `0` comes out of the
vanishing of `H¹(𝐏¹_k, 𝒪)`; neither is written into a hypothesis. `𝐏¹_k` is not a plane curve
in `𝐏²_k`, so the second one is a separate computation, carried out in
`StacksFrontier/AlgebraicGeometry/Curves/GenusCurve/ProjectiveLine.lean`.

## References

* [Stacks Project, Tag 0CD1](https://stacks.math.columbia.edu/tag/0CD1)
* [Stacks Project, Tag 0BYD](https://stacks.math.columbia.edu/tag/0BYD)
* [Stacks Project, Tag 0BYC](https://stacks.math.columbia.edu/tag/0BYC)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff)
open Stacks.AlgebraicGeometry.IdealOfClosedSubscheme (idealOfClosedSubscheme)
open Stacks.ProjectiveSpace.Cohomology (twistCohomology)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (PlaneCurveData genus_planeCurve)

universe u v

namespace Stacks.Curves.InseparableGenus

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Elements of `k(x)` that are not cubes -/

/-- **A polynomial whose degree is not divisible by `n` is not an `n`-th power in `k(x)`.** The
`intDegree` of a rational function is additive, hence multiplies by `n` on `n`-th powers, while
on a polynomial it is the degree. -/
theorem not_pow_algebraMap_of_not_dvd_natDegree {k : Type u} [Field k] {n : ℕ}
    {p : Polynomial k} (hn : ¬ (n : ℤ) ∣ (p.natDegree : ℤ)) (b : RatFunc k) :
    b ^ n ≠ algebraMap (Polynomial k) (RatFunc k) p := by
  intro h
  have hd := congrArg RatFunc.intDegree h
  rw [ratFunc_intDegree_pow, RatFunc.intDegree_polynomial] at hd
  exact hn ⟨b.intDegree, hd.symm⟩

/-- **`x² + a` is not a cube in `k(x)`, for any `a`.** Its `x`-degree is two, which is not a
multiple of three. This is what makes the cubic `Y³ - (x² + a)` irreducible over `k(x)`. -/
theorem ratFuncX_sq_add_C_not_cube {k : Type u} [Field k] (a : k) (b : RatFunc k) :
    b ^ 3 ≠ RatFunc.X ^ 2 + RatFunc.C a := by
  have hmap : algebraMap (Polynomial k) (RatFunc k) (Polynomial.X ^ 2 + Polynomial.C a) =
      RatFunc.X ^ 2 + RatFunc.C a := by
    rw [map_add, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  rw [← hmap]
  exact not_pow_algebraMap_of_not_dvd_natDegree
    (by rw [Polynomial.natDegree_X_pow_add_C]; decide) b

/-- **The indeterminate of `𝐅₃(a)` is not a cube.** Its degree is one, which is not a multiple of
three. -/
theorem zmodThree_ratFuncX_not_cube (b : RatFunc (ZMod 3)) : b ^ 3 ≠ RatFunc.X := by
  rw [← RatFunc.algebraMap_X]
  exact not_pow_algebraMap_of_not_dvd_natDegree
    (by rw [Polynomial.natDegree_X]; decide) b

/-- **The hypotheses of [Stacks, Tag 0CD1] are satisfiable: `𝐅₃(a)` works.** There is a field of
characteristic three, in any universe, carrying an element which is not a cube. -/
@[stacks 0CD1 "the example's remark that k = 𝐅₃(a) works: a field of characteristic three with \
an element that is not a cube"]
theorem exists_charThree_notCube :
    ∃ (K : Type u) (_ : Field K), CharP K 3 ∧ ∃ a : K, ∀ b : K, b ^ 3 ≠ a := by
  refine ⟨ULift.{u} (RatFunc (ZMod 3)), inferInstance, inferInstance,
    ULift.up RatFunc.X, fun b hb => ?_⟩
  refine zmodThree_ratFuncX_not_cube (ULift.ringEquiv b) ?_
  rw [← map_pow, hb]
  rfl

/-! ### The non-cube condition is exactly squarefreeness of the fibre polynomial -/

/-- **The nonsingularity input of the example.** The affine equation `x² - y³ + a = 0` presents
the curve as the quadratic extension `x² = y³ - a` of the `y`-line, which is nonsingular exactly
when the fibre polynomial `y³ - a` is squarefree; in characteristic three that happens exactly
when `a` is not a cube. If `a = b³` then `y³ - a = (y - b)³` and the curve acquires a cusp. -/
theorem squarefree_X_pow_three_sub_C_iff_forall_pow_ne {k : Type u} [Field k] [ExpChar k 3]
    (a : k) :
    Squarefree (Polynomial.X ^ 3 - Polynomial.C a : Polynomial k) ↔ ∀ b : k, b ^ 3 ≠ a := by
  refine ⟨fun hsq b hb => ?_, fun ha =>
    (X_pow_sub_C_irreducible_of_prime Nat.prime_three ha).squarefree⟩
  have hfac : (Polynomial.X ^ 3 - Polynomial.C a : Polynomial k) =
      (Polynomial.X - Polynomial.C b) ^ 3 := by
    rw [← hb, map_pow, sub_pow_expChar]
  exact Polynomial.not_isUnit_X_sub_C b
    (hsq _ ⟨Polynomial.X - Polynomial.C b, by rw [hfac]; ring⟩)

/-! ### The equation of the plane curve -/

/-- **The homogeneous equation of [Stacks, Tag 0CD1]**, `F = T₁²T₀ - T₂³ + aT₀³`. -/
def planeCubic (k : Type u) [CommRing k] (a : k) : MvPolynomial (Fin 3) k :=
  MvPolynomial.X 1 ^ 2 * MvPolynomial.X 0 - MvPolynomial.X 2 ^ 3 +
    MvPolynomial.C a * MvPolynomial.X 0 ^ 3

/-- The equation is homogeneous of degree three. -/
theorem planeCubic_isHomogeneous (k : Type u) [CommRing k] (a : k) :
    (planeCubic k a).IsHomogeneous 3 :=
  (((MvPolynomial.isHomogeneous_X_pow (R := k) 1 2).mul
      (MvPolynomial.isHomogeneous_X (R := k) 0)).sub
    (MvPolynomial.isHomogeneous_X_pow (R := k) 2 3)).add
      ((MvPolynomial.isHomogeneous_X_pow (R := k) 0 3).C_mul a)

/-- The equation is nonzero: it takes the value `-1` at `(0 : 0 : 1)`. -/
theorem planeCubic_ne_zero (k : Type u) [CommRing k] [Nontrivial k] (a : k) :
    planeCubic k a ≠ 0 := by
  intro h
  simpa [planeCubic] using
    congrArg (MvPolynomial.eval fun j : Fin 3 => if j = 2 then (1 : k) else 0) h

/-- The equation has total degree three; this is the `d` of the genus formula. -/
theorem planeCubic_totalDegree (k : Type u) [CommRing k] [Nontrivial k] (a : k) :
    (planeCubic k a).totalDegree = 3 :=
  (planeCubic_isHomogeneous k a).totalDegree (planeCubic_ne_zero k a)

/-! ### Irreducibility of the equation -/

/-- **Eisenstein at a prime dividing the constant term exactly once.** If `p` is prime, `p ∣ c`
and `p² ∤ c`, then `Y ^ n - c` is irreducible. -/
theorem irreducible_X_pow_sub_C_of_prime_dvd_notDvd_sq
    {R : Type u} [CommRing R] [IsDomain R] {p c : R}
    (hp : Prime p) (hdvd : p ∣ c) (hsq : ¬ p ^ 2 ∣ c) {n : ℕ} (hn : 0 < n) :
    Irreducible (Polynomial.X ^ n - Polynomial.C c) := by
  have hm : (Polynomial.X ^ n - Polynomial.C c).Monic := Polynomial.monic_X_pow_sub_C c hn.ne'
  refine Polynomial.IsEisensteinAt.irreducible (𝓟 := Ideal.span {p}) ?_
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp) hm.isPrimitive (by simpa using hn)
  refine hm.isEisensteinAt_of_mem_of_notMem
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).ne_top ?_ ?_
  · intro m hmn
    rw [Polynomial.natDegree_X_pow_sub_C] at hmn
    rcases eq_or_ne m 0 with rfl | hm0
    · simpa [Polynomial.coeff_X_pow, hn.ne', hn.ne, Ideal.mem_span_singleton]
        using dvd_neg.mpr hdvd
    · simp [Polynomial.coeff_X_pow, Nat.ne_of_lt hmn, Polynomial.coeff_C, hm0]
  · simpa [Ideal.span_singleton_pow, Polynomial.coeff_X_pow, hn.ne', hn.ne,
      Ideal.mem_span_singleton]
      using (not_congr (dvd_neg : p ^ 2 ∣ -c ↔ p ^ 2 ∣ c)).mpr hsq

/-- The constant term of the equation read as a cubic in `T₂`, namely `T₀²T₁ + aT₁³` after the
reindexing of `cubicChart`. -/
def planeCubicCoefficient (k : Type u) [CommRing k] (a : k) : MvPolynomial (Fin 2) k :=
  MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 + MvPolynomial.C a * MvPolynomial.X 1 ^ 3

/-- **The equation read as a cubic in `T₂`**, with coefficients in `k[T₀, T₁]`: swap `T₀` and
`T₂`, then split off the first variable. -/
def cubicChart (k : Type u) [CommRing k] :
    MvPolynomial (Fin 3) k ≃ₐ[k] Polynomial (MvPolynomial (Fin 2) k) :=
  (MvPolynomial.renameEquiv k (Equiv.swap (0 : Fin 3) 2)).trans (MvPolynomial.finSuccEquiv k 2)

/-- `cubicChart` on a variable: swap `T₀` and `T₂`, then split off the first variable. -/
private theorem cubicChart_X (k : Type u) [CommRing k] (j : Fin 3) :
    cubicChart k (MvPolynomial.X j) =
      MvPolynomial.finSuccEquiv k 2 (MvPolynomial.X (Equiv.swap (0 : Fin 3) 2 j)) := by
  simp [cubicChart]

/-- `cubicChart` sends `T₀` to the constant `T₁` of `k[T₀, T₁]`. -/
@[simp] theorem cubicChart_X_zero (k : Type u) [CommRing k] :
    cubicChart k (MvPolynomial.X 0) = Polynomial.C (MvPolynomial.X (R := k) (1 : Fin 2)) :=
  (cubicChart_X k 0).trans (MvPolynomial.finSuccEquiv_X_succ (j := 1))

/-- `cubicChart` sends `T₁` to the constant `T₀` of `k[T₀, T₁]`. -/
@[simp] theorem cubicChart_X_one (k : Type u) [CommRing k] :
    cubicChart k (MvPolynomial.X 1) = Polynomial.C (MvPolynomial.X (R := k) (0 : Fin 2)) :=
  (cubicChart_X k 1).trans (MvPolynomial.finSuccEquiv_X_succ (j := 0))

/-- `cubicChart` sends `T₂` to the polynomial variable. -/
@[simp] theorem cubicChart_X_two (k : Type u) [CommRing k] :
    cubicChart k (MvPolynomial.X 2) = (Polynomial.X : Polynomial (MvPolynomial (Fin 2) k)) :=
  (cubicChart_X k 2).trans MvPolynomial.finSuccEquiv_X_zero

/-- `cubicChart` sends a constant `a` to the constant `a`. -/
@[simp] theorem cubicChart_C (k : Type u) [CommRing k] (a : k) :
    cubicChart k (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) := by
  have hC : (MvPolynomial.C a : MvPolynomial (Fin 3) k) = algebraMap k _ a := rfl
  rw [hC, AlgEquiv.commutes]
  rfl

/-- Up to sign the equation is the monic cubic `T₂³ - (T₀²T₁ + aT₁³)` over `k[T₀, T₁]`. -/
theorem cubicChart_neg_planeCubic (k : Type u) [CommRing k] (a : k) :
    cubicChart k (-planeCubic k a) =
      Polynomial.X ^ 3 - Polynomial.C (planeCubicCoefficient k a) := by
  rw [planeCubic, planeCubicCoefficient]
  simp only [map_neg, map_add, map_sub, map_mul, map_pow, cubicChart_X_zero,
    cubicChart_X_one, cubicChart_X_two, cubicChart_C]
  ring

/-- The variable `T₁` divides the constant term exactly once: `T₁ ∤ T₀²`. -/
theorem planeCubicCoefficient_notDvd_sq (k : Type u) [Field k] (a : k) :
    ¬ (MvPolynomial.X (R := k) (1 : Fin 2)) ^ 2 ∣ planeCubicCoefficient k a := by
  rintro ⟨q, hq⟩
  rw [planeCubicCoefficient] at hq
  have h : (MvPolynomial.X (R := k) (0 : Fin 2)) ^ 2 +
      MvPolynomial.C a * MvPolynomial.X 1 ^ 2 = MvPolynomial.X 1 * q := by
    refine mul_left_cancel₀ (MvPolynomial.X_ne_zero (1 : Fin 2)) ?_
    calc (MvPolynomial.X (R := k) (1 : Fin 2)) *
          ((MvPolynomial.X 0) ^ 2 + MvPolynomial.C a * MvPolynomial.X 1 ^ 2)
        = MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 +
            MvPolynomial.C a * MvPolynomial.X 1 ^ 3 := by ring
      _ = MvPolynomial.X 1 ^ 2 * q := hq
      _ = MvPolynomial.X 1 * (MvPolynomial.X 1 * q) := by ring
  simpa using congrArg (MvPolynomial.eval fun j : Fin 2 => if j = 0 then (1 : k) else 0) h

/-- **The equation of the example is irreducible**, by Eisenstein at `T₁` for the cubic in `T₂`.
With [Stacks, Tag 0BYC] this is what makes the zero scheme a curve over `k`. -/
theorem planeCubic_irreducible (k : Type u) [Field k] (a : k) :
    Irreducible (planeCubic k a) := by
  refine ((Associated.refl (planeCubic k a)).neg_left.irreducible_iff).mp ?_
  refine (MulEquiv.irreducible_iff (cubicChart k).toMulEquiv).mp ?_
  change Irreducible (cubicChart k (-planeCubic k a))
  rw [cubicChart_neg_planeCubic]
  refine irreducible_X_pow_sub_C_of_prime_dvd_notDvd_sq
    (p := (MvPolynomial.X 1 : MvPolynomial (Fin 2) k)) MvPolynomial.X_prime
    ⟨MvPolynomial.X 0 ^ 2 + MvPolynomial.C a * MvPolynomial.X 1 ^ 2,
      by rw [planeCubicCoefficient]; ring⟩
    (planeCubicCoefficient_notDvd_sq k a) (by decide)

/-! ### The inseparable extension of function fields -/

/-- An algebra generated by a single element whose `p`-th power lies in the base field is purely
inseparable, in exponential characteristic `p`. -/
theorem isPurelyInseparable_of_adjoin_singleton_eq_top {F : Type u} {L : Type v}
    [Field F] [CommRing L] [IsDomain L] [Algebra F L] (p : ℕ) [ExpChar F p] (y : L)
    (hy : y ^ p ∈ (algebraMap F L).range) (hgen : Algebra.adjoin F {y} = ⊤) :
    IsPurelyInseparable F L := by
  have : ExpChar L p := expChar_of_injective_algebraMap (algebraMap F L).injective p
  refine (isPurelyInseparable_iff_pow_mem F p).mpr fun x => ⟨1, ?_⟩
  rw [pow_one]
  have hx : x ∈ Algebra.adjoin F {y} := by rw [hgen]; trivial
  induction hx using Algebra.adjoin_induction with
  | mem z hz => simpa only [Set.mem_singleton_iff.mp hz] using hy
  | algebraMap c => exact ⟨c ^ p, map_pow (algebraMap F L) c p⟩
  | add x z hx hz ihx ihz =>
    rw [add_pow_expChar]
    exact (algebraMap F L).range.add_mem ihx ihz
  | mul x z hx hz ihx ihz =>
    rw [mul_pow]
    exact (algebraMap F L).range.mul_mem ihx ihz

/-- **Adjoining a `p`-th root of a non-`p`-th-power gives a purely inseparable extension of
degree `p`**, in characteristic `p`. -/
theorem isPurelyInseparable_and_finrank_adjoinRoot_X_pow_sub_C {F : Type u} [Field F] (p : ℕ)
    (hp : p.Prime) [ExpChar F p] {c : F} (hc : ∀ b : F, b ^ p ≠ c) :
    IsPurelyInseparable F (AdjoinRoot (Polynomial.X ^ p - Polynomial.C c : Polynomial F)) ∧
      Module.finrank F
        (AdjoinRoot (Polynomial.X ^ p - Polynomial.C c : Polynomial F)) = p := by
  have hfact : Fact (Irreducible (Polynomial.X ^ p - Polynomial.C c : Polynomial F)) :=
    ⟨X_pow_sub_C_irreducible_of_prime hp hc⟩
  have hne : (Polynomial.X ^ p - Polynomial.C c : Polynomial F) ≠ 0 := hfact.out.ne_zero
  refine ⟨?_, ?_⟩
  · refine isPurelyInseparable_of_adjoin_singleton_eq_top p
      (AdjoinRoot.root (Polynomial.X ^ p - Polynomial.C c : Polynomial F)) ⟨c, ?_⟩
      AdjoinRoot.adjoinRoot_eq_top
    have h := AdjoinRoot.mk_self (f := (Polynomial.X ^ p - Polynomial.C c : Polynomial F))
    simp only [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h
    exact h.symm
  · rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim,
      Polynomial.natDegree_X_pow_sub_C]

/-- **The function field of the curve of [Stacks, Tag 0CD1]**, as an extension of the function
field `k(x)` of the projective line along the `x`-projection: `k(x)[y]/(y³ - x² - a)`, the
dehomogenization `x² - y³ + a = 0` of the equation on `D₊(T₀)` solved for `y`. -/
@[ega "IV 6.7.5"]
abbrev curveFunctionField (k : Type u) [Field k] (a : k) : Type u :=
  AdjoinRoot (Polynomial.X ^ 3 - Polynomial.C (RatFunc.X ^ 2 + RatFunc.C a) :
    Polynomial (RatFunc k))

/-- **The `x`-projection induces an inseparable extension of function fields of degree `p = 3`.**
In characteristic three, `k(x) ⊆ k(x)(y)` with `y³ = x² + a` is purely inseparable, and it has
degree three because `x² + a` is not a cube in `k(x)`. -/
theorem isPurelyInseparable_and_finrank_curveFunctionField (k : Type u) [Field k] [ExpChar k 3]
    (a : k) :
    IsPurelyInseparable (RatFunc k) (curveFunctionField k a) ∧
      Module.finrank (RatFunc k) (curveFunctionField k a) = 3 :=
  isPurelyInseparable_and_finrank_adjoinRoot_X_pow_sub_C 3 Nat.prime_three
    (ratFuncX_sq_add_C_not_cube a)

/-! ### The genus change -/

/-- **The plane curve of [Stacks, Tag 0CD1] as the plane-curve data of [Stacks, Tag 0BYB].** The
equation `F = T₁²T₀ - T₂³ + aT₀³` is homogeneous of degree three and generates the homogeneous
ideal of `Z`, so `Z` is a plane curve of degree three in the sense of
`AlgebraicGeometry.ProjectiveSpectrum.Proj.PlaneCurveData`; that is the shape in which the genus
formula of [Stacks, Tag 0BYD] consumes it.

The degree is recorded as the literal `3`, not as `(planeCubic k a).totalDegree`, so that the
genus the formula returns is `(3 - 1)(3 - 2)/2` with no rewriting; the two agree by
`planeCubic_totalDegree`. -/
def planeCubicData {k : Type u} [Field k] (a : k) {Z : Scheme.{u}} [Nonempty Z]
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k)) [IsClosedImmersion i]
    (hno : HasNoEmbeddedPoints Z)
    (hdim : ∀ W ∈ irreducibleComponents Z, topologicalKrullDim W = 1)
    (hI : idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) k) i =
      Ideal.span {planeCubic k a}) :
    PlaneCurveData k where
  Z := Z
  i := i
  isClosedImmersion := ‹IsClosedImmersion i›
  nonempty := ‹Nonempty Z›
  hasNoEmbeddedPoints := hno
  equidimensional := hdim
  deg := 3
  F := planeCubic k a
  isHomogeneous := (MvPolynomial.mem_homogeneousSubmodule 3 _).2 (planeCubic_isHomogeneous k a)
  span_eq := hI

/-- The structure morphism of the plane-curve data is the closed immersion followed by the
structure morphism of `𝐏²_k`, as everywhere else in this file. -/
@[simp] theorem planeCubicData_toSpec {k : Type u} [Field k] (a : k) {Z : Scheme.{u}}
    [Nonempty Z]
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k)) [IsClosedImmersion i]
    (hno : HasNoEmbeddedPoints Z)
    (hdim : ∀ W ∈ irreducibleComponents Z, topologicalKrullDim W = 1)
    (hI : idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) k) i =
      Ideal.span {planeCubic k a}) :
    (planeCubicData a i hno hdim hI).toSpec = i ≫ projToSpecCoeff k 2 := rfl

/-- The degree recorded by the plane-curve data is three, the degree of the cubic. -/
@[simp] theorem planeCubicData_deg {k : Type u} [Field k] (a : k) {Z : Scheme.{u}}
    [Nonempty Z]
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k)) [IsClosedImmersion i]
    (hno : HasNoEmbeddedPoints Z)
    (hdim : ∀ W ∈ irreducibleComponents Z, topologicalKrullDim W = 1)
    (hI : idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) k) i =
      Ideal.span {planeCubic k a}) :
    (planeCubicData a i hno hdim hI).deg = 3 := rfl

/-- **The genus of the curve of [Stacks, Tag 0CD1] is one.** This is the degree formula of
[Stacks, Tag 0BYD] — `AlgebraicGeometry.ProjectiveSpectrum.Proj.genus_planeCurve` — at
`deg F = 3`: `(3 - 1)(3 - 2)/2 = 1`. No genus value is assumed. -/
theorem genus_planeCubic_eq_one {k : Type u} [Field k] (a : k)
    {Z : Scheme.{u}} [Nonempty Z] (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k))
    [IsClosedImmersion i] (hno : HasNoEmbeddedPoints Z)
    (hdim : ∀ W ∈ irreducibleComponents Z, topologicalKrullDim W = 1)
    (hI : idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) k) i =
      Ideal.span {planeCubic k a}) :
    genus (i ≫ projToSpecCoeff k 2) = 1 :=
  (genus_planeCurve (planeCubicData a i hno hdim hI)).trans (by
    rw [planeCubicData_deg])

/-- **The genus change of [Stacks, Tag 0CD1], for a supplied plane cubic.** Let `k` be a field
of characteristic three and let `a ∈ k` not be a cube — such a pair exists by
`exists_charThree_notCube`. Let `Z ⊆ 𝐏²_k` be the plane curve cut out by `F = T₁²T₀ - T₂³ + aT₀³`,
equidimensional of dimension one and without embedded points.
Then `Z` is a curve over `k`, its genus is `1`, the genus of `𝐏¹_k` is `0`, these two differ, and
the `x`-projection `Z ⟶ 𝐏¹_k` induces a purely inseparable extension of function fields of
degree three. So the genus is not preserved by a purely inseparable morphism.

The non-cube hypothesis is the nonsingularity of `Z`
(`squarefree_X_pow_three_sub_C_iff_forall_pow_ne`), and characteristic three is what makes the
function field extension inseparable. Both genus values are proved: `1` from the genus formula of
[Stacks, Tag 0BYD] (`genus_planeCubic_eq_one`) and `0` from
`Stacks.Curves.genus_projToSpecCoeff_one`. The extension of function fields here is the abstract
`curveFunctionField k a`; the example in full, at the constructed curve and for the extension the
projection induces, is
`Stacks.Curves.InseparableGenus.planeCubicProjection_inseparable_genus_change`. -/
theorem isCurve_and_genus_ne_genus_projectiveLine {k : Type u} [Field k] [ExpChar k 3] (a : k)
    (ha : ∀ b : k, b ^ 3 ≠ a)
    {Z : Scheme.{u}} [Nonempty Z]
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k))
    [IsClosedImmersion i] (hno : HasNoEmbeddedPoints Z)
    (hdim : ∀ W ∈ irreducibleComponents Z, topologicalKrullDim W = 1)
    (hI : idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) k) i =
      Ideal.span {planeCubic k a}) :
    Squarefree (Polynomial.X ^ 3 - Polynomial.C a : Polynomial k) ∧
      IsCurve k (i ≫ projToSpecCoeff k 2) ∧
      genus (i ≫ projToSpecCoeff k 2) = 1 ∧
      genus (projToSpecCoeff k 1) = 0 ∧
      genus (i ≫ projToSpecCoeff k 2) ≠ genus (projToSpecCoeff k 1) ∧
      IsPurelyInseparable (RatFunc k) (curveFunctionField k a) ∧
      Module.finrank (RatFunc k) (curveFunctionField k a) = 3 := by
  have hone : genus (i ≫ projToSpecCoeff k 2) = 1 :=
    genus_planeCubic_eq_one a i hno hdim hI
  have hline : genus (projToSpecCoeff k 1) = 0 := genus_projToSpecCoeff_one k
  refine ⟨(squarefree_X_pow_three_sub_C_iff_forall_pow_ne a).mpr ha,
    (ProjectiveSpectrum.Proj.projectivePlane_isCurve_iff_irreducible_of_equidimensional
      k i hdim hI).mpr (planeCubic_irreducible k a),
    hone, hline, ?_, (isPurelyInseparable_and_finrank_curveFunctionField k a).1,
    (isPurelyInseparable_and_finrank_curveFunctionField k a).2⟩
  rw [hone, hline]
  exact one_ne_zero

end Stacks.Curves.InseparableGenus

end
