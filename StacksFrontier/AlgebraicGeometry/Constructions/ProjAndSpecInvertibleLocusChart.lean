module

public import StacksFrontier.RingTheory.GradedAlgebra.TruncationLocalizationChart
public import StacksFrontier.RingTheory.GradedAlgebra.Proj.DegreeOneUnitAway

/-!
# The chart of the cone over a standard open `D₊(cb)` with `deg c = deg b + 1`

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `B = ⨁_{d ≥ 0} A_{≥ d}` its truncation algebra and
`L = Proj B` the cone over `P = Proj A` ([Stacks, Tag 0EKF]). Over a standard open `D₊(g)` of `P`
the cone is the affine scheme with ring `C = B₍ψ g₎`, and
`Stacks.Truncation.awayToLocalization : C → A[1/g]` identifies `C` with the nonnegative part of
the localization.

Suppose `g = c b` with `c` homogeneous of degree `m + 1` and `b` homogeneous of degree `m`. These
standard opens cover the open of [Stacks, Tag 01MU] for `d = 1`. In `A[1/g]` the fraction
`u = c² / g` is a unit of degree one (`Stacks.DegreeOneUnitAway.chartUnit`), and this file shows
that `C = A₍g₎[X]` with `X` the element `(c²)⁽²ᵐ⁺¹⁾ / ψ g` of `C`, which is `u` in `A[1/g]`: the
cone over `D₊(g)` is the trivial line bundle. Under this identification the restriction to the
This generalises `Stacks.Truncation.Chart.bijective_polyHom`, which treats `g = u h` with `u` of
degree one; the open of [Stacks, Tag 01MU] for `d = 1` need not be covered by such standard opens.

## Main definitions

* `Stacks.Truncation.RatioChart.coordinate`: the element `X = (c²)⁽²ᵐ⁺¹⁾ / ψ g` of `C`.
* `Stacks.Truncation.RatioChart.polyHom`: the map `A₍g₎[X] → C`.

## Main results

* `Stacks.Truncation.RatioChart.bijective_polyHom`: **`A₍g₎[X] → C` is bijective.**
* `Stacks.Truncation.RatioChart.exists_eq_awayMap_mul_coordinate`: every element of degree one
  of `C` is a degree-zero fraction of `A` times the coordinate.

## References

* [Stacks Project, Tag 0EKF](https://stacks.math.columbia.edu/tag/0EKF)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
-/

@[expose] public noncomputable section

open HomogeneousLocalization Polynomial
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation Stacks.DegreeOneUnitAway

namespace Stacks.Truncation.RatioChart

universe u

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {c b g : A} {m : ℕ}

/-- `c²` lies in `𝒜 (1 + 1 · (2m + 1))` when `c` has degree `m + 1`. -/
theorem sq_mem (hc : c ∈ 𝒜 (m + 1)) : c ^ 2 ∈ 𝒜 (1 + 1 * (2 * m + 1)) := by
  have h := SetLike.pow_mem_graded 2 hc
  convert h using 2
  simp only [smul_eq_mul]
  ring

/-- `c²` lies in `A_{≥ 1 · (2m + 1)}` when `c` has degree `m + 1`. -/
theorem sq_mem_truncation (hc : c ∈ 𝒜 (m + 1)) : c ^ 2 ∈ truncation 𝒜 (1 * (2 * m + 1)) :=
  mem_truncation_of_mem 𝒜 (Nat.le_add_left _ _) (sq_mem hc)

/-- **The fibre coordinate of the cone over `D₊(g)`**: the element `(c²)⁽²ᵐ⁺¹⁾ / ψ g` of
`C = B₍ψ g₎`, which is the unit `c² / g` of degree one in `A[1/g]`. -/
def coordinate (hc : c ∈ 𝒜 (m + 1)) (hg : g ∈ 𝒜 (2 * m + 1)) :
    Away (grading 𝒜) (psi 𝒜 g) :=
  awayElt 𝒜 (2 * m + 1) hg 1 (c ^ 2) (sq_mem_truncation hc)

/-- The comparison map `C → A[1/g]` sends the fibre coordinate to the unit `c² / g`. -/
theorem awayToLocalization_coordinate (hc : c ∈ 𝒜 (m + 1)) (hg : g ∈ 𝒜 (2 * m + 1))
    (hcb : c * b = g) :
    awayToLocalization 𝒜 (coordinate hc hg) = (chartUnit hcb : Localization.Away g) := by
  rw [coordinate, awayToLocalization_awayElt, coe_chartUnit, awayFrac]
  exact congrArg (Localization.mk (c ^ 2)) (Subtype.ext (pow_one g))

/-- The fibre coordinate has degree one. -/
theorem coordinate_mem_awayGrading (hc : c ∈ 𝒜 (m + 1)) (hg : g ∈ 𝒜 (2 * m + 1)) :
    coordinate hc hg ∈ awayGrading 𝒜 (2 * m + 1) hg 1 :=
  awayElt_mem_awayGrading 𝒜 (2 * m + 1) hg (sq_mem hc)

/-- The degree-zero fraction `x / gⁿ` of `A`, carried by `ψ` into `C`, is `x⁽ⁿᵉ⁾ / (ψ g)ⁿ`. -/
theorem awayMap_psi_mk {e : ℕ} (hg : g ∈ 𝒜 e) (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • e)) :
    Away.map (psi 𝒜) g (Away.mk 𝒜 hg n x hx) =
      awayElt 𝒜 e hg n x (mem_truncation_of_mem 𝒜 (by simp [smul_eq_mul]) hx) := by
  rw [Away.map_mk]
  refine congrArg HomogeneousLocalization.mk
    (HomogeneousLocalization.NumDenSameDeg.ext _ (smul_eq_mul n e) ?_ ?_)
  · change psi 𝒜 x = degElt 𝒜 (n * e) x _
    rw [psi_eq_degElt 𝒜 x hx]
    exact degElt_congr 𝒜 (smul_eq_mul n e) rfl _ _
  · change psi 𝒜 g ^ n = psi 𝒜 g ^ n
    rfl

/-- **On degree-zero fractions of `A` the comparison map `C → A[1/g]` is the inclusion.** -/
theorem awayToLocalization_awayMap_psi {e : ℕ} (hg : g ∈ 𝒜 e) (z : Away 𝒜 g) :
    awayToLocalization 𝒜 (Away.map (psi 𝒜) g z) = z.val := by
  obtain ⟨n, x, hx, rfl⟩ := Away.mk_surjective 𝒜 hg z
  rw [awayMap_psi_mk hg, awayToLocalization_awayElt, Away.val_mk]
  rfl

/-- The map `A₍g₎[X] → C` sending `X` to the fibre coordinate. -/
def polyHom (hc : c ∈ 𝒜 (m + 1)) (hg : g ∈ 𝒜 (2 * m + 1)) :
    (Away 𝒜 g)[X] →+* Away (grading 𝒜) (psi 𝒜 g) :=
  eval₂RingHom (Away.map (psi 𝒜) g) (coordinate hc hg)

/-- The map `A₍g₎[X] → C` sends the constant `z` to `Away.map ψ g z`. -/
theorem polyHom_C (hc : c ∈ 𝒜 (m + 1)) (hg : g ∈ 𝒜 (2 * m + 1)) (z : Away 𝒜 g) :
    polyHom hc hg (Polynomial.C z) = Away.map (psi 𝒜) g z :=
  eval₂_C _ _

/-- The map `A₍g₎[X] → C` sends `X` to the fibre coordinate. -/
theorem polyHom_X (hc : c ∈ 𝒜 (m + 1)) (hg : g ∈ 𝒜 (2 * m + 1)) :
    polyHom hc hg Polynomial.X = coordinate hc hg :=
  eval₂_X _ _

/-- **Read in `A[1/g]`, the map `A₍g₎[X] → C` is evaluation at the unit `c² / g`.** -/
theorem awayToLocalization_comp_polyHom (hc : c ∈ 𝒜 (m + 1)) (hg : g ∈ 𝒜 (2 * m + 1))
    (hcb : c * b = g) :
    (awayToLocalization 𝒜).comp (polyHom hc hg) =
      eval₂RingHom (algebraMap (Away 𝒜 g) (Localization.Away g))
        (chartUnit hcb : Localization.Away g) := by
  refine Polynomial.ringHom_ext (fun z => ?_) ?_
  · rw [RingHom.comp_apply, polyHom_C, coe_eval₂RingHom, eval₂_C,
      HomogeneousLocalization.algebraMap_apply]
    exact awayToLocalization_awayMap_psi hg z
  · rw [RingHom.comp_apply, polyHom_X, coe_eval₂RingHom, eval₂_X]
    exact awayToLocalization_coordinate hc hg hcb

/-- Evaluation at the unit `c² / g` is injective on `A₍g₎[X]`: the powers of `c² / g` are
linearly independent over `A₍g₎`. -/
theorem injective_eval₂_chartUnit (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m) (hcb : c * b = g) :
    Function.Injective (eval₂RingHom (algebraMap (Away 𝒜 g) (Localization.Away g))
      (chartUnit hcb : Localization.Away g)) := by
  have hli := (linearIndependent_chartUnit_zpow hc hb hcb).comp (fun n : ℕ => (n : ℤ))
    Nat.cast_injective
  refine (injective_iff_map_eq_zero _).mpr fun P hP => ?_
  refine Polynomial.ext fun n => ?_
  rw [Polynomial.coeff_zero]
  by_cases hn : n ∈ P.support
  · refine linearIndependent_iff'.mp hli P.support P.coeff ?_ n hn
    rw [coe_eval₂RingHom, eval₂_eq_sum, Polynomial.sum_def] at hP
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) hP
    simp only [Function.comp_apply, zpow_natCast, Units.val_pow_eq_pow_val,
      HomogeneousLocalization.algebraMap_apply]
    rfl
  · exact Polynomial.notMem_support_iff.mp hn

/-- **The cone over `D₊(cb)` is the trivial line bundle**: `A₍g₎[X] → C` is bijective. -/
theorem bijective_polyHom (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m) (hcb : c * b = g) :
    Function.Bijective (polyHom hc (DegreeOneUnitAway.mul_mem hc hb hcb)) := by
  classical
  have hg := DegreeOneUnitAway.mul_mem hc hb hcb
  have hcomp := awayToLocalization_comp_polyHom (𝒜 := 𝒜) hc hg hcb
  have hρinj := awayToLocalization_injective 𝒜 (2 * m + 1) hg
  refine ⟨fun P Q hPQ => ?_, fun y => ?_⟩
  · have := congrArg (awayToLocalization 𝒜) hPQ
    rw [← RingHom.comp_apply, ← RingHom.comp_apply, hcomp] at this
    exact injective_eval₂_chartUnit hc hb hcb this
  · obtain ⟨k, a, ha, rfl⟩ := awayElt_surjective 𝒜 (2 * m + 1) hg y
    have hpoly : ∀ e ∈ DFinsupp.support (DirectSum.decompose 𝒜 a),
        ∃ P : (Away 𝒜 g)[X],
          eval₂RingHom (algebraMap (Away 𝒜 g) (Localization.Away g))
              (chartUnit hcb : Localization.Away g) P =
            Localization.mk (DirectSum.decompose 𝒜 a e : A) (genPow g k) := by
      intro e he
      have hle : k * (2 * m + 1) ≤ e := by
        by_contra hlt
        exact (DFinsupp.mem_support_iff.1 he) (Subtype.ext
          (proj_eq_zero_of_mem_truncation 𝒜 (by omega) ha))
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
      obtain ⟨z, hz⟩ := exists_mk_eq_chartUnit_zpow_mul hc hb hcb
        (DirectSum.decompose 𝒜 a e).2 k
      refine ⟨Polynomial.C z * X ^ j, ?_⟩
      have hexp : ((e : ℕ) : ℤ) - (k : ℤ) * (2 * (m : ℤ) + 1) = (j : ℤ) := by
        rw [hj]; push_cast; ring
      rw [hz, hexp, zpow_natCast, Units.val_pow_eq_pow_val, map_mul, map_pow,
        coe_eval₂RingHom, eval₂_C, eval₂_X, HomogeneousLocalization.algebraMap_apply, mul_comm]
    choose P hP using hpoly
    refine ⟨∑ e ∈ (DFinsupp.support (DirectSum.decompose 𝒜 a)).attach, P e.1 e.2, hρinj ?_⟩
    rw [← RingHom.comp_apply, hcomp, map_sum, awayToLocalization_awayElt]
    simp only [hP]
    rw [Finset.sum_attach (DFinsupp.support (DirectSum.decompose 𝒜 a))
      (fun e => (Localization.mk (DirectSum.decompose 𝒜 a e : A) (genPow g k) :
        Localization.Away g)),
      ← Localization.mk_sum, DirectSum.sum_support_decompose 𝒜 a]
    rfl

/-- The identification `A₍g₎[X] ≃+* C` of the chart of the cone over `D₊(cb)`. -/
def polyEquiv (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m) (hcb : c * b = g) :
    (Away 𝒜 g)[X] ≃+* Away (grading 𝒜) (psi 𝒜 g) :=
  RingEquiv.ofBijective (polyHom hc (DegreeOneUnitAway.mul_mem hc hb hcb))
    (bijective_polyHom hc hb hcb)

/-- The identification `A₍g₎[X] ≃+* C` is `polyHom`. -/
theorem polyEquiv_apply (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m) (hcb : c * b = g)
    (P : (Away 𝒜 g)[X]) :
    polyEquiv hc hb hcb P = polyHom hc (DegreeOneUnitAway.mul_mem hc hb hcb) P :=
  rfl

/-- **Every element of degree one of `C` is a degree-zero fraction of `A` times the fibre
coordinate.** -/
theorem exists_eq_awayMap_mul_coordinate (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m) (hcb : c * b = g)
    {y : Away (grading 𝒜) (psi 𝒜 g)}
    (hy : y ∈ awayGrading 𝒜 (2 * m + 1) (DegreeOneUnitAway.mul_mem hc hb hcb) 1) :
    ∃ z : Away 𝒜 g,
      y = Away.map (psi 𝒜) g z * coordinate hc (DegreeOneUnitAway.mul_mem hc hb hcb) := by
  have hg := DegreeOneUnitAway.mul_mem hc hb hcb
  obtain ⟨k, a, ha, hya⟩ := hy
  obtain ⟨z, hz⟩ := exists_mk_eq_chartUnit_zpow_mul hc hb hcb ha k
  refine ⟨z, awayToLocalization_injective 𝒜 (2 * m + 1) hg ?_⟩
  have hexp : (((1 + k * (2 * m + 1) : ℕ) : ℤ) - (k : ℤ) * (2 * (m : ℤ) + 1)) = 1 := by
    push_cast; ring
  change awayToLocalization 𝒜 y = _ at hya
  rw [hya, map_mul, awayToLocalization_awayMap_psi hg,
    awayToLocalization_coordinate hc hg hcb, awayFrac]
  refine (hz.trans ?_)
  rw [hexp, zpow_one, mul_comm]

end Stacks.Truncation.RatioChart

end
