module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.NumberTheory.FrobeniusNumber
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.MvPowerSeries.CotangentSpace

/-!
# Brieskorn hypersurfaces that are not factorial

The complex formal hypersurface with equation `x^r + y^s + z^t` is not a unique
factorization domain when `1 < r < s < t` are pairwise coprime, except for the
triple `(2, 3, 5)`. In particular, the hypersurface with exponents `(2, 5, 7)`
is not factorial.

## Main definitions

* `Stacks.MvPowerSeries.Brieskorn.brieskornEquation` is the defining power series over a
  commutative ring.
* `Stacks.MvPowerSeries.Brieskorn.BrieskornHypersurface` is its quotient over the complex
  numbers.

## Main results

All declarations are in the namespace `Stacks.MvPowerSeries.Brieskorn`.

* `not_uniqueFactorizationMonoid_brieskornHypersurface` is the general nonfactoriality
  assertion.
* `not_uniqueFactorizationMonoid_brieskornHypersurface_two_five_seven` is the explicit
  example.

## Implementation notes

The three variables are indexed by `Fin 3`, in the order `x`, `y`, `z`. The exception
`(2, 3, 5)` is expressed as the negation of simultaneous equality of the three exponents.

The proof is not the one of the source, which exhibits the seven monomial curves
`x ↦ t^7, y ↦ t^3, z ↦ -ζ t^2 (1 + t)^{1/7}` and multiplies their equations; instead one
monomial curve suffices. Its kernel is a prime of height one — the hypersurface has dimension
two, and the kernel is neither zero nor maximal — so factoriality would make it principal, and
then the equation and a second generator would generate a proper ideal containing the equation
inside its own maximal multiple, which is impossible for an irreducible element. The numerical
input is the Frobenius gap `r*s + r*t + s*t < r*s*t`, which for ordered pairwise coprime
exponents greater than one fails exactly at `(2, 3, 5)`.

## References

* [Stacks Project, Tag 0AEA](https://stacks.math.columbia.edu/tag/0AEA)
* [Brieskorn]
* [Lipman-rational]

Tags covered: 0AEA.
-/

@[expose] public section

namespace Stacks.MvPowerSeries.Brieskorn
open Stacks.MvPowerSeries.RegularParameters

/-- The formal power series `x^r + y^s + z^t`. -/
public noncomputable def brieskornEquation (R : Type*) [CommRing R] (r s t : ℕ) :
    MvPowerSeries (Fin 3) R :=
  MvPowerSeries.X 0 ^ r + MvPowerSeries.X 1 ^ s + MvPowerSeries.X 2 ^ t

/-- The complex formal Brieskorn hypersurface with exponents `r`, `s`, `t`. -/
public abbrev BrieskornHypersurface (r s t : ℕ) : Type :=
  MvPowerSeries (Fin 3) ℂ ⧸ Ideal.span {brieskornEquation ℂ r s t}

private theorem equation_constantCoeff_zero {r s t : ℕ}
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) :
    MvPowerSeries.constantCoeff (brieskornEquation ℂ r s t) = 0 := by
  simp [brieskornEquation, map_add, map_pow, hr.ne', hs.ne', ht.ne']

private theorem equation_ideal_ne_top {r s t : ℕ}
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) :
    Ideal.span ({brieskornEquation ℂ r s t} : Set (MvPowerSeries (Fin 3) ℂ)) ≠ ⊤ := by
  intro htop
  have hunit : IsUnit (brieskornEquation ℂ r s t) :=
    Ideal.span_singleton_eq_top.mp htop
  have hc := MvPowerSeries.isUnit_iff_constantCoeff.mp hunit
  rw [equation_constantCoeff_zero hr hs ht] at hc
  exact not_isUnit_zero hc


private theorem variable_mem_maximalIdeal (i : Fin 3) :
    (MvPowerSeries.X i : MvPowerSeries (Fin 3) ℂ) ∈
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin 3) ℂ) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    MvPowerSeries.isUnit_iff_constantCoeff]
  simp

/-- The ambient formal power series ring has dimension at most three. -/
private theorem ambient_ringKrullDim_le_three :
    ringKrullDim (MvPowerSeries (Fin 3) ℂ) ≤ 3 := by
  classical
  let B := MvPowerSeries (Fin 3) ℂ
  have hC : Function.Surjective (MvPowerSeries.constantCoeff : B →+* ℂ) := by
    intro a
    exact ⟨MvPowerSeries.C a, by simp⟩
  have hmax : IsLocalRing.maximalIdeal B =
      Ideal.span (Set.range (MvPowerSeries.X : Fin 3 → B)) := by
    apply le_antisymm
    · intro f hf
      have hzero : MvPowerSeries.constantCoeff f = 0 := by
        rw [← IsLocalRing.ker_eq_maximalIdeal _ hC] at hf
        exact RingHom.mem_ker.mp hf
      have hmem : f ∈ Ideal.span
          ((fun i : Fin 3 => (MvPowerSeries.X i : B)) '' (Finset.univ : Finset (Fin 3))) := by
        apply QuotInitVars.mem_span_X_image_of_coeff_eq_zero Finset.univ
        intro α hα
        by_cases hα0 : α = 0
        · subst α
          simpa [MvPowerSeries.coeff_zero_eq_constantCoeff] using hzero
        · exact (hα0 (Finsupp.ext fun i => hα i (Finset.mem_univ i))).elim
      simpa using hmem
    · refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      exact variable_mem_maximalIdeal i
  have hs : (IsLocalRing.maximalIdeal B).spanFinrank ≤ 3 := by
    rw [hmax]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans ?_
    simpa [← Set.image_univ] using
      Set.ncard_image_le (f := (MvPowerSeries.X : Fin 3 → B)) Set.finite_univ
  exact (ringKrullDim_le_spanFinrank_maximalIdeal B).trans (by exact_mod_cast hs)

/-- The Brieskorn equation is nonzero, as seen after setting `y` and `z` to zero. -/
private theorem equation_ne_zero {r s t : ℕ} (hs : 0 < s) (ht : 0 < t) :
    brieskornEquation ℂ r s t ≠ 0 := by
  let a : Fin 3 → PowerSeries ℂ := ![PowerSeries.X, 0, 0]
  have ha (i : Fin 3) : (a i).constantCoeff = 0 := by
    fin_cases i <;> simp [a]
  let ψ : MvPowerSeries (Fin 3) ℂ →ₐ[ℂ] PowerSeries ℂ :=
    MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)
  have hψ : ψ (brieskornEquation ℂ r s t) = PowerSeries.X ^ r := by
    simp only [brieskornEquation, map_add, map_pow]
    simp only [ψ, MvPowerSeries.substAlgHom_X]
    change (PowerSeries.X : PowerSeries ℂ) ^ r + 0 ^ s + 0 ^ t = _
    simp [hs.ne', ht.ne']
  intro h
  exact pow_ne_zero r PowerSeries.X_ne_zero (by rw [← hψ, h]; simp)


/-- Any nonzero Brieskorn equation cuts the ambient dimension from at most three
to at most two. -/
private theorem brieskorn_ringKrullDim_le_two {r s t : ℕ}
    (hs : 0 < s) (ht : 0 < t) :
    ringKrullDim (BrieskornHypersurface r s t) ≤ 2 := by
  have hreg : brieskornEquation ℂ r s t ∈
      nonZeroDivisors (MvPowerSeries (Fin 3) ℂ) :=
    mem_nonZeroDivisors_of_ne_zero (equation_ne_zero hs ht)
  have hle : ringKrullDim (BrieskornHypersurface r s t) + 1 ≤ 3 :=
    (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hreg).trans ambient_ringKrullDim_le_three
  exact ENat.WithBot.add_le_add_one_right_iff.mp
    (show ringKrullDim (BrieskornHypersurface r s t) + 1 ≤
      (2 : WithBot ℕ∞) + 1 by simpa [show (2 : WithBot ℕ∞) + 1 = 3 by norm_num] using hle)

private instance (r s t : ℕ) [NeZero r] [NeZero s] [NeZero t] :
    Nontrivial (BrieskornHypersurface r s t) :=
  Ideal.Quotient.nontrivial_iff.mpr
    (equation_ideal_ne_top (Nat.pos_of_neZero r) (Nat.pos_of_neZero s)
      (Nat.pos_of_neZero t))

private instance (r s t : ℕ) [NeZero r] [NeZero s] [NeZero t] :
    IsLocalRing (BrieskornHypersurface r s t) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective

/-- In a local ring, an irreducible element cannot lie in the maximal ideal
times a proper two-generated ideal when it is one of its generators. -/
private theorem irreducible_not_mem_maximal_mul_span_pair
    {R : Type*} [CommRing R] [IsLocalRing R]
    (f g : R) (hf : Irreducible f)
    (hproper : Ideal.span ({f, g} : Set R) ≠ ⊤) :
    f ∉ IsLocalRing.maximalIdeal R * Ideal.span {f, g} := by
  intro hmem
  let m := IsLocalRing.maximalIdeal R
  have hspan : Ideal.span ({f, g} : Set R) =
      Ideal.span {f} ⊔ Ideal.span {g} := by
    simpa using (Ideal.span_insert f ({g} : Set R))
  rw [hspan, Ideal.mul_sup] at hmem
  obtain ⟨u, hu, v, hv, huv⟩ := (Submodule.mem_sup).mp hmem
  obtain ⟨a, ha, hau⟩ := Ideal.mem_mul_span_singleton.mp hu
  obtain ⟨b, hb, hbv⟩ := Ideal.mem_mul_span_singleton.mp hv
  have hrelation : a * f + b * g = f := by rwa [← hau, ← hbv] at huv
  have hunit : IsUnit (1 - a) := by
    apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
    rwa [← IsLocalRing.mem_maximalIdeal]
  obtain ⟨w, hw⟩ := hunit.exists_left_inv
  have hfactor : f = (w * b) * g :=
    calc
      f = w * ((1 - a) * f) := by rw [← mul_assoc, hw, one_mul]
      _ = (w * b) * g := by
        rw [show (1 - a) * f = b * g by linear_combination -hrelation, mul_assoc]
  have hbg : w * b ∈ m := m.mul_mem_left w hb
  have hbg_nonunit : ¬ IsUnit (w * b) := by
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hbg
  have hgmem : g ∈ Ideal.span ({f, g} : Set R) := Ideal.subset_span (by simp)
  have hg_nonunit : ¬ IsUnit g := by
    intro hunitg
    exact hproper ((Ideal.span ({f, g} : Set R)).eq_top_of_isUnit_mem hgmem hunitg)
  rcases hf.isUnit_or_isUnit hfactor with h | h
  · exact hbg_nonunit h
  · exact hg_nonunit h

/-- If an ideal becomes principal after quotienting by one of its elements,
then the original ideal is generated by that element and one lift. -/
private theorem exists_pair_generators_of_quotient_principal
    {R : Type*} [CommRing R] (I : Ideal R) (f : R) (hf : f ∈ I)
    (hP : (I.map (Ideal.Quotient.mk (Ideal.span {f}))).IsPrincipal) :
    ∃ g : R, I = Ideal.span {f, g} := by
  let J : Ideal R := Ideal.span {f}
  let π : R →+* R ⧸ J := Ideal.Quotient.mk J
  let P : Ideal (R ⧸ J) := I.map π
  let : P.IsPrincipal := hP
  let q : R ⧸ J := Submodule.IsPrincipal.generator P
  have hqP : q ∈ P := by
    rw [← Submodule.IsPrincipal.span_singleton_generator P]
    exact Ideal.subset_span (by simp [q])
  obtain ⟨g, hgI, hgq⟩ := (Ideal.mem_map_iff_of_surjective π
    Ideal.Quotient.mk_surjective).mp hqP
  refine ⟨g, le_antisymm ?_ ?_⟩
  · intro x hx
    have hxP : π x ∈ P := Ideal.mem_map_of_mem π hx
    obtain ⟨d, hd⟩ := (Submodule.IsPrincipal.mem_iff_generator_dvd P).mp hxP
    obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective d
    have hzero : π (x - e * g) = 0 := by
      rw [map_sub, map_mul, hgq]
      linear_combination hd
    have hJ : x - e * g ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hJ
    apply Ideal.mem_span_pair.mpr
    refine ⟨a, e, ?_⟩
    linear_combination ha
  · rw [Ideal.span_le]
    rintro _ (rfl | rfl)
    exacts [hf, hgI]

/-- A nonzero prime away from the closed point has height one in a local
domain of dimension at most two. -/
private theorem height_one_of_nonzero_nonmaximal
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    (hdim : ringKrullDim R ≤ 2) (P : Ideal R) [P.IsPrime]
    (hne : P ≠ ⊥) (hnmax : ¬ P.IsMaximal) : P.height = 1 := by
  let : FiniteRingKrullDim R :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr ⟨by
      have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim R := ringKrullDim_nonneg_of_nontrivial
      exact ne_bot_of_gt (lt_of_lt_of_le (by decide : (⊥ : WithBot ℕ∞) < 0) h0), by
      intro htop
      rw [htop] at hdim
      exact (by decide : ¬ (⊤ : WithBot ℕ∞) ≤ 2) hdim⟩
  have hpneq : P ≠ IsLocalRing.maximalIdeal R := by
    intro h
    exact hnmax ((IsLocalRing.isMaximal_iff (R := R)).2 h)
  have hlt : P < IsLocalRing.maximalIdeal R :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal
      (show P ≠ ⊤ from (inferInstance : P.IsPrime).ne_top')) hpneq
  have hh : P.height < 2 := by
    have hM : (IsLocalRing.maximalIdeal R).height ≤ 2 := by
      have h : (↑((IsLocalRing.maximalIdeal R).height) : WithBot ℕ∞) ≤
          (↑(2 : ℕ∞) : WithBot ℕ∞) := by
        rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
        exact hdim
      exact WithBot.coe_le_coe.mp h
    calc
      P.height < (IsLocalRing.maximalIdeal R).height :=
        Ideal.height_strict_mono_of_isPrime hlt
      _ ≤ 2 := hM
  have h1 : 1 ≤ P.height := by
    rw [Order.one_le_iff_ne_zero]
    exact fun h => hne (Ideal.height_eq_zero_iff_eq_bot.mp h)
  exact le_antisymm (ENat.lt_two_iff.mp hh) h1

/-- Every ordered pairwise coprime triple in the theorem other than `E₈` lies on the
hyperbolic side of the Brieskorn exponent inequality. -/
private theorem exponent_inequality
    {r s t : ℕ} (hr : 1 < r) (hrs : r < s) (hst : s < t)
    (hrs' : Nat.Coprime r s) (hrt' : Nat.Coprime r t)
    (hE8 : ¬ (r = 2 ∧ s = 3 ∧ t = 5)) :
    r * s + r * t + s * t < r * s * t := by
  by_cases hr2 : r = 2
  · subst r
    by_cases hs3 : s = 3
    · subst s
      have ht7 : 7 ≤ t := by
        obtain ⟨k, hk⟩ := Nat.coprime_two_left.mp hrt'
        have ht5 : t ≠ 5 := fun h => hE8 ⟨rfl, rfl, h⟩
        omega
      nlinarith
    · have hs5 : 5 ≤ s := by
        obtain ⟨k, hk⟩ := Nat.coprime_two_left.mp hrs'
        omega
      have ht6 : 6 ≤ t := by omega
      have h₁ : 6 * s ≤ s * t := by nlinarith [Nat.mul_le_mul_left s ht6]
      have h₂ : 5 * t ≤ s * t := by nlinarith [Nat.mul_le_mul_right t hs5]
      nlinarith
  · have hr3 : 3 ≤ r := by omega
    have hs4 : 4 ≤ s := by omega
    have ht5 : 5 ≤ t := by omega
    have h₁ : 5 * (r * s) ≤ r * s * t := by
      nlinarith [Nat.mul_le_mul_left (r * s) ht5]
    have h₂ : 4 * (r * t) ≤ r * s * t := by
      nlinarith [Nat.mul_le_mul_left (r * t) hs4]
    have h₃ : 3 * (s * t) ≤ r * s * t := by
      nlinarith [Nat.mul_le_mul_left (s * t) hr3]
    have hp : 0 < r * s * t := by positivity
    nlinarith



/-- The Frobenius gap of `r` and `s` is large enough to support a curve section
whose `z` coordinate has higher order than the cancellation of `x^r` and `y^s`. -/
private theorem frobenius_branch_exponent {r s t : ℕ}
    (hineq : r * s + r * t + s * t < r * s * t) :
    let c := r * s - r - s
    0 < c ∧ r * s < c * t := by
  have ht : 0 < t := Nat.pos_of_ne_zero (by intro h; simp [h] at hineq)
  have hsum : r + s < r * s := by
    by_contra h
    have hle : r * s ≤ r + s := by omega
    have hm := Nat.mul_le_mul_right t hle
    nlinarith
  have hc : r * s - r - s + r + s = r * s := by omega
  dsimp
  constructor
  · omega
  · nlinarith


/-- The correction degree `d = c * t - r * s` satisfies `d + r * s = c * t`. -/
private theorem frobenius_degree_add_eq {r s t : ℕ}
    (hineq : r * s + r * t + s * t < r * s * t) :
    (r * s - r - s) * t - r * s + r * s = (r * s - r - s) * t := by
  obtain ⟨-, hct⟩ := frobenius_branch_exponent hineq
  omega

/-- The Frobenius gap remains coprime to either original exponent, so the
associated monomial curve has primitive weights. -/
private theorem frobenius_gap_coprime_right {r s : ℕ}
    (hrs : Nat.Coprime r s) (hsum : r + s < r * s) :
    Nat.Coprime (r * s - r - s) s := by
  let c := r * s - r - s
  have hc : c + s + r = r * s := by dsimp [c]; omega
  let d := Nat.gcd c s
  have hdc : d ∣ c := Nat.gcd_dvd_left c s
  have hds : d ∣ s := Nat.gcd_dvd_right c s
  have hdrs : d ∣ r * s := by
    simpa [mul_comm] using (dvd_mul_of_dvd_left hds r)
  have hdr : d ∣ r := by
    have h := Nat.dvd_sub hdrs (dvd_add hdc hds)
    convert h using 1; omega
  exact Nat.dvd_one.mp (by simpa [hrs] using Nat.dvd_gcd hdr hds)


/-- The correction degree `c * t - r * s` dominates `(s - 1) * (c - 1)`, where `c` is the
Frobenius gap of `r` and `s`. -/
private theorem frobenius_correction_bound {r s t : ℕ}
    (hr : 1 < r) (hrs : r < s) (hst : s < t) (hrs' : Nat.Coprime r s)
    (hineq : r * s + r * t + s * t < r * s * t) :
    (s - 1) * (r * s - r - s - 1) ≤ (r * s - r - s) * t - r * s := by
  let c := r * s - r - s
  let d := c * t - r * s
  have ⟨hc, hct⟩ := frobenius_branch_exponent hineq
  have hsum : r + s < r * s := by omega
  have hceq : c + r + s = r * s := by
    change r * s - r - s + r + s = r * s
    omega
  have hdeq : d + r * s = c * t := frobenius_degree_add_eq hineq
  have hs : 1 < s := by omega
  change (s - 1) * (c - 1) ≤ d
  by_cases hr2 : r = 2
  · subst r
    by_cases hs3 : s = 3
    · subst s
      have hc1 : c = 1 := by omega
      simp [hc1]
    · have hs5 : 5 ≤ s := by
        obtain ⟨k, hk⟩ := Nat.coprime_two_left.mp hrs'
        omega
      have hsmall : 2 * s ≤ 2 * c + s - 1 := by omega
      have htarget : (s - 1) * (c - 1) + 2 * s ≤ c * (s + 1) := by
        have hc1 : c - 1 + 1 = c := by omega
        have hs1 : s - 1 + 1 = s := by omega
        nlinarith
      have ht : s + 1 ≤ t := by omega
      have hmul := Nat.mul_le_mul_left c ht
      omega
  · have hr3 : 3 ≤ r := by omega
    have hs4 : 4 ≤ s := by omega
    have hprod : (0 : ℤ) ≤ ((r : ℤ) - 3) * ((s : ℤ) - 2) :=
      mul_nonneg (by omega) (by omega)
    have hsmall' : r * s + 1 ≤ 2 * c + s := by nlinarith [hprod]
    have hsmall : r * s ≤ 2 * c + s - 1 := by omega
    have htarget : (s - 1) * (c - 1) + r * s ≤ c * (s + 1) := by
      have hc1 : c - 1 + 1 = c := by omega
      have hs1 : s - 1 + 1 = s := by omega
      nlinarith
    have ht : s + 1 ≤ t := by omega
    have hmul := Nat.mul_le_mul_left c ht
    omega

/-- The correction exponent for the dual curve is a monomial in its `x` and `z`
coordinates, with a positive `z` exponent. -/
private theorem frobenius_correction_decomposition {r s t : ℕ}
    (hr : 1 < r) (hrs : r < s) (hst : s < t)
    (hrs' : Nat.Coprime r s) (hst' : Nat.Coprime s t)
    (hineq : r * s + r * t + s * t < r * s * t) :
    let c := r * s - r - s
    let d := c * t - r * s
    ∃ a b : ℕ, 0 < b ∧ a * s + b * c = d := by
  let c := r * s - r - s
  let d := c * t - r * s
  have ⟨hc, hct⟩ := frobenius_branch_exponent hineq
  have hsum : r + s < r * s := by omega
  have hdeq : d + r * s = c * t := frobenius_degree_add_eq hineq
  have hbound : (s - 1) * (c - 1) ≤ d := frobenius_correction_bound hr hrs hst hrs' hineq
  have hcop : Nat.Coprime s c :=
    (frobenius_gap_coprime_right hrs' hsum).symm
  obtain ⟨a, b, hab⟩ := Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le
    s c d (by simp [hcop.gcd_eq_one]) (by simpa [Nat.pred_eq_sub_one] using hbound)
  refine ⟨a, b, ?_, hab⟩
  by_contra hb
  have hb0 : b = 0 := by omega
  have hsd : s ∣ d := by
    refine ⟨a, ?_⟩
    simpa [hb0, mul_comm] using hab.symm
  have hsct : s ∣ c * t := by
    rw [← hdeq]
    exact dvd_add hsd ⟨r, by ring⟩
  have hst : s ∣ t := hcop.dvd_of_dvd_mul_left hsct
  have hsone : s = 1 := Nat.eq_one_of_dvd_coprimes hst' dvd_rfl hst
  omega

/-- The monomial correction makes the remaining `z` term a positive `z`
multiple of a difference of powers of `z^s` and `x^c`. -/
private theorem frobenius_correction_factorization {r s t : ℕ}
    (hr : 1 < r) (hrs : r < s) (hst : s < t)
    (hrs' : Nat.Coprime r s) (hst' : Nat.Coprime s t)
    (hineq : r * s + r * t + s * t < r * s * t) :
    let c := r * s - r - s
    ∃ a b k : ℕ, 0 < b ∧ t = b + k * s ∧ r + a = k * c := by
  let c := r * s - r - s
  let d := c * t - r * s
  obtain ⟨a, b, hb, hab⟩ :=
    frobenius_correction_decomposition hr hrs hst hrs' hst' hineq
  have ⟨hc, hct⟩ := frobenius_branch_exponent hineq
  have hsum : r + s < r * s := by omega
  have hdeq : d + r * s = c * t := frobenius_degree_add_eq hineq
  have hbt : b ≤ t := by nlinarith [hab]
  have hmul : c * (t - b) = s * (r + a) := by
    have hsub : t - b + b = t := Nat.sub_add_cancel hbt
    nlinarith [hab, hdeq]
  have hcop : Nat.Coprime s c :=
    (frobenius_gap_coprime_right hrs' hsum).symm
  have hsdvd : s ∣ t - b := hcop.dvd_of_dvd_mul_left (by
    rw [hmul]
    exact dvd_mul_right s _)
  obtain ⟨k, hk⟩ := hsdvd
  refine ⟨a, b, k, hb, ?_, ?_⟩
  · calc
      t = t - b + b := (Nat.sub_add_cancel hbt).symm
      _ = b + k * s := by rw [hk, mul_comm s k, add_comm]
  · have hspos : 0 < s := by omega
    nlinarith [hmul]


/-- Three curve relations force the hypersurface equation into the maximal
ideal times the curve kernel. This is the algebraic cancellation behind the
direct nonprincipality argument. -/
private theorem equation_mem_maximal_mul_of_curve_relations
    {R : Type*} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (x y z q α αinv : R) {r s t a b : ℕ}
    (hr : 0 < r) (hs : 0 < s)
    (hα : αinv * α = 1)
    (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hy : y ∈ IsLocalRing.maximalIdeal R)
    (hq : q ^ s = 1 + x ^ a * z ^ b)
    (hg1 : z * y - α * x ^ (r - 1) * q ∈ I)
    (hg2 : z * x * q ^ (s - 1) + α * y ^ (s - 1) ∈ I)
    (hcorrection : z ^ t - x ^ r * (x ^ a * z ^ b) ∈
      IsLocalRing.maximalIdeal R * I) :
    x ^ r + y ^ s + z ^ t ∈ IsLocalRing.maximalIdeal R * I := by
  let m := IsLocalRing.maximalIdeal R
  have hrpow : x ^ (r - 1) * x = x ^ r := pow_sub_one_mul hr.ne' x
  have hspow : y ^ (s - 1) * y = y ^ s := pow_sub_one_mul hs.ne' y
  have hqpow : q ^ (s - 1) * q = q ^ s := pow_sub_one_mul hs.ne' q
  have hxm : x * q ^ (s - 1) ∈ m := m.mul_mem_right _ hx
  have hfirst := Ideal.mul_mem_mul hxm hg1
  have hsecond := Ideal.mul_mem_mul hy hg2
  have hscaled : -(α * (x ^ r * q ^ s + y ^ s)) ∈ m * I := by
    have heq : (x * q ^ (s - 1)) * (z * y - α * x ^ (r - 1) * q) -
        y * (z * x * q ^ (s - 1) + α * y ^ (s - 1)) =
        -(α * (x ^ r * q ^ s + y ^ s)) := by
      linear_combination (-α) * ((q ^ (s - 1) * q) * hrpow + x ^ r * hqpow + hspow)
    rw [← heq]
    exact (m * I).sub_mem hfirst hsecond
  have hmain : x ^ r * q ^ s + y ^ s ∈ m * I := by
    have h := (m * I).mul_mem_left αinv hscaled
    have heq : αinv * -(α * (x ^ r * q ^ s + y ^ s)) =
        -(x ^ r * q ^ s + y ^ s) := by
      linear_combination (-(x ^ r * q ^ s + y ^ s)) * hα
    rw [heq] at h
    exact (m * I).neg_mem_iff.mp h
  have heq : x ^ r + y ^ s + z ^ t =
      (x ^ r * q ^ s + y ^ s) + (z ^ t - x ^ r * (x ^ a * z ^ b)) := by
    rw [hq]
    ring
  rw [heq]
  exact (m * I).add_mem hmain hcorrection

/-- Substitution of a power series into a multivariate series is compatible with
any two subsequent substitutions that agree on the inserted argument. -/
private theorem substAlgHom_substAlgHom_eq_of_substAlgHom_eq
    {R σ : Type*} [CommRing R]
    (u : MvPowerSeries σ R)
    (hu : MvPowerSeries.constantCoeff u = 0)
    (v : PowerSeries R)
    {a a' : σ → PowerSeries R}
    (ha : MvPowerSeries.HasSubst a) (ha' : MvPowerSeries.HasSubst a')
    (heq : MvPowerSeries.substAlgHom ha u = MvPowerSeries.substAlgHom ha' u) :
    MvPowerSeries.substAlgHom ha
        (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero hu) v) =
      MvPowerSeries.substAlgHom ha'
        (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero hu) v) := by
  let h := (PowerSeries.HasSubst.of_constantCoeff_zero hu).const
  have hcomp := MvPowerSeries.substAlgHom_comp_substAlgHom_apply h ha v
  have hcomp' := MvPowerSeries.substAlgHom_comp_substAlgHom_apply h ha' v
  calc
    _ = MvPowerSeries.substAlgHom (h.comp ha) v := by simpa [h, PowerSeries.substAlgHom] using hcomp
    _ = MvPowerSeries.substAlgHom (h.comp ha') v := by
      simp [heq]
    _ = _ := by simpa [h, PowerSeries.substAlgHom] using hcomp'.symm

/-- The same binomial root construction works in the three-variable ambient ring. -/
private theorem exists_root_one_add_mv_monomial (n a b : ℕ)
    (hn : 0 < n) (hb : 0 < b) :
    ∃ q : MvPowerSeries (Fin 3) ℂ,
      q ^ n = 1 + MvPowerSeries.X 0 ^ a * MvPowerSeries.X 2 ^ b ∧
      ∀ (v v' : Fin 3 → PowerSeries ℂ)
        (hv : MvPowerSeries.HasSubst v) (hv' : MvPowerSeries.HasSubst v'),
        MvPowerSeries.substAlgHom hv
            ((MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ) ^ a *
              MvPowerSeries.X 2 ^ b) =
          MvPowerSeries.substAlgHom hv'
            ((MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ) ^ a *
              MvPowerSeries.X 2 ^ b) →
        MvPowerSeries.substAlgHom hv q = MvPowerSeries.substAlgHom hv' q := by
  let u : MvPowerSeries (Fin 3) ℂ := MvPowerSeries.X 0 ^ a * MvPowerSeries.X 2 ^ b
  have hu : MvPowerSeries.constantCoeff u = 0 := by
    simp [u, hb.ne']
  let φ : PowerSeries ℂ →ₐ[ℂ] MvPowerSeries (Fin 3) ℂ :=
    PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero hu)
  let v : PowerSeries ℂ := PowerSeries.binomialSeries ℂ (1 / (n : ℂ))
  have hv : v ^ n = 1 + PowerSeries.X := by
    have hpow (z : ℂ) (k : ℕ) :
        PowerSeries.binomialSeries ℂ z ^ k =
          PowerSeries.binomialSeries ℂ ((k : ℂ) * z) := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, ih, ← PowerSeries.binomialSeries_add]
        congr 1
        push_cast
        ring
    rw [show v ^ n = PowerSeries.binomialSeries ℂ
        ((n : ℂ) * (1 / (n : ℂ))) from hpow _ n]
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [show (n : ℂ) * (1 / (n : ℂ)) = 1 by simp [hn']]
    simpa using (PowerSeries.binomialSeries_nat (A := ℂ) (R := ℂ) 1)
  refine ⟨φ v, ?_, ?_⟩
  · have h := congrArg φ hv
    simpa [φ, u, map_add, map_pow, PowerSeries.substAlgHom_X] using h
  · intro v₁ v₂ hv₁ hv₂ heq
    simpa [φ, u] using substAlgHom_substAlgHom_eq_of_substAlgHom_eq u hu v hv₁ hv₂ heq


/-- The correction degree `d = c * t - r * s` of the dual curve, for the Frobenius gap `c`,
satisfies `d + r * s = c * t` and `a * s + b * c = d`. -/
private theorem frobenius_correction_degree {r s t a b k : ℕ}
    (hineq : r * s + r * t + s * t < r * s * t)
    (ht : t = b + k * s) (ha : r + a = k * (r * s - r - s)) :
    (r * s - r - s) * t - r * s + r * s = (r * s - r - s) * t ∧
      a * s + b * (r * s - r - s) = (r * s - r - s) * t - r * s := by
  let c := r * s - r - s
  let d := c * t - r * s
  have hdeq : d + r * s = c * t := frobenius_degree_add_eq hineq
  refine ⟨hdeq, ?_⟩
  change a * s + b * c = d
  have htc := congrArg (· * c) ht
  have har := congrArg (· * s) ha
  nlinarith [htc, har, hdeq]

/-- The dual curve `(X ^ s, C α * X ^ r * q, X ^ c)` satisfies the Brieskorn equation
once `q ^ s = 1 + X ^ d`, `α ^ s = -1` and `d + r * s = c * t`. -/
private theorem dual_curve_equation_eq_zero {r s t c d : ℕ} {α : ℂ} {q : PowerSeries ℂ}
    (hq : q ^ s = 1 + PowerSeries.X ^ d) (hα : α ^ s = -1) (hdeq : d + r * s = c * t) :
    ((PowerSeries.X : PowerSeries ℂ) ^ s) ^ r + (PowerSeries.C α * PowerSeries.X ^ r * q) ^ s +
      (PowerSeries.X ^ c) ^ t = 0 := by
  have hpow : (PowerSeries.X : PowerSeries ℂ) ^ (c * t) =
      PowerSeries.X ^ (r * s) * PowerSeries.X ^ d := by
    rw [← pow_add]
    congr 1
    omega
  rw [mul_pow, mul_pow, ← map_pow, hα, hq]
  simp only [map_neg, map_one]
  rw [← pow_mul, ← pow_mul, ← pow_mul, Nat.mul_comm s r, hpow]
  ring

/-- The dual curve can be chosen with its binomial correction lifted to the
ambient ring depending only on `x` and `z`. -/
private theorem exists_brieskorn_curve_hom_dual_lifted {r s t : ℕ}
    (hr : 1 < r) (hrs : r < s) (hst : s < t)
    (hrs' : Nat.Coprime r s) (hst' : Nat.Coprime s t)
    (hineq : r * s + r * t + s * t < r * s * t) :
    let c := r * s - r - s
    ∃ (a b k : ℕ) (Q : MvPowerSeries (Fin 3) ℂ)
      (ψ : MvPowerSeries (Fin 3) ℂ →ₐ[ℂ] PowerSeries ℂ) (α : ℂ),
      0 < b ∧ t = b + k * s ∧ r + a = k * c ∧
      Q ^ s = 1 + MvPowerSeries.X 0 ^ a * MvPowerSeries.X 2 ^ b ∧
      α ^ s = -1 ∧
      ψ (MvPowerSeries.X (0 : Fin 3)) = PowerSeries.X ^ s ∧
      ψ (MvPowerSeries.X (1 : Fin 3)) =
        PowerSeries.C α * PowerSeries.X ^ r * ψ Q ∧
      ψ (MvPowerSeries.X (2 : Fin 3)) = PowerSeries.X ^ c ∧
      ψ (brieskornEquation ℂ r s t) = 0 := by
  let c := r * s - r - s
  let d := c * t - r * s
  obtain ⟨a, b, k, hb, ht, ha⟩ :=
    frobenius_correction_factorization hr hrs hst hrs' hst' hineq
  obtain ⟨hc, -⟩ := frobenius_branch_exponent hineq
  obtain ⟨hdeq, hab⟩ := frobenius_correction_degree hineq ht ha
  obtain ⟨Q, hQ, hQstable⟩ := exists_root_one_add_mv_monomial s a b (by omega) hb
  let base : Fin 3 → PowerSeries ℂ := ![PowerSeries.X ^ s, 0, PowerSeries.X ^ c]
  have hbase (i : Fin 3) : (base i).constantCoeff = 0 := by
    fin_cases i <;> simp [base] <;> omega
  let β : MvPowerSeries (Fin 3) ℂ →ₐ[ℂ] PowerSeries ℂ :=
    MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero hbase)
  let q : PowerSeries ℂ := β Q
  have hβM : β (MvPowerSeries.X 0 ^ a * MvPowerSeries.X 2 ^ b) =
      PowerSeries.X ^ d := by
    simp only [map_mul, map_pow, β, MvPowerSeries.substAlgHom_X]
    change (PowerSeries.X ^ s) ^ a * (PowerSeries.X ^ c) ^ b = _
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    simpa [c, d, mul_comm] using hab
  have hq : q ^ s = 1 + PowerSeries.X ^ d := by
    simpa [q, hβM, map_add, map_pow] using congrArg β hQ
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : ℂ) (by omega : 0 < s)
  let curve : Fin 3 → PowerSeries ℂ :=
    ![PowerSeries.X ^ s, PowerSeries.C α * PowerSeries.X ^ r * q,
      PowerSeries.X ^ c]
  have hcurve (i : Fin 3) : (curve i).constantCoeff = 0 := by
    fin_cases i <;> simp [curve] <;> omega
  let ψ : MvPowerSeries (Fin 3) ℂ →ₐ[ℂ] PowerSeries ℂ :=
    MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero hcurve)
  have hψQ : ψ Q = q :=
    hQstable curve base (MvPowerSeries.hasSubst_of_constantCoeff_zero hcurve)
      (MvPowerSeries.hasSubst_of_constantCoeff_zero hbase) (by
        simp only [map_mul, map_pow, MvPowerSeries.substAlgHom_X]
        rfl)
  have hx : ψ (MvPowerSeries.X (0 : Fin 3)) = PowerSeries.X ^ s := by
    simp only [ψ, MvPowerSeries.substAlgHom_X]
    simp [curve]
  have hy : ψ (MvPowerSeries.X (1 : Fin 3)) =
      PowerSeries.C α * PowerSeries.X ^ r * ψ Q := by
    rw [hψQ]
    simp only [ψ, MvPowerSeries.substAlgHom_X]
    simp [curve]
  have hz : ψ (MvPowerSeries.X (2 : Fin 3)) = PowerSeries.X ^ c := by
    simp only [ψ, MvPowerSeries.substAlgHom_X]
    simp [curve]
  refine ⟨a, b, k, Q, ψ, α, hb, ht, ha, hQ, hα, hx, hy, by simpa [c] using hz, ?_⟩
  simp only [brieskornEquation, map_add, map_pow, hx, hy, hz, hψQ]
  exact dual_curve_equation_eq_zero hq hα hdeq

/-- The second relation of the dual curve: with `c + s = r * (s - 1)` and `α ^ s = -1`,
the terms `X ^ (c + s) * q ^ (s - 1)` and `α * (α * X ^ r * q) ^ (s - 1)` cancel. -/
private theorem dual_curve_second_relation {r s c : ℕ} (hs : 1 ≤ s)
    (hcs : c + s = r * (s - 1)) {α : ℂ} (hα : α ^ s = -1) (q : PowerSeries ℂ) :
    PowerSeries.X ^ c * PowerSeries.X ^ s * q ^ (s - 1) +
      PowerSeries.C α * (PowerSeries.C α * PowerSeries.X ^ r * q) ^ (s - 1) = 0 := by
  have hα' : α * α ^ (s - 1) = -1 := by
    rwa [mul_comm α, ← pow_succ, Nat.sub_add_cancel hs]
  have hCpow : PowerSeries.C α * PowerSeries.C α ^ (s - 1) = -1 := by
    rw [← map_pow, ← map_mul, hα']
    simp
  calc
    _ = (1 + PowerSeries.C α * PowerSeries.C α ^ (s - 1)) *
        PowerSeries.X ^ (r * (s - 1)) * q ^ (s - 1) := by
          rw [← pow_add, hcs, mul_pow, mul_pow, ← pow_mul]
          ring
    _ = 0 := by rw [hCpow]; ring

/-- If `z ^ s - x ^ c ∈ I` and `z ^ b ∈ m`, then with `t = b + k * s` and `r + a = k * c`
the corrected power `z ^ t - x ^ r * (x ^ a * z ^ b)` lies in `m * I`. -/
private theorem pow_sub_correction_mem_mul {R : Type*} [CommRing R] (m I : Ideal R)
    (x z : R) {r s t a b c k : ℕ} (hg : z ^ s - x ^ c ∈ I) (hzb : z ^ b ∈ m)
    (ht : t = b + k * s) (ha : r + a = k * c) :
    z ^ t - x ^ r * (x ^ a * z ^ b) ∈ m * I := by
  convert Ideal.mul_mem_mul hzb
    (I.mem_of_dvd (sub_dvd_pow_sub_pow (z ^ s) (x ^ c) k) hg) using 1
  calc
    z ^ t - x ^ r * (x ^ a * z ^ b) = z ^ t - x ^ (r + a) * z ^ b := by
      rw [pow_add]
      ring
    _ = z ^ b * ((z ^ s) ^ k - (x ^ c) ^ k) := by
      rw [ht, ha]
      simp only [pow_add, pow_mul]
      ring

/-- The Frobenius gap `c = r * s - r - s` satisfies `c + r = s * (r - 1)` and
`c + s = r * (s - 1)`. -/
private theorem frobenius_gap_add_eq {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hsum : r + s < r * s) :
    r * s - r - s + r = s * (r - 1) ∧ r * s - r - s + s = r * (s - 1) := by
  let c := r * s - r - s
  have hceq : c + r + s = r * s := by
    change r * s - r - s + r + s = r * s
    omega
  change c + r = s * (r - 1) ∧ c + s = r * (s - 1)
  constructor
  · have hmul := congrArg (s * ·) (Nat.sub_add_cancel hr)
    nlinarith [hceq]
  · have hmul := congrArg (r * ·) (Nat.sub_add_cancel hs)
    nlinarith [hceq]

/-- For the lifted dual curve, the defining equation lies in the maximal
ideal times the kernel. This is stronger than merely vanishing on the curve. -/
private theorem exists_curve_kernel_equation_mem_maximal_mul {r s t : ℕ}
    (hr : 1 < r) (hrs : r < s) (hst : s < t)
    (hrs' : Nat.Coprime r s) (hst' : Nat.Coprime s t)
    (hineq : r * s + r * t + s * t < r * s * t) :
    ∃ ψ : MvPowerSeries (Fin 3) ℂ →ₐ[ℂ] PowerSeries ℂ,
      ψ (brieskornEquation ℂ r s t) = 0 ∧
      brieskornEquation ℂ r s t ∈
        IsLocalRing.maximalIdeal (MvPowerSeries (Fin 3) ℂ) * RingHom.ker ψ.toRingHom ∧
      ψ (MvPowerSeries.X (0 : Fin 3)) = PowerSeries.X ^ s ∧
      ψ (MvPowerSeries.X (2 : Fin 3)) = PowerSeries.X ^ (r * s - r - s) := by
  let c := r * s - r - s
  obtain ⟨a, b, k, Q, ψ, α, hb, ht, ha, hQ, hα, hx, hy, hz, hf⟩ :=
    exists_brieskorn_curve_hom_dual_lifted hr hrs hst hrs' hst' hineq
  let B := MvPowerSeries (Fin 3) ℂ
  let x : B := MvPowerSeries.X 0
  let y : B := MvPowerSeries.X 1
  let z : B := MvPowerSeries.X 2
  let αB : B := MvPowerSeries.C α
  let I : Ideal B := RingHom.ker ψ.toRingHom
  let m : Ideal B := IsLocalRing.maximalIdeal B
  have hαne : α ≠ 0 := by
    intro h
    simp [h, show s ≠ 0 by omega] at hα
  have hαunit : IsUnit αB := by
    apply MvPowerSeries.isUnit_iff_constantCoeff.mpr
    simpa [αB] using (isUnit_iff_ne_zero.mpr hαne)
  obtain ⟨αinv, hαinv⟩ := hαunit.exists_left_inv
  obtain ⟨hcr, hcs⟩ := frobenius_gap_add_eq (r := r) (s := s) (by omega) (by omega)
    (by have ⟨hc, _⟩ := frobenius_branch_exponent hineq; omega)
  have hC : ψ (MvPowerSeries.C α) = PowerSeries.C α := ψ.commutes α
  have hg1 : z * y - αB * x ^ (r - 1) * Q ∈ I := by
    change ψ (z * y - αB * x ^ (r - 1) * Q) = 0
    simp only [x, y, z, αB, map_sub, map_mul, map_pow, hx, hy, hz, hC]
    change PowerSeries.X ^ c * (PowerSeries.C α * PowerSeries.X ^ r * ψ Q) -
      PowerSeries.C α * (PowerSeries.X ^ s) ^ (r - 1) * ψ Q = 0
    rw [← pow_mul, ← hcr, pow_add]
    ring
  have hg2 : z * x * Q ^ (s - 1) + αB * y ^ (s - 1) ∈ I := by
    change ψ (z * x * Q ^ (s - 1) + αB * y ^ (s - 1)) = 0
    simp only [x, y, z, αB, map_add, map_mul, map_pow, hx, hy, hz, hC]
    change PowerSeries.X ^ c * PowerSeries.X ^ s * (ψ Q) ^ (s - 1) +
      PowerSeries.C α * (PowerSeries.C α * PowerSeries.X ^ r * ψ Q) ^ (s - 1) = 0
    exact dual_curve_second_relation (by omega) hcs hα (ψ Q)
  have hg3 : z ^ s - x ^ c ∈ I := by
    change ψ (z ^ s - x ^ c) = 0
    simp only [x, z, map_sub, map_pow, hx, hz, ← pow_mul]
    rw [Nat.mul_comm c s, sub_self]
  have hcorrection : z ^ t - x ^ r * (x ^ a * z ^ b) ∈ m * I :=
    pow_sub_correction_mem_mul m I x z hg3
      (m.pow_mem_of_mem (variable_mem_maximalIdeal 2) b hb) ht ha
  have heq : (brieskornEquation ℂ r s t : B) = x ^ r + y ^ s + z ^ t := rfl
  refine ⟨ψ, hf, ?_, hx, hz⟩
  rw [heq]
  exact equation_mem_maximal_mul_of_curve_relations I x y z Q αB αinv
    (by omega) (by omega) hαinv
    (variable_mem_maximalIdeal 0) (variable_mem_maximalIdeal 1)
    (by simpa [x, z] using hQ) hg1 hg2 hcorrection



/-- The monomial relation of the dual curve is not already a consequence of the
Brieskorn equation. Evaluating at `x = y = 0` detects its `z ^ s` term before
the equation's first `z` term, which occurs in degree `t`. -/
private theorem dual_curve_relation_not_mem_equation_ideal {r s t c : ℕ}
    (hr : 0 < r) (hs : 0 < s) (hc : 0 < c) (hst : s < t) :
    MvPowerSeries.X (0 : Fin 3) ^ c - MvPowerSeries.X (2 : Fin 3) ^ s ∉
      (Ideal.span {brieskornEquation ℂ r s t} : Ideal (MvPowerSeries (Fin 3) ℂ)) := by
  let a : Fin 3 → PowerSeries ℂ := ![0, 0, PowerSeries.X]
  have ha (i : Fin 3) : (a i).constantCoeff = 0 := by
    fin_cases i <;> simp [a]
  let ψ : MvPowerSeries (Fin 3) ℂ →ₐ[ℂ] PowerSeries ℂ :=
    MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)
  have hx : ψ (MvPowerSeries.X (0 : Fin 3)) = 0 := by
    simp only [ψ, MvPowerSeries.substAlgHom_X]
    simp [a]
  have hy : ψ (MvPowerSeries.X (1 : Fin 3)) = 0 := by
    simp only [ψ, MvPowerSeries.substAlgHom_X]
    simp [a]
  have hz : ψ (MvPowerSeries.X (2 : Fin 3)) = PowerSeries.X := by
    simp only [ψ, MvPowerSeries.substAlgHom_X]
    simp [a]
  intro hmem
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp hmem
  have hmap := congrArg ψ hg
  have heq : -(PowerSeries.X : PowerSeries ℂ) ^ s = ψ g * PowerSeries.X ^ t := by
    simpa [brieskornEquation, map_sub, map_add, map_pow, hx, hy, hz,
      hr.ne', hs.ne', hc.ne'] using hmap.symm
  have hcoeff := congrArg (PowerSeries.coeff s) heq
  have hnot : ¬ t ≤ s := by omega
  simp [PowerSeries.coeff_mul_X_pow', hnot] at hcoeff

/-- The dual curve's extra relation represents a nonzero element of the
hypersurface ring. -/
private theorem dual_curve_relation_ne_zero {r s t c : ℕ}
    (hr : 0 < r) (hs : 0 < s) (hc : 0 < c) (hst : s < t) :
    (Ideal.Quotient.mk (Ideal.span {brieskornEquation ℂ r s t})
      (MvPowerSeries.X (0 : Fin 3) ^ c - MvPowerSeries.X (2 : Fin 3) ^ s) :
        BrieskornHypersurface r s t) ≠ 0 :=
  fun h => dual_curve_relation_not_mem_equation_ideal hr hs hc hst
    (Ideal.Quotient.eq_zero_iff_mem.mp h)


/-- A ring map from a local ring to `ℂ⟦X⟧` sending some element to a positive power
of `X` has a nonmaximal kernel. -/
private theorem ker_not_isMaximal_of_map_eq_X_pow {A : Type*} [CommRing A] [IsLocalRing A]
    (φ : A →+* PowerSeries ℂ) {x : A} {s : ℕ} (hs : s ≠ 0)
    (hφx : φ x = PowerSeries.X ^ s) : ¬ (RingHom.ker φ).IsMaximal := by
  have hX : (PowerSeries.X : PowerSeries ℂ) ^ s ≠ 0 :=
    pow_ne_zero s PowerSeries.X_ne_zero
  have hxmax : x ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    have hunit' : IsUnit ((PowerSeries.X : PowerSeries ℂ) ^ s) := by
      rw [← hφx]
      exact hunit.map φ
    have hconstant := PowerSeries.isUnit_iff_constantCoeff.mp hunit'
    simp [hs] at hconstant
  intro hmax
  have hxker : x ∈ RingHom.ker φ := (IsLocalRing.eq_maximalIdeal hmax) ▸ hxmax
  exact hX (by simp [RingHom.mem_ker, hφx] at hxker)

/-- The same prime and height argument applies to the lifted curve map, and
records its kernel as the image of the ambient kernel. -/
private theorem dual_curve_prime_properties {r s t : ℕ}
    (hr : 1 < r) (hrs : r < s) (hst : s < t)
    (hineq : r * s + r * t + s * t < r * s * t)
    (ψ : MvPowerSeries (Fin 3) ℂ →ₐ[ℂ] PowerSeries ℂ)
    (hψ : ψ (brieskornEquation ℂ r s t) = 0)
    (hx : ψ (MvPowerSeries.X (0 : Fin 3)) = PowerSeries.X ^ s)
    (hz : ψ (MvPowerSeries.X (2 : Fin 3)) =
      PowerSeries.X ^ (r * s - r - s)) :
    ∃ φ : BrieskornHypersurface r s t →+* PowerSeries ℂ,
      (∀ v, φ (Ideal.Quotient.mk (Ideal.span {brieskornEquation ℂ r s t}) v) = ψ v) ∧
      (RingHom.ker φ).IsPrime ∧ RingHom.ker φ ≠ ⊥ ∧
      ¬ (RingHom.ker φ).IsMaximal ∧
      RingHom.ker φ = (RingHom.ker ψ.toRingHom).map
        (Ideal.Quotient.mk (Ideal.span {brieskornEquation ℂ r s t})) := by
  let : NeZero r := ⟨by omega⟩
  let : NeZero s := ⟨by omega⟩
  let : NeZero t := ⟨by omega⟩
  let c := r * s - r - s
  have ⟨hc, _⟩ := frobenius_branch_exponent hineq
  have hker : Ideal.span ({brieskornEquation ℂ r s t} :
      Set (MvPowerSeries (Fin 3) ℂ)) ≤ RingHom.ker ψ.toRingHom :=
    (Ideal.span_singleton_le_iff_mem _).mpr hψ
  let φ : BrieskornHypersurface r s t →+* PowerSeries ℂ :=
    Ideal.Quotient.lift (Ideal.span {brieskornEquation ℂ r s t}) ψ.toRingHom
      (fun x hx' => hker hx')
  let v : BrieskornHypersurface r s t :=
    Ideal.Quotient.mk (Ideal.span {brieskornEquation ℂ r s t})
      (MvPowerSeries.X (0 : Fin 3) ^ c - MvPowerSeries.X (2 : Fin 3) ^ s)
  have hv : v ≠ 0 := dual_curve_relation_ne_zero (by omega) (by omega) hc hst
  have hvker : v ∈ RingHom.ker φ := by
    change ψ (MvPowerSeries.X (0 : Fin 3) ^ c -
      MvPowerSeries.X (2 : Fin 3) ^ s) = 0
    rw [map_sub, map_pow, map_pow, hx, hz]
    simp only [← pow_mul]
    change (PowerSeries.X : PowerSeries ℂ) ^ (s * c) -
      PowerSeries.X ^ (c * s) = 0
    rw [mul_comm s c, sub_self]
  have hnzero : RingHom.ker φ ≠ ⊥ := by
    intro hbot
    rw [hbot] at hvker
    exact hv (Ideal.mem_bot.mp hvker)
  have hnmax : ¬ (RingHom.ker φ).IsMaximal :=
    ker_not_isMaximal_of_map_eq_X_pow φ
      (x := Ideal.Quotient.mk (Ideal.span {brieskornEquation ℂ r s t})
        (MvPowerSeries.X (0 : Fin 3))) (by omega) hx
  exact ⟨φ, fun _ => Ideal.Quotient.lift_mk _ _ _, RingHom.ker_isPrime φ, hnzero, hnmax,
    Ideal.ker_quotient_lift ψ.toRingHom hker⟩



/-- The lifted curve kernel cannot become principal in the hypersurface.
The equation is a minimal prime generator in the ambient domain under a UFD
assumption on the quotient, while it lies in the maximal ideal times that
kernel. -/
private theorem not_ufm_of_curve_kernel_cancellation {r s t : ℕ}
    (hr : 1 < r) (hrs : r < s) (hst : s < t)
    (hrs' : Nat.Coprime r s) (hst' : Nat.Coprime s t)
    (hineq : r * s + r * t + s * t < r * s * t) :
    ¬ UniqueFactorizationMonoid (BrieskornHypersurface r s t) := by
  intro hUFD
  let : NeZero r := ⟨by omega⟩
  let : NeZero s := ⟨by omega⟩
  let : NeZero t := ⟨by omega⟩
  let A := BrieskornHypersurface r s t
  let B := MvPowerSeries (Fin 3) ℂ
  let f : B := brieskornEquation ℂ r s t
  let J : Ideal B := Ideal.span {f}
  let π : B →+* A := Ideal.Quotient.mk J
  let : UniqueFactorizationMonoid A := hUFD
  have : IsDomain A := NoZeroDivisors.to_isDomain A
  obtain ⟨ψ, hψ, hmem, hx, hz⟩ :=
    exists_curve_kernel_equation_mem_maximal_mul hr hrs hst hrs' hst' hineq
  obtain ⟨φ, hφ, hP, hne, hnmax, hmap⟩ :=
    dual_curve_prime_properties hr hrs hst hineq ψ hψ hx hz
  let P : Ideal A := RingHom.ker φ
  let : P.IsPrime := hP
  have hheight : P.height = 1 :=
    height_one_of_nonzero_nonmaximal
      (brieskorn_ringKrullDim_le_two (by omega) (by omega)) P hne hnmax
  have hprin' : ((RingHom.ker ψ.toRingHom).map π).IsPrincipal := by
    rw [← hmap]
    exact UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hheight
  obtain ⟨g, hg⟩ := exists_pair_generators_of_quotient_principal
    (RingHom.ker ψ.toRingHom) f hψ hprin'
  have hJprime : J.IsPrime := (Ideal.Quotient.isDomain_iff_prime J).mp ‹IsDomain A›
  have hfprime : Prime f :=
    (Ideal.span_singleton_prime (equation_ne_zero (by omega) (by omega))).mp hJprime
  have hproper : Ideal.span ({f, g} : Set B) ≠ ⊤ := by
    rw [← hg]
    exact (RingHom.ker_isPrime ψ.toRingHom).ne_top
  exact irreducible_not_mem_maximal_mul_span_pair f g hfprime.irreducible hproper
    (by rwa [← hg])

/-- Apart from the `E₈` triple `(2, 3, 5)`, a Brieskorn hypersurface with ordered,
pairwise coprime exponents greater than one is not factorial. -/
@[stacks 0AEA "the general nonfactoriality assertion"]
public theorem not_uniqueFactorizationMonoid_brieskornHypersurface
    {r s t : ℕ} (hr : 1 < r) (hrs : r < s) (hst : s < t)
    (hrs' : Nat.Coprime r s) (hrt' : Nat.Coprime r t) (hst' : Nat.Coprime s t)
    (hE8 : ¬ (r = 2 ∧ s = 3 ∧ t = 5)) :
    ¬ UniqueFactorizationMonoid (BrieskornHypersurface r s t) :=
  not_ufm_of_curve_kernel_cancellation hr hrs hst hrs' hst'
    (exponent_inequality hr hrs hst hrs' hrt' hE8)

/-- The hypersurface `ℂ⟦x,y,z⟧/(x²+y⁵+z⁷)` is not factorial. -/
@[stacks 0AEA "the explicit (2, 5, 7) example"]
public theorem not_uniqueFactorizationMonoid_brieskornHypersurface_two_five_seven :
    ¬ UniqueFactorizationMonoid (BrieskornHypersurface 2 5 7) :=
  not_uniqueFactorizationMonoid_brieskornHypersurface (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide) (by norm_num)

end Stacks.MvPowerSeries.Brieskorn
