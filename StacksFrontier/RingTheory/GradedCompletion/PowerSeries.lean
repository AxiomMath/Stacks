module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.Finiteness.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A graded ring inside power series over itself

Let `Γ = ⨁_{d ≥ 0} 𝒜_d` be an `ℕ`-graded commutative algebra over a ring `k`. The map
`γ ↦ ∑_d γ_d T^d` is an injective `k`-algebra homomorphism `Γ → Γ⟦T⟧`; its image lies in the
subalgebra of power series whose coefficient of `T^d` is homogeneous of degree `d`, which is a
model of the completion `∏_d 𝒜_d` of `Γ` along its irrelevant ideal. Power series of this shape
are compared through their lowest-degree coefficients.

## Main definitions

* `Stacks.GradedCompletion.toPowerSeries`: the homomorphism `γ ↦ ∑_d γ_d T^d`.
* `Stacks.GradedCompletion.homogeneousSeries`: the subalgebra of `Γ⟦T⟧` of series whose
  coefficient of `T^d` lies in `𝒜_d`.

## Main results

* `Stacks.GradedCompletion.toPowerSeries_injective`: the map `γ ↦ ∑_d γ_d T^d` is injective.
* `Stacks.GradedCompletion.mem_pow_smul_top_of_decompose_eq_zero`: if `Γ` is a finite module over
  a polynomial ring whose variables map to degree one, then there is `D` such that every element
  of `Γ` with vanishing components in degrees `< N + D` lies in `(X)^N Γ`.
* `Stacks.GradedCompletion.exists_homogeneous_of_series_equation`: if `Γ` is a domain, `p ≥ 2`,
  `α, β ∈ 𝒜_d` with `β ≠ 0`, and `β (u^p - u v^{p-1}) = α v^p` for series `u, v ≠ 0` with
  homogeneous coefficients, then the same equation has a solution `u₀, v₀ ∈ 𝒜_{d'}`, `v₀ ≠ 0`, in
  `Γ`: compare the coefficients in the lowest degree where `u` or `v` is nonzero.
-/

@[expose] public section

open DirectSum PowerSeries

namespace Stacks.GradedCompletion

variable {k Γ : Type*} [CommRing k] [CommRing Γ] [Algebra k Γ] (𝒜 : ℕ → Submodule k Γ)
  [GradedAlgebra 𝒜]

/-! ### The homomorphism `γ ↦ ∑_d γ_d T^d` -/

/-- The `k`-algebra homomorphism `Γ → Γ⟦T⟧` sending `γ` to `∑_d γ_d T^d`, where `γ_d` is the
degree-`d` component of `γ`. -/
noncomputable def toPowerSeries : Γ →ₐ[k] PowerSeries Γ where
  toFun γ := PowerSeries.mk fun d => (decompose 𝒜 γ d : Γ)
  map_one' := by
    ext d
    rw [coeff_mk, coeff_one]
    split_ifs with h
    · subst h
      exact decompose_of_mem_same 𝒜 (SetLike.one_mem_graded 𝒜)
    · exact decompose_of_mem_ne 𝒜 (SetLike.one_mem_graded 𝒜) (Ne.symm h)
  map_mul' x y := by
    ext d
    rw [coeff_mk, coeff_mul, decompose_mul, coe_mul_apply_eq_sum_antidiagonal]
    simp only [coeff_mk]
  map_zero' := by
    ext d
    simp
  map_add' x y := by
    ext d
    simp
  commutes' c := by
    ext d
    rw [coeff_mk, PowerSeries.algebraMap_apply, coeff_C]
    split_ifs with h
    · subst h
      exact decompose_of_mem_same 𝒜 (SetLike.algebraMap_mem_graded 𝒜 c)
    · exact decompose_of_mem_ne 𝒜 (SetLike.algebraMap_mem_graded 𝒜 c) (Ne.symm h)

/-- The coefficient of `T^d` in `toPowerSeries 𝒜 γ` is the degree-`d` component of `γ`. -/
@[simp]
theorem coeff_toPowerSeries (γ : Γ) (d : ℕ) :
    coeff d (toPowerSeries 𝒜 γ) = (decompose 𝒜 γ d : Γ) :=
  coeff_mk d fun d => (decompose 𝒜 γ d : Γ)

/-- An element `γ ∈ 𝒜 d` is sent to the monomial `γ T^d`. -/
theorem toPowerSeries_of_mem {γ : Γ} {d : ℕ} (hγ : γ ∈ 𝒜 d) :
    toPowerSeries 𝒜 γ = monomial d γ := by
  ext m
  rw [coeff_toPowerSeries, coeff_monomial]
  split_ifs with h
  · subst h
    exact decompose_of_mem_same 𝒜 hγ
  · exact decompose_of_mem_ne 𝒜 hγ (Ne.symm h)

/-- The homomorphism `γ ↦ ∑_d γ_d T^d` is injective. -/
theorem toPowerSeries_injective : Function.Injective (toPowerSeries 𝒜) := by
  rw [injective_iff_map_eq_zero]
  intro γ hγ
  apply (decompose 𝒜).injective
  rw [decompose_zero]
  ext d
  have := congrArg (coeff d) hγ
  rwa [coeff_toPowerSeries, map_zero] at this

/-- `toPowerSeries 𝒜 γ` is divisible by `T^N` exactly when the components of `γ` in degrees
below `N` vanish. -/
theorem X_pow_dvd_toPowerSeries_iff {γ : Γ} {N : ℕ} :
    X ^ N ∣ toPowerSeries 𝒜 γ ↔ ∀ d < N, (decompose 𝒜 γ d : Γ) = 0 := by
  simp [X_pow_dvd_iff]

/-! ### Series with homogeneous coefficients -/

/-- The subalgebra of `Γ⟦T⟧` of power series whose coefficient of `T^d` lies in `𝒜 d` for every
`d`: the formal sums `∑_d γ_d` with `γ_d ∈ 𝒜_d`. -/
@[sga "6 V 1.11" "partial"]
def homogeneousSeries : Subalgebra k (PowerSeries Γ) where
  carrier := {f | ∀ d, coeff d f ∈ 𝒜 d}
  mul_mem' {f g} hf hg d := by
    rw [coeff_mul]
    refine Submodule.sum_mem _ fun ij hij => ?_
    obtain ⟨i, j⟩ := ij
    rw [Finset.mem_antidiagonal] at hij
    subst hij
    exact SetLike.mul_mem_graded (hf i) (hg j)
  add_mem' {f g} hf hg d := by
    rw [map_add]
    exact add_mem (hf d) (hg d)
  algebraMap_mem' c d := by
    rw [PowerSeries.algebraMap_apply, coeff_C]
    split_ifs with h
    · subst h
      exact SetLike.algebraMap_mem_graded 𝒜 c
    · exact zero_mem _

/-- A power series lies in `homogeneousSeries 𝒜` if and only if its coefficient of `T^d` lies in
`𝒜 d` for every `d`. -/
theorem mem_homogeneousSeries {f : PowerSeries Γ} :
    f ∈ homogeneousSeries 𝒜 ↔ ∀ d, coeff d f ∈ 𝒜 d :=
  Iff.rfl

/-- The image of `toPowerSeries 𝒜` lies in `homogeneousSeries 𝒜`. -/
theorem toPowerSeries_mem_homogeneousSeries (γ : Γ) :
    toPowerSeries 𝒜 γ ∈ homogeneousSeries 𝒜 := fun d => by
  rw [coeff_toPowerSeries]
  exact (decompose 𝒜 γ d).2

/-! ### Lowest-degree comparison -/

/-- **Lowest-degree comparison.** Let `Γ` be a domain and `p ≥ 2`. Let `α, β ∈ 𝒜_d` with
`β ≠ 0`, and let `u, v` be power series with homogeneous coefficients, `v ≠ 0`, satisfying
`β (u^p - u v^{p-1}) = α v^p`. Then there are `u₀, v₀ ∈ 𝒜_{d'}` with `v₀ ≠ 0` and
`β (u₀^p - u₀ v₀^{p-1}) = α v₀^p`. -/
theorem exists_homogeneous_of_series_equation [IsDomain Γ] {p : ℕ} (hp : 2 ≤ p) {α β : Γ}
    (hβ : β ≠ 0) {u v : PowerSeries Γ} (hu : u ∈ homogeneousSeries 𝒜)
    (hv : v ∈ homogeneousSeries 𝒜) (hv0 : v ≠ 0)
    (h : C β * (u ^ p - u * v ^ (p - 1)) = C α * v ^ p) :
    ∃ (d' : ℕ) (u₀ v₀ : Γ), u₀ ∈ 𝒜 d' ∧ v₀ ∈ 𝒜 d' ∧ v₀ ≠ 0 ∧
      β * (u₀ ^ p - u₀ * v₀ ^ (p - 1)) = α * v₀ ^ p := by
  classical
  have hex : ∃ m, coeff m u ≠ 0 ∨ coeff m v ≠ 0 := by
    obtain ⟨m, hm⟩ := (exists_coeff_ne_zero_iff_ne_zero (φ := v)).mpr hv0
    exact ⟨m, Or.inr hm⟩
  obtain ⟨c, hspec, hlow⟩ : ∃ c, (coeff c u ≠ 0 ∨ coeff c v ≠ 0) ∧
      ∀ m < c, coeff m u = 0 ∧ coeff m v = 0 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => by simpa using Nat.find_min hex hm⟩
  obtain ⟨u', rfl⟩ : X ^ c ∣ u := X_pow_dvd_iff.mpr fun m hm => (hlow m hm).1
  obtain ⟨v', rfl⟩ : X ^ c ∣ v := X_pow_dvd_iff.mpr fun m hm => (hlow m hm).2
  have hc (f : PowerSeries Γ) : coeff c (X ^ c * f) = constantCoeff f := by
    rw [coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply]
  rw [hc, hc] at hspec
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h ⊢
  have hXne : (X : PowerSeries Γ) ^ (c * (q + 1)) ≠ 0 := pow_ne_zero _ X_ne_zero
  have h' : C β * (u' ^ (q + 1) - u' * v' ^ q) = C α * v' ^ (q + 1) := by
    apply mul_left_cancel₀ hXne
    have e1 : (X : PowerSeries Γ) ^ (c * (q + 1)) * (C β * (u' ^ (q + 1) - u' * v' ^ q)) =
        C β * ((X ^ c * u') ^ (q + 1) - X ^ c * u' * (X ^ c * v') ^ q) := by
      ring
    have e2 : (X : PowerSeries Γ) ^ (c * (q + 1)) * (C α * v' ^ (q + 1)) =
        C α * (X ^ c * v') ^ (q + 1) := by
      ring
    rw [e1, e2, h]
  have h0 := congrArg constantCoeff h'
  simp only [map_mul, map_sub, map_pow, constantCoeff_C] at h0
  refine ⟨c, constantCoeff u', constantCoeff v', ?_, ?_, ?_, h0⟩
  · rw [← hc]
    exact hu c
  · rw [← hc]
    exact hv c
  · intro hv'
    rcases hspec with hu' | hv''
    · rw [hv', zero_pow (by omega), mul_zero, sub_zero, zero_pow (by omega), mul_zero] at h0
      exact hu' (pow_eq_zero_iff (by omega) |>.mp ((mul_eq_zero.mp h0).resolve_left hβ))
    · exact hv'' hv'

/-! ### High degrees lie in high powers of the ideal of variables -/

section Polynomial

variable {σ : Type*} [Algebra (MvPolynomial σ k) Γ] [IsScalarTower k (MvPolynomial σ k) Γ]

/-- If the variables map to elements of degree one, then a homogeneous polynomial of degree `j`
maps to an element of degree `j`. -/
theorem algebraMap_mem_of_isHomogeneous
    (hX : ∀ i, algebraMap (MvPolynomial σ k) Γ (MvPolynomial.X i) ∈ 𝒜 1)
    {q : MvPolynomial σ k} {j : ℕ} (hq : q.IsHomogeneous j) :
    algebraMap (MvPolynomial σ k) Γ q ∈ 𝒜 j := by
  classical
  have key : ∀ x : σ →₀ ℕ, x.degree = j →
      algebraMap (MvPolynomial σ k) Γ (MvPolynomial.monomial x (1 : k)) ∈ 𝒜 j := by
    intro x hx
    simp only [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, map_finsuppProd, map_pow]
    have := SetLike.prod_pow_mem_graded 𝒜 (F := x.support) (fun _ => 1)
      (fun i => algebraMap (MvPolynomial σ k) Γ (MvPolynomial.X i)) x (fun i _ => hX i)
    rw [Finsupp.prod]
    convert this using 2
    simp [Finsupp.degree_apply, ← hx]
  rw [q.as_sum, map_sum]
  refine Submodule.sum_mem _ fun x hx => ?_
  have hdeg : x.degree = j := by
    rw [← hq (MvPolynomial.mem_support_iff.mp hx)]
    simp [Finsupp.degree_eq_weight_one, Pi.one_def]
  rw [← mul_one (MvPolynomial.coeff x q), ← MvPolynomial.C_mul_monomial, map_mul,
    ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (key x hdeg)

/-- The degree-`j` component of the image of a polynomial is the image of its degree-`j`
homogeneous component. -/
theorem decompose_algebraMap
    (hX : ∀ i, algebraMap (MvPolynomial σ k) Γ (MvPolynomial.X i) ∈ 𝒜 1)
    (q : MvPolynomial σ k) (j : ℕ) :
    (decompose 𝒜 (algebraMap (MvPolynomial σ k) Γ q) j : Γ) =
      algebraMap (MvPolynomial σ k) Γ (MvPolynomial.homogeneousComponent j q) := by
  classical
  conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent q]
  rw [map_sum, decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum]
  have hmem : ∀ i, algebraMap (MvPolynomial σ k) Γ (MvPolynomial.homogeneousComponent i q) ∈ 𝒜 i :=
    fun i => algebraMap_mem_of_isHomogeneous 𝒜 hX
      (MvPolynomial.homogeneousComponent_isHomogeneous i q)
  rw [Finset.sum_eq_single j]
  · exact decompose_of_mem_same 𝒜 (hmem j)
  · intro i _ hij
    exact decompose_of_mem_ne 𝒜 (hmem i) hij
  · intro hj
    rw [Finset.mem_range, not_lt] at hj
    rw [MvPolynomial.homogeneousComponent_eq_zero j q (by omega), map_zero]
    simp

/-- **High degrees lie in high powers of the ideal of variables.** Let `Γ` be a finite module over
`MvPolynomial σ k` through an algebra map sending each variable into `𝒜 1`. Then there is `D`
such that every element of `Γ` whose components in degrees below `N + D` vanish lies in
`(X)^N Γ`, for every `N`. -/
theorem mem_pow_smul_top_of_decompose_eq_zero [Module.Finite (MvPolynomial σ k) Γ]
    (hX : ∀ i, algebraMap (MvPolynomial σ k) Γ (MvPolynomial.X i) ∈ 𝒜 1) :
    ∃ D : ℕ, ∀ (N : ℕ) (γ : Γ), (∀ d < N + D, (decompose 𝒜 γ d : Γ) = 0) →
      γ ∈ MvPolynomial.idealOfVars σ k ^ N • (⊤ : Submodule (MvPolynomial σ k) Γ) := by
  classical
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := MvPolynomial σ k) (M := Γ)
  obtain ⟨D, hD⟩ : ∃ D : ℕ, ∀ g ∈ G, ∀ i, D ≤ i → (decompose 𝒜 g i : Γ) = 0 := by
    refine ⟨G.sup fun g => (decompose 𝒜 g).support.sup id + 1, fun g hg i hi => ?_⟩
    by_contra hne
    have hmem : i ∈ (decompose 𝒜 g).support := by
      rw [DFinsupp.mem_support_iff]
      exact fun h => hne (by rw [h, ZeroMemClass.coe_zero])
    have h1 : i ≤ (decompose 𝒜 g).support.sup id := Finset.le_sup (f := id) hmem
    have h2 : (decompose 𝒜 g).support.sup id + 1 ≤
        G.sup fun g => (decompose 𝒜 g).support.sup id + 1 :=
      Finset.le_sup (f := fun g => (decompose 𝒜 g).support.sup id + 1) hg
    omega
  let v : G × Fin D → Γ := fun gi => decompose 𝒜 (gi.1 : Γ) gi.2
  have hv : Submodule.span (MvPolynomial σ k) (Set.range v) = ⊤ := by
    rw [eq_top_iff, ← hG, Submodule.span_le]
    intro g hg
    have : g = ∑ i : Fin D, v (⟨g, hg⟩, i) := by
      conv_lhs => rw [← sum_support_decompose 𝒜 g]
      rw [Finset.sum_subset (s₂ := (Finset.range D)) ?_ ?_]
      · exact (Finset.sum_range fun i => (decompose 𝒜 g i : Γ))
      · intro i hi
        rw [Finset.mem_range]
        by_contra hiD
        exact (DFinsupp.mem_support_iff.mp hi) (Subtype.ext (hD g hg i (by omega)))
      · intro i _ hi
        rw [DFinsupp.notMem_support_iff.mp hi, ZeroMemClass.coe_zero]
    rw [SetLike.mem_coe, this]
    exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨_, rfl⟩
  have hvmem : ∀ gi, v gi ∈ 𝒜 gi.2 := fun gi => (decompose 𝒜 (gi.1 : Γ) gi.2).2
  have hhom : ∀ N m, N + D ≤ m → ∀ y ∈ 𝒜 m,
      y ∈ MvPolynomial.idealOfVars σ k ^ N • (⊤ : Submodule (MvPolynomial σ k) Γ) := by
    intro N m hm y hy
    have hy' : y ∈ Submodule.span (MvPolynomial σ k) (Set.range v) := by rw [hv]; trivial
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hy'
    rw [← decompose_of_mem_same 𝒜 hy, decompose_sum, DFinsupp.finsetSum_apply,
      Submodule.coe_sum]
    refine Submodule.sum_mem _ fun gi _ => ?_
    have hle : (gi.2 : ℕ) ≤ m := by have := gi.2.2; omega
    rw [Algebra.smul_def (c gi) (v gi), coe_decompose_mul_of_right_mem_of_le 𝒜 (hvmem gi) hle,
      decompose_algebraMap 𝒜 hX, ← Algebra.smul_def]
    refine Submodule.smul_mem_smul ?_ trivial
    rw [MvPolynomial.mem_pow_idealOfVars_iff']
    intro x hx
    rw [MvPolynomial.coeff_homogeneousComponent, if_neg]
    have := gi.2.2
    omega
  refine ⟨D, fun N γ hγ => ?_⟩
  rw [← sum_support_decompose 𝒜 γ]
  refine Submodule.sum_mem _ fun m hm => ?_
  refine hhom N m ?_ _ (decompose 𝒜 γ m).2
  by_contra hlt
  exact (DFinsupp.mem_support_iff.mp hm) (Subtype.ext (hγ m (by omega)))

end Polynomial

end Stacks.GradedCompletion
