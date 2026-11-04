module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Examples.AffineSpaceDeRhamTopDegree

/-!
# The class of `η` in the top cohomology of the de Rham complex of affine space

The example of [Stacks, Tag 07LK] closes by remarking that `p^N η` is not in the image of `d`
for any `N`, and that this "implies that `η` generates a copy of `𝐐_p`" inside `H^r`.  This
module proves, for every `r > 0` and for the complex `D → Ω¹_D → ⋯ → Ω^r_D` of
`Crystalline.AffineSpaceCrystallineSetup.deRhamComplexNat`, where
`η = ∑_{e ≥ 0} p^e x_1^{p^e - 1} ⋯ x_r^{p^e - 1} dx_1 ∧ ⋯ ∧ dx_r`:

* `Crystalline.AffineSpaceCrystallineSetup.smul_etaTop_notMem_range`: no nonzero `𝐙_p`-multiple
  of `η` is exact, in particular `p^N η` is not;
* `Crystalline.AffineSpaceCrystallineSetup.injective_homologyClassTop_smul_etaTop`: hence
  `a ↦ a[η]` embeds `𝐙_p` into `H^r`, and the class `[η]` is divisible by every power of `p`
  (`Crystalline.AffineSpaceCrystallineSetup.exists_ne_zero_forall_eq_pow_nsmul_homology_top`).

## The quoted remark, read literally, fails

The divisibility of `[η]` is *not* compatible: there is no `x ∈ H^r` with `p x = [η]` that is
itself divisible by every power of `p`
(`Crystalline.AffineSpaceCrystallineSetup.not_exists_pow_smul_eq_etaTop`), and so no additive
map `𝐐_p → H^r` sends `1` to `[η]`
(`Crystalline.AffineSpaceCrystallineSetup.not_exists_padic_homology_top`).  Indeed, write `c_e`
for the coefficient of `x^{m(p^e - 1)} dx_1 ∧ ⋯ ∧ dx_r`.  If `p ξ - η = d y` and
`ξ = p^e ζ_e + d z_e` for every `e`, then `p^e` divides `c_e(ξ)`, because it divides `c_e` of
every exact form; so `c_e(d y) = p c_e(ξ) - p^e` is `p^e` times a unit for every `e`, while for
all large `e` the coefficient `c_e(d y)` is divisible by `p^{e+1}`.  So `[η]` lies in `p^t H^r`
for every `t` and generates a copy of `𝐙_p`, but it does not generate a copy of `𝐐_p`.

## References

* [Stacks Project, Tag 07LK](https://stacks.math.columbia.edu/tag/07LK)
-/

@[expose] public noncomputable section

namespace Crystalline

namespace AffineSpaceCrystallineSetup

variable (T : AffineSpaceCrystallineSetup) {s : ℕ} (hs : T.r = s + 1)

/-- The class map `Ω^r_D → H^r` onto the top cohomology, for `r = s + 1`: a surjective additive
map whose kernel is the image of `d : Ω^{r-1}_D → Ω^r_D`. -/
public def homologyClassTop : T.completedForms (s + 1) →+ T.deRhamComplexNat.homology T.r :=
  Classical.choose (T.exists_surjective_homologyClass_top hs)

/-- The class map onto the top cohomology is surjective. -/
public theorem surjective_homologyClassTop : Function.Surjective (T.homologyClassTop hs) :=
  (Classical.choose_spec (T.exists_surjective_homologyClass_top hs)).1

/-- A form of `Ω^r_D` has zero class in `H^r` exactly when it is exact. -/
public theorem homologyClassTop_eq_zero_iff (x : T.completedForms (s + 1)) :
    T.homologyClassTop hs x = 0 ↔ x ∈ LinearMap.range (T.completedDifferential s) :=
  (Classical.choose_spec (T.exists_surjective_homologyClass_top hs)).2 x

/-- The source's `η = ∑_{e ≥ 0} p^e x_1^{p^e - 1} ⋯ x_r^{p^e - 1} dx_1 ∧ ⋯ ∧ dx_r` in
`Ω^r_D`. -/
public def etaTop : T.completedForms (s + 1) := T.series hs fun e ↦ T.p ^ e - 1

/-- The coefficient of `η` at `x^{m(p^e - 1)} dx_1 ∧ ⋯ ∧ dx_r` is `p^e`. -/
public theorem topCoeff_etaTop (e : ℕ) :
    T.topCoeff hs (T.diagMonomial (T.p ^ e - 1)) (T.etaTop hs) = (T.p : T.A) ^ e :=
  T.topCoeff_series hs (T.injective_eta) e

/-- `p` does not divide `1` in `𝐙_p`. -/
private lemma not_p_dvd_one : ¬ (T.p : T.A) ∣ 1 :=
  fun h ↦ PadicInt.p_nonunit (p := T.p) (isUnit_of_dvd_one h)

/-- Powers of `p` are nonzero in `𝐙_p`. -/
private lemma natCast_pow_ne_zero (k : ℕ) : (T.p : T.A) ^ k ≠ 0 :=
  pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : T.p.Prime).ne_zero)

/-- Forms with equal classes in `H^r` differ by an exact form. -/
private lemma sub_mem_range_of_homologyClassTop_eq {x y : T.completedForms (s + 1)}
    (h : T.homologyClassTop hs x = T.homologyClassTop hs y) :
    x - y ∈ LinearMap.range (T.completedDifferential s) := by
  rw [← T.homologyClassTop_eq_zero_iff hs, map_sub, h, sub_self]

/-- **No nonzero `𝐙_p`-multiple of `η` is exact.**  If `a = p^v u` with `u` a unit and
`a η = d y`, then the coefficient `p^{e+v} u` of `a η` at `x^{m(p^e - 1)} dx_1 ∧ ⋯ ∧ dx_r` is
divisible by `p^{e+v+1}` for all large `e`. -/
public theorem smul_etaTop_notMem_range {a : T.A} (ha : a ≠ 0) :
    a • T.etaTop hs ∉ LinearMap.range (T.completedDifferential s) := by
  rintro ⟨y, hy⟩
  obtain ⟨B, hB⟩ :=
    T.exists_pow_add_dvd_topCoeff_completedDifferential hs y (a.valuation + 1)
  have h1 := hB B le_rfl
  generalize hv : a.valuation = v at h1
  rw [hy, map_smul, topCoeff_etaTop, smul_eq_mul, PadicInt.unitCoeff_spec ha, hv] at h1
  have h2 : (T.p : T.A) ^ (B + v) * T.p ∣
      (T.p : T.A) ^ (B + v) * (PadicInt.unitCoeff ha : T.A) := by
    convert h1 using 1 <;> ring
  rw [mul_dvd_mul_iff_left (T.natCast_pow_ne_zero _)] at h2
  have h3 := dvd_mul_of_dvd_left h2 (↑(PadicInt.unitCoeff ha)⁻¹ : T.A)
  rw [Units.mul_inv] at h3
  exact T.not_p_dvd_one h3

/-- **`p^N η` is not exact, for any `N`.** -/
public theorem pow_smul_etaTop_notMem_range (N : ℕ) :
    (T.p : T.A) ^ N • T.etaTop hs ∉ LinearMap.range (T.completedDifferential s) :=
  T.smul_etaTop_notMem_range hs (T.natCast_pow_ne_zero N)

/-- **`η` generates a copy of `𝐙_p` in `H^r`**: `a ↦ [a η]` is injective. -/
public theorem injective_homologyClassTop_smul_etaTop :
    Function.Injective fun a : T.A ↦ T.homologyClassTop hs (a • T.etaTop hs) := by
  intro a b hab
  by_contra hne
  exact T.smul_etaTop_notMem_range hs (sub_ne_zero.mpr hne)
    (by rw [sub_smul]; exact T.sub_mem_range_of_homologyClassTop_eq hs hab)

/-- **The class of `η` has no compatible system of `p`-power roots**: there is no `x ∈ H^r`
with `p x = [η]` that is divisible by every power of `p`. -/
public theorem not_exists_pow_smul_eq_etaTop :
    ¬ ∃ x : T.deRhamComplexNat.homology T.r, T.p • x = T.homologyClassTop hs (T.etaTop hs) ∧
      ∀ e : ℕ, ∃ z, (T.p ^ e) • z = x := by
  rintro ⟨x, hx, hdiv⟩
  obtain ⟨ξ, rfl⟩ := T.surjective_homologyClassTop hs x
  have hcast : ∀ (n : ℕ) (w : T.completedForms (s + 1)), n • w = (n : T.A) • w :=
    fun n w ↦ (Nat.cast_smul_eq_nsmul T.A n w).symm
  have hξ : T.p • ξ - T.etaTop hs ∈ LinearMap.range (T.completedDifferential s) := by
    exact T.sub_mem_range_of_homologyClassTop_eq hs (by rw [map_nsmul, hx])
  obtain ⟨y, hy⟩ := hξ
  have hdvd : ∀ e : ℕ, (T.p : T.A) ^ e ∣ T.topCoeff hs (T.diagMonomial (T.p ^ e - 1)) ξ := by
    intro e
    obtain ⟨z, hz⟩ := hdiv e
    obtain ⟨ζ, rfl⟩ := T.surjective_homologyClassTop hs z
    have hmem : (T.p ^ e) • ζ - ξ ∈ LinearMap.range (T.completedDifferential s) := by
      exact T.sub_mem_range_of_homologyClassTop_eq hs (by rw [map_nsmul, hz])
    obtain ⟨w, hw⟩ := hmem
    have h1 := T.pow_dvd_topCoeff_completedDifferential hs w e
    rw [hw, map_sub, hcast, map_smul, smul_eq_mul, Nat.cast_pow] at h1
    have h2 := (dvd_mul_right ((T.p : T.A) ^ e)
      (T.topCoeff hs (T.diagMonomial (T.p ^ e - 1)) ζ)).sub h1
    rwa [sub_sub_cancel] at h2
  obtain ⟨B, hB⟩ := T.exists_pow_succ_dvd_topCoeff_completedDifferential hs y
  have h1 := hB B le_rfl
  rw [hy, map_sub, hcast, map_smul, smul_eq_mul, topCoeff_etaTop] at h1
  obtain ⟨c, hc⟩ := hdvd B
  obtain ⟨d, hd⟩ := h1
  rw [hc] at hd
  have h3 : (T.p : T.A) ^ B * 1 = (T.p : T.A) ^ B * (T.p * (c - d)) := by
    rw [mul_one]
    linear_combination -hd
  exact T.not_p_dvd_one ⟨c - d, mul_left_cancel₀ (T.natCast_pow_ne_zero B) h3⟩

/-- **No additive map `𝐐_p → H^r` sends `1` to the class of `η`.**  So the closing remark of
[Stacks, Tag 07LK], that `η` "generates a copy of `𝐐_p`" in the top cohomology, fails as
stated: the image of `p^{-1}` would be an `x` with `p x = [η]` divisible by every power of `p`,
which `Crystalline.AffineSpaceCrystallineSetup.not_exists_pow_smul_eq_etaTop` excludes.  What
holds is that `[η]` generates a copy of `𝐙_p`
(`Crystalline.AffineSpaceCrystallineSetup.injective_homologyClassTop_smul_etaTop`) and lies in
`p^t H^r` for every `t`. -/
public theorem not_exists_padic_homology_top :
    ¬ ∃ f : ℚ_[T.p] →+ T.deRhamComplexNat.homology T.r,
      f 1 = T.homologyClassTop hs (T.etaTop hs) := by
  rintro ⟨f, hf⟩
  have hp0 : (T.p : ℚ_[T.p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : T.p.Prime).ne_zero
  refine T.not_exists_pow_smul_eq_etaTop hs ⟨f (T.p : ℚ_[T.p])⁻¹, ?_, fun e ↦ ?_⟩
  · rw [← hf, ← map_nsmul, nsmul_eq_mul, mul_inv_cancel₀ hp0]
  · refine ⟨f ((T.p : ℚ_[T.p]) ^ (e + 1))⁻¹, ?_⟩
    rw [← map_nsmul, nsmul_eq_mul, Nat.cast_pow, pow_succ, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ hp0), one_mul]

end AffineSpaceCrystallineSetup

end Crystalline

end
