module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorFirstCohomology
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.StandardNodalModelOrigin
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.ModelComparison
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineBaseCohomology
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# The blowup of the standard nodal model in its singular point has no first cohomology

Let `A = R[x, y]/(xy - πⁿ)` with `n ≥ 2` and `𝔪 = (π, x, y)`. The ideal `J = (x + y, π)` is a
reduction of `𝔪` with reduction number one, `𝔪² = J 𝔪`: indeed `x² = (x + y)x - π · πⁿ⁻¹`,
`y² = (x + y)y - π · πⁿ⁻¹` and `xy = π · πⁿ⁻¹`. Consequently the blowup `Proj(⨁ 𝔪ᵏ)` of
`Spec A` in `𝔪` is covered by the two affine charts `D₊((x + y)⁽¹⁾)` and `D₊(π⁽¹⁾)`, and every
function on their intersection is a sum of functions on the two charts, so that
`H¹(Bl, 𝒪) = 0`. This is the cohomological half of the "explicit calculation" the proof of
[Stacks, Tag 0E97] leaves to the reader for the blowup "`X₁ → X₀`" of [Stacks, Tag 0CDC].

## Main results

* `Stacks.Blowup.exists_awayMap_add_awayMap_eq_of_reduction`: in a graded ring with
  `𝒜ₖ₊₁ = f 𝒜ₖ + g 𝒜ₖ` for `k ≥ 1`, every element of `A_{(fg)}` is a sum of an element of
  `A_{(f)}` and one of `A_{(g)}`.
* `Stacks.Blowup.isZero_Hgroup_one_proj_reesGrading_of_sq_le`: `H¹(Proj(⨁ Iᵏ), 𝒪) = 0` when
  `I² ≤ (a, b) I` for some `a, b ∈ I`.
* `Stacks.isZero_Hgroup_one_blowUp_nodalModelOriginPoint`: `H¹ = 0` for the blowup of the
  standard nodal model of exponent `n ≥ 2` in its origin.

## References

* [Stacks Project, Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC)
* [Stacks Project, Tag 0E97](https://stacks.math.columbia.edu/tag/0E97)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open HomogeneousLocalization

universe u

namespace Stacks.Blowup

section Algebra

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A)
  [_root_.GradedAlgebra 𝒜] {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)

include hf hg in
/-- The product of two elements of degree one has degree two. -/
theorem mul_mem_two : f * g ∈ 𝒜 2 := by
  simpa using SetLike.mul_mem_graded hf hg

include hf hg in
/-- If `s` has degree `a + b`, then `s fᵇ gᵃ` has degree `2(a + b)`. -/
theorem fracFG_mem {a b : ℕ} {s : A} (hs : s ∈ 𝒜 (a + b)) :
    s * f ^ b * g ^ a ∈ 𝒜 ((a + b) • 2) := by
  convert SetLike.mul_mem_graded (SetLike.mul_mem_graded hs (SetLike.pow_mem_graded b hf))
    (SetLike.pow_mem_graded a hg) using 2
  simp only [smul_eq_mul, mul_one]
  ring

/-- The element `s / (fᵃ gᵇ)` of `A_{(fg)}`, written `s fᵇ gᵃ / (fg)ᵃ⁺ᵇ`. -/
def fracFG (a b : ℕ) (s : A) (hs : s ∈ 𝒜 (a + b)) : Away 𝒜 (f * g) :=
  Away.mk 𝒜 (mul_mem_two 𝒜 hf hg) (a + b) (s * f ^ b * g ^ a) (fracFG_mem 𝒜 hf hg hs)

/-- The image of `A_{(f)} × A_{(g)}` in `A_{(fg)}`, as a predicate. -/
def IsSumOfCharts (z : Away 𝒜 (f * g)) : Prop :=
  ∃ (z₀ : Away 𝒜 f) (z₁ : Away 𝒜 g),
    z = awayMap 𝒜 hg rfl z₀ + awayMap 𝒜 hf (mul_comm f g) z₁

/-- The image of `A_{(f)} × A_{(g)}` in `A_{(fg)}` is closed under addition. -/
theorem isSumOfCharts_add {z w : Away 𝒜 (f * g)} (hz : IsSumOfCharts 𝒜 hf hg z)
    (hw : IsSumOfCharts 𝒜 hf hg w) : IsSumOfCharts 𝒜 hf hg (z + w) := by
  obtain ⟨z₀, z₁, rfl⟩ := hz
  obtain ⟨w₀, w₁, rfl⟩ := hw
  exact ⟨z₀ + w₀, z₁ + w₁, by rw [map_add, map_add]; abel⟩

/-- Two fractions `x / hᵐ` and `y / hⁿ` in `A_{(h)}` are equal if `x hⁿ = y hᵐ`. -/
private theorem away_mk_eq_away_mk {h : A} {d m n : ℕ} (hh : h ∈ 𝒜 d) {x y : A}
    (hx : x ∈ 𝒜 (m • d)) (hy : y ∈ 𝒜 (n • d)) (e : x * h ^ n = y * h ^ m) :
    Away.mk 𝒜 hh m x hx = Away.mk 𝒜 hh n y hy := by
  ext
  simp only [Away.val_mk]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simpa [mul_comm] using e⟩

/-- If `𝒜ₖ₊₁ = f 𝒜ₖ + g 𝒜ₖ` for every `k ≥ 1`, then every element `s / (fᵃ gᵇ)` of `A_{(fg)}`
is a sum of an element of `A_{(f)}` and one of `A_{(g)}`. -/
theorem isSumOfCharts_fracFG
    (hred : ∀ k, 1 ≤ k → ∀ s ∈ 𝒜 (k + 1), ∃ p ∈ 𝒜 k, ∃ q ∈ 𝒜 k, s = f * p + g * q) :
    ∀ (n a b : ℕ), a + b = n → ∀ (s : A) (hs : s ∈ 𝒜 (a + b)),
      IsSumOfCharts 𝒜 hf hg (fracFG 𝒜 hf hg a b s hs) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hab s hs
    rcases a with _ | a
    · have hs' : s ∈ 𝒜 (b • 1) := by simpa using hs
      refine ⟨0, Away.mk 𝒜 hg b s hs', ?_⟩
      rw [map_zero, zero_add, awayMap_mk]
      exact away_mk_eq_away_mk 𝒜 _ _ _ (by simp)
    rcases b with _ | b
    · have hs' : s ∈ 𝒜 ((a + 1) • 1) := by simpa using hs
      refine ⟨Away.mk 𝒜 hf (a + 1) s hs', 0, ?_⟩
      rw [map_zero, add_zero, awayMap_mk]
      exact away_mk_eq_away_mk 𝒜 _ _ _ (by simp)
    · have hs' : s ∈ 𝒜 ((a + b + 1) + 1) := by
        convert hs using 2
        omega
      obtain ⟨p, hp, q, hq, rfl⟩ := hred (a + b + 1) (by omega) s hs'
      have hp' : p ∈ 𝒜 (a + (b + 1)) := by convert hp using 2
      have hq' : q ∈ 𝒜 ((a + 1) + b) := by convert hq using 2; omega
      have key : fracFG 𝒜 hf hg (a + 1) (b + 1) (f * p + g * q) hs =
          fracFG 𝒜 hf hg a (b + 1) p hp' + fracFG 𝒜 hf hg (a + 1) b q hq' := by
        ext
        simp only [fracFG, Away.val_mk, val_add]
        have e : a + (b + 1) = a + 1 + b := by omega
        rw [show (⟨(f * g) ^ (a + (b + 1)), _⟩ : Submonoid.powers (f * g)) =
          ⟨(f * g) ^ (a + 1 + b), ⟨a + 1 + b, rfl⟩⟩ from Subtype.ext (by rw [e]),
          Localization.add_mk_self, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
        exact ⟨1, by simp; ring⟩
      rw [key]
      exact isSumOfCharts_add 𝒜 hf hg (ih _ (by omega) a (b + 1) rfl p hp')
        (ih _ (by omega) (a + 1) b rfl q hq')

/-- **`A_{(fg)} = A_{(f)} + A_{(g)}` for a reduction of reduction number one.** In a graded ring
in which `𝒜ₖ₊₁ = f 𝒜ₖ + g 𝒜ₖ` for every `k ≥ 1`, with `f, g` of degree one, every element of
the degree-zero part of the localization at `fg` is the image of an element of `A_{(f)}` plus
the image of an element of `A_{(g)}`. -/
theorem exists_awayMap_add_awayMap_eq_of_reduction
    (hred : ∀ k, 1 ≤ k → ∀ s ∈ 𝒜 (k + 1), ∃ p ∈ 𝒜 k, ∃ q ∈ 𝒜 k, s = f * p + g * q)
    (z : Away 𝒜 (f * g)) :
    ∃ (z₀ : Away 𝒜 f) (z₁ : Away 𝒜 g),
      z = awayMap 𝒜 hg rfl z₀ + awayMap 𝒜 hf (mul_comm f g) z₁ := by
  obtain ⟨d, s, hs, rfl⟩ := Away.mk_surjective 𝒜 (mul_mem_two 𝒜 hf hg) z
  have hs' : s ∈ 𝒜 (d + d) := by convert hs using 2; simp only [smul_eq_mul]; ring
  have heq : Away.mk 𝒜 (mul_mem_two 𝒜 hf hg) d s hs = fracFG 𝒜 hf hg d d s hs' :=
    away_mk_eq_away_mk 𝒜 _ _ _ (by ring)
  rw [heq]
  exact isSumOfCharts_fracFG 𝒜 hf hg hred _ d d rfl s hs'

end Algebra

section Rees

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- A homogeneous element of degree `k` of the Rees algebra is `monomial k r` with `r ∈ Iᵏ`. -/
theorem exists_eq_reesMonomial {k : ℕ} {s : reesAlgebra I} (hs : s ∈ reesGrading I k) :
    ∃ r : (I ^ k : Ideal R), s = (reesMonomial I k r : reesAlgebra I) :=
  ⟨⟨((s : Polynomial R)).coeff k, s.2 k⟩, Subtype.ext (coe_eq_monomial I hs)⟩

/-- If `I² ≤ (a, b) I`, then `Iᵏ⁺¹ ≤ (a, b) Iᵏ` for every `k ≥ 1`. -/
theorem pow_succ_le_span_mul_pow {a b : R} (hsq : I ^ 2 ≤ Ideal.span {a, b} * I) :
    ∀ k, 1 ≤ k → I ^ (k + 1) ≤ Ideal.span {a, b} * I ^ k := by
  intro k hk
  obtain ⟨k, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  calc I ^ (k + 1 + 1) = I ^ 2 * I ^ k := by rw [← pow_add]; ring_nf
    _ ≤ Ideal.span {a, b} * I * I ^ k := Ideal.mul_mono_left hsq
    _ = Ideal.span {a, b} * I ^ (k + 1) := by rw [mul_assoc, ← pow_succ']

/-- **The reduction condition in the Rees algebra.** If `I² ≤ (a, b) I`, then every
homogeneous element of degree `k + 1 ≥ 2` of the Rees algebra is `a⁽¹⁾ p + b⁽¹⁾ q` with `p, q` of
degree `k`. -/
theorem reesGrading_reduction {a b : R} (ha : a ∈ I) (hb : b ∈ I)
    (hsq : I ^ 2 ≤ Ideal.span {a, b} * I) :
    ∀ k, 1 ≤ k → ∀ s ∈ reesGrading I (k + 1), ∃ p ∈ reesGrading I k, ∃ q ∈ reesGrading I k,
      s = reesDegOne I ha * p + reesDegOne I hb * q := by
  intro k hk s hs
  obtain ⟨⟨r, hr⟩, rfl⟩ := exists_eq_reesMonomial I hs
  have hr' := pow_succ_le_span_mul_pow I hsq k hk hr
  rw [show Ideal.span {a, b} = Ideal.span {a} ⊔ Ideal.span {b} by
    rw [← Ideal.span_union]; rfl, Ideal.sup_mul, Submodule.mem_sup] at hr'
  obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := hr'
  obtain ⟨t₁, ht₁, rfl⟩ := Ideal.mem_span_singleton_mul.1 hr₁
  obtain ⟨t₂, ht₂, rfl⟩ := Ideal.mem_span_singleton_mul.1 hr₂
  refine ⟨reesMonomial I k ⟨t₁, ht₁⟩, (reesMonomial I k ⟨t₁, ht₁⟩).2,
    reesMonomial I k ⟨t₂, ht₂⟩, (reesMonomial I k ⟨t₂, ht₂⟩).2, ?_⟩
  apply Subtype.ext
  simp only [coe_reesMonomial, Subalgebra.coe_add, Subalgebra.coe_mul, coe_reesDegOne,
    Polynomial.monomial_mul_monomial, ← map_add]
  rw [add_comm 1 k]

set_option maxHeartbeats 400000 in
-- long chain of `rw`/`change` steps through sections of `Proj` of the Rees algebra
open Stacks.Cohomology.CechSheaf Stacks.Cohomology.Basis in
/-- **`H¹(Proj(⨁ Iᵏ), 𝒪) = 0` for an ideal with a two-generated reduction of reduction number
one.** If `a, b ∈ I` and `I² ≤ (a, b) I`, then the two charts `D₊(a⁽¹⁾)`, `D₊(b⁽¹⁾)` cover the
blowup — every degree-one element squares into `(a⁽¹⁾, b⁽¹⁾)` — their intersection is affine,
and every function on the intersection is a sum of functions on the two charts
(`Stacks.Blowup.exists_awayMap_add_awayMap_eq_of_reduction`). -/
theorem isZero_Hgroup_one_proj_reesGrading_of_sq_le {a b : R} (ha : a ∈ I) (hb : b ∈ I)
    (hsq : I ^ 2 ≤ Ideal.span {a, b} * I) :
    IsZero (Hgroup (AlgebraicGeometry.Proj (reesGrading I)).ringCatSheaf ⊤ 1
      (SheafOfModules.unit (AlgebraicGeometry.Proj (reesGrading I)).ringCatSheaf)) := by
  let f : reesAlgebra I := reesDegOne I ha
  let g : reesAlgebra I := reesDegOne I hb
  have hf : f ∈ (reesGrading I) 1 := reesDegOne_mem_reesGrading I ha
  have hg : g ∈ (reesGrading I) 1 := reesDegOne_mem_reesGrading I hb
  have hfg : f * g ∈ (reesGrading I) 2 := mul_mem_two (reesGrading I) hf hg
  have hred := reesGrading_reduction I ha hb hsq
  let U₀ : (AlgebraicGeometry.Proj (reesGrading I)).Opens := Proj.basicOpen (reesGrading I) f
  let U₁ : (AlgebraicGeometry.Proj (reesGrading I)).Opens := Proj.basicOpen (reesGrading I) g
  have htop : U₀ ⊔ U₁ = ⊤ := by
    have hgen := adjoin_range_reesDegOne_eq_top I (g := fun x : I => (x : R)) (fun x => x.2)
      (by simp)
    have h := Proj.iSup_basicOpen_eq_top' (reesGrading I)
      (fun x : I => (reesDegOne I x.2 : reesAlgebra I))
      (fun x => ⟨1, reesDegOne_mem_reesGrading I _⟩) hgen
    refine top_le_iff.mp (h.symm.le.trans (iSup_le fun x => ?_))
    -- the square of a degree-one element lies in `(f, g)`
    obtain ⟨p, -, q, -, hpq⟩ := hred 1 le_rfl ((reesDegOne I x.2) ^ 2)
      (by simpa using SetLike.pow_mem_graded 2 (reesDegOne_mem_reesGrading I x.2))
    intro z hz
    rw [← Proj.basicOpen_pow (reesGrading I) _ 2 two_pos, Proj.mem_basicOpen, hpq] at hz
    by_contra hcon
    simp only [Opens.mem_sup, U₀, U₁, Proj.mem_basicOpen, not_or, not_not] at hcon
    exact hz (add_mem (Ideal.mul_mem_right _ _ hcon.1) (Ideal.mul_mem_right _ _ hcon.2))
  have hint : U₀ ⊓ U₁ = Proj.basicOpen (reesGrading I) (f * g) :=
    (Proj.basicOpen_mul (reesGrading I) f g).symm
  have h₀₁ : IsAffineOpen (U₀ ⊓ U₁) := by
    rw [hint]
    exact Proj.isAffineOpen_basicOpen (reesGrading I) (f * g) hfg two_pos
  rw [← htop]
  refine Stacks.Cohomology.TwoCover.isZero_Hgroup_one_of_surjective _
    (Proj.isAffineOpen_basicOpen (reesGrading I) f hf one_pos)
    (Proj.isAffineOpen_basicOpen (reesGrading I) g hg one_pos) h₀₁ fun c => ?_
  let d : Γ(AlgebraicGeometry.Proj (reesGrading I), Proj.basicOpen (reesGrading I) (f * g)) :=
    (AlgebraicGeometry.Proj (reesGrading I)).presheaf.map (homOfLE hint.ge).op (secToΓ c)
  obtain ⟨z₀, z₁, hz⟩ := exists_awayMap_add_awayMap_eq_of_reduction (reesGrading I) hf hg hred
    ((Proj.basicOpenIsoAway (reesGrading I) (f * g) hfg two_pos).inv d)
  refine ⟨Γtosec (-(Proj.awayToSection (reesGrading I) f z₀)),
    Γtosec (Proj.awayToSection (reesGrading I) g z₁), ?_⟩
  apply secToΓ_injective
  rw [secToΓ_sub, secToΓ_res, secToΓ_res, secToΓ_Γtosec, secToΓ_Γtosec]
  have hd : d = Proj.awayToSection (reesGrading I) (f * g)
      ((Proj.basicOpenIsoAway (reesGrading I) (f * g) hfg two_pos).inv d) :=
    (ConcreteCategory.congr_hom
      (Proj.basicOpenIsoAway (reesGrading I) (f * g) hfg two_pos).inv_hom_id d).symm
  have e0 := ConcreteCategory.congr_hom
    (Proj.awayMap_awayToSection (reesGrading I) hg (rfl : f * g = f * g)) z₀
  have e1 := ConcreteCategory.congr_hom
    (Proj.awayMap_awayToSection (reesGrading I) hf (mul_comm f g : f * g = g * f)) z₁
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at e0 e1
  rw [hz, map_add] at hd
  change Proj.awayToSection (reesGrading I) (f * g) (awayMap (reesGrading I) hg rfl z₀) = _ at e0
  change Proj.awayToSection (reesGrading I) (f * g)
    (awayMap (reesGrading I) hf (mul_comm f g) z₁) = _ at e1
  rw [e0, e1] at hd
  have hc : secToΓ c =
      (AlgebraicGeometry.Proj (reesGrading I)).presheaf.map (homOfLE hint.le).op d := by
    change secToΓ c = ((AlgebraicGeometry.Proj (reesGrading I)).presheaf.map (homOfLE hint.ge).op ≫
      (AlgebraicGeometry.Proj (reesGrading I)).presheaf.map (homOfLE hint.le).op) (secToΓ c)
    rw [← Functor.map_comp]
    exact (ConcreteCategory.congr_hom
      ((AlgebraicGeometry.Proj (reesGrading I)).presheaf.map_id _) (secToΓ c)).symm
  rw [hc, hd]
  exact presheaf_map_add_eq_sub_neg _ _ _ _ _ _ _

end Rees

end Stacks.Blowup

namespace Stacks

open Stacks.Blowup

variable {R : Type u} [CommRing R]

/-- **`(x + y, π)` is a reduction of `𝔪 = (π, x, y)` with reduction number one**, in
`R[x, y]/(xy - πⁿ)` for `n ≥ 2`: `x² = (x + y)x - π · πⁿ⁻¹`, `xy = π · πⁿ⁻¹`,
`y² = (x + y)y - π · πⁿ⁻¹`. -/
theorem nodalCenter_sq_le (π : R) {n : ℕ} (hn : 2 ≤ n) :
    nodalCenter R π (π ^ n) ^ 2 ≤
      Ideal.span {nodalGen R (π ^ n) 0 + nodalGen R (π ^ n) 1,
        algebraMap R (nodalChartRing R (π ^ n)) π} * nodalCenter R π (π ^ n) := by
  set p := algebraMap R (nodalChartRing R (π ^ n)) π
  set x := nodalGen R (π ^ n) 0
  set y := nodalGen R (π ^ n) 1
  set I := nodalCenter R π (π ^ n)
  set J := Ideal.span {x + y, p}
  have hpI : p ∈ I := Ideal.subset_span (Set.mem_insert _ _)
  have hxI : x ∈ I := Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hyI : y ∈ I := Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hpJ : p ∈ J := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hwJ : x + y ∈ J := Ideal.subset_span (Set.mem_insert _ _)
  have hpowI : p ^ (n - 1) ∈ I := by
    obtain ⟨m, hm⟩ : ∃ m, n - 1 = m + 1 := ⟨n - 2, by omega⟩
    rw [hm, pow_succ]
    exact Ideal.mul_mem_left _ _ hpI
  have hxy : x * y = p * p ^ (n - 1) := by
    rw [nodalGen_zero_mul_nodalGen_one, map_pow, ← pow_succ']
    congr 1
    omega
  have hc : p * p ^ (n - 1) ∈ J * I := Ideal.mul_mem_mul hpJ hpowI
  rw [pow_two]
  change Ideal.span {p, x, y} * Ideal.span {p, x, y} ≤ J * I
  rw [Ideal.span_mul_span, Ideal.span_le]
  rintro _ ⟨s, hs, t, ht, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
  change s * t ∈ J * I
  rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl
  · exact Ideal.mul_mem_mul hpJ hpI
  · exact Ideal.mul_mem_mul hpJ hxI
  · exact Ideal.mul_mem_mul hpJ hyI
  · rw [mul_comm x p]
    exact Ideal.mul_mem_mul hpJ hxI
  · rw [show x * x = (x + y) * x - p * p ^ (n - 1) by rw [← hxy]; ring]
    exact sub_mem (Ideal.mul_mem_mul hwJ hxI) hc
  · rw [hxy]
    exact hc
  · rw [mul_comm y p]
    exact Ideal.mul_mem_mul hpJ hyI
  · rw [mul_comm y x, hxy]
    exact hc
  · rw [show y * y = (x + y) * y - p * p ^ (n - 1) by rw [← hxy]; ring]
    exact sub_mem (Ideal.mul_mem_mul hwJ hyI) hc

/-- **`H¹(X', 𝒪_{X'}) = 0` for the blowup `X'` of the standard nodal model of exponent `n ≥ 2` in
`𝔪 = (π, x, y)`.** -/
theorem isZero_Hgroup_one_nodalModelBlowup (π : R) {n : ℕ} (hn : 2 ≤ n) :
    IsZero (Hgroup (nodalModelBlowup R π n).ringCatSheaf ⊤ 1
      (SheafOfModules.unit (nodalModelBlowup R π n).ringCatSheaf)) :=
  isZero_Hgroup_one_proj_reesGrading_of_sq_le (nodalCenter R π (π ^ n))
    (a := nodalGen R (π ^ n) 0 + nodalGen R (π ^ n) 1)
    (b := algebraMap R (nodalChartRing R (π ^ n)) π)
    (add_mem (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)))
    (Ideal.subset_span (by simp)) (nodalCenter_sq_le π hn)

/-- **`H¹ = 0` for the blowup of the standard nodal model of exponent `n ≥ 2` in its origin**,
in the form of the blowup of the scheme in the reduced point. -/
theorem isZero_Hgroup_one_blowUp_nodalModelOriginPoint {π : R}
    (hπ : (Ideal.span {π}).IsMaximal) {n : ℕ} (hn : 2 ≤ n) :
    IsZero (Hgroup (AlgebraicGeometry.blowUp (Scheme.IdealSheafData.vanishingIdeal
        (⟨{nodalModelOriginPoint hπ (by omega : 1 ≤ n)},
          isClosed_singleton_nodalModelOriginPoint hπ (by omega : 1 ≤ n)⟩ :
            Closeds (nodalModel R π n)))).ringCatSheaf ⊤ 1
      (SheafOfModules.unit (AlgebraicGeometry.blowUp (Scheme.IdealSheafData.vanishingIdeal
        (⟨{nodalModelOriginPoint hπ (by omega : 1 ≤ n)},
          isClosed_singleton_nodalModelOriginPoint hπ (by omega : 1 ≤ n)⟩ :
            Closeds (nodalModel R π n)))).ringCatSheaf)) := by
  obtain ⟨κ⟩ := nonempty_over_iso_blowUpToBase_nodalModelOriginPoint hπ (by omega : 1 ≤ n)
  let e := (Over.forget _).mapIso κ
  exact (Stacks.Cohomology.SchemeIso.isZero_Hgroup_pullback_iff e _ 1).mp
    ((isZero_Hgroup_one_nodalModelBlowup π hn).of_iso
      ((Hfunctor (nodalModelBlowup R π n).ringCatSheaf ⊤ 1).mapIso
        (Scheme.Modules.pullbackUnitIso e.hom)))

end Stacks

end
