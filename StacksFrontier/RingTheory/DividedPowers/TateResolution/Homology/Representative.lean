module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Basic
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Homology.GradedAlgebra
import all StacksFrontier.RingTheory.DividedPowers.TateResolution.Homology.GradedAlgebra

/-!
# Divided powers of homologous cycles

For a surjective morphism `f : A → B` of divided-power differential graded algebras whose source
has vanishing homology in positive degrees, this file lifts homogeneous elements and boundaries
along `f` and shows that `γₙ` of two homogeneous cycles of the same positive even degree that
differ by a boundary again differ by a boundary. This is the independence of the representative
used to define divided powers on homology.
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w t

private theorem exists_homogeneous_lift {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule R B)
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (f : A →ₐ[R] B)
    (hf_grade : ∀ {n : ℕ} {x : A}, x ∈ 𝒜 n → f x ∈ ℬ n)
    (hf_surjective : Function.Surjective f) {n : ℕ} {x : B}
    (hx : x ∈ ℬ n) : ∃ y : A, y ∈ 𝒜 n ∧ f y = x := by
  classical
  obtain ⟨y, hy⟩ := hf_surjective x
  refine ⟨(DirectSum.decompose 𝒜 y n : 𝒜 n), (DirectSum.decompose 𝒜 y n).property, ?_⟩
  have h := comp_of_graded 𝒜 ℬ f.toLinearMap
    (fun (i : ℕ) (z : A) (hz : z ∈ 𝒜 i) => hf_grade (n := i) hz) y n
  change f.toLinearMap y = x at hy
  rw [hy, DirectSum.decompose_of_mem_same ℬ hx] at h
  exact h.symm

/-- The differential of the degree-`(n + 1)` component of `z` is the degree-`n` component of
`d z`. -/
public theorem differential_decompose_succ {R : Type u} {B : Type w}
    [CommRing R] [Ring B] [Algebra R B]
    (𝒜 : ℕ → Submodule R B) [GradedAlgebra 𝒜]
    (d : B →ₗ[R] B) [IsDifferentialGradedAlgebra 𝒜 d] (z : B) (n : ℕ) :
    d ((DirectSum.decompose 𝒜 z (n + 1) : 𝒜 (n + 1)) : B) =
      (DirectSum.decompose 𝒜 (d z) n : B) := by
  classical
  let S := (DirectSum.decompose 𝒜 z).support
  have hzsum : (∑ j ∈ S, ((DirectSum.decompose 𝒜 z j : 𝒜 j) : B)) = z := by
    simpa [S] using (DirectSum.sum_support_decompose 𝒜 z)
  have hproj : GradedAlgebra.proj 𝒜 n (d z) =
      ∑ j ∈ S, GradedAlgebra.proj 𝒜 n
        (d ((DirectSum.decompose 𝒜 z j : 𝒜 j) : B)) := by
    rw [show d z = d (∑ j ∈ S, ((DirectSum.decompose 𝒜 z j : 𝒜 j) : B)) by
      rw [hzsum]]
    simp only [map_sum]
  have hterm (j : ℕ) : GradedAlgebra.proj 𝒜 n
      (d ((DirectSum.decompose 𝒜 z j : 𝒜 j) : B)) =
        if j = n + 1 then d ((DirectSum.decompose 𝒜 z j : 𝒜 j) : B) else 0 := by
    by_cases hj0 : j = 0
    · subst j
      have hzero := IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒜) (d := d)
        (DirectSum.decompose 𝒜 z 0).property
      simp [GradedAlgebra.proj_apply, hzero]
    · let k := j - 1
      have hj : j = k + 1 := by dsimp [k]; omega
      have hmem := IsDifferentialGradedAlgebra.d_mem (𝒜 := 𝒜) (d := d)
        (n := k) (by rw [← hj]; exact (DirectSum.decompose 𝒜 z j).property)
      rw [GradedAlgebra.proj_apply]
      by_cases hkn : k = n
      · have hmem' : d ((DirectSum.decompose 𝒜 z j : 𝒜 j) : B) ∈ 𝒜 n := by
          simpa [hkn] using hmem
        rw [DirectSum.decompose_of_mem_same 𝒜 hmem']
        have hjn : j = n + 1 := by omega
        simp [hjn]
      · have _hneq : j ≠ n + 1 := by omega
        rw [DirectSum.decompose_of_mem 𝒜 hmem, DirectSum.of_apply]
        simp [hj, hkn]
  have hcollapse : (∑ j ∈ S,
      if j = n + 1 then d ((DirectSum.decompose 𝒜 z j : 𝒜 j) : B) else 0) =
      d ((DirectSum.decompose 𝒜 z (n + 1) : 𝒜 (n + 1)) : B) := by
    by_cases hn : n + 1 ∈ S
    · rw [Finset.sum_eq_single (n + 1)]
      · simp
      · intro j hj hne
        simp [hne]
      · intro hn'
        exact (hn' hn).elim
    · have hzcomponent : DirectSum.decompose 𝒜 z (n + 1) = 0 := by
        simp only [S, DFinsupp.mem_support_iff, not_not] at hn
        exact hn
      simp [hzcomponent, hn]
  have hdegree := IsDifferentialGradedAlgebra.d_mem (𝒜 := 𝒜) (d := d)
    (n := n) (DirectSum.decompose 𝒜 z (n + 1)).property
  calc
    d ((DirectSum.decompose 𝒜 z (n + 1) : 𝒜 (n + 1)) : B) =
        GradedAlgebra.proj 𝒜 n
          (d ((DirectSum.decompose 𝒜 z (n + 1) : 𝒜 (n + 1)) : B)) := by
            rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same 𝒜 hdegree]
    _ = GradedAlgebra.proj 𝒜 n (d z) := by
      rw [hproj]
      simp_rw [hterm]
      rw [hcollapse]
      simp
    _ = (DirectSum.decompose 𝒜 (d z) n : B) := rfl

/-- A homogeneous boundary of degree `n` is the differential of a homogeneous element of degree
`n + 1`. -/
public theorem exists_homogeneous_boundary_preimage {R : Type u} {B : Type w}
    [CommRing R] [Ring B] [Algebra R B]
    (𝒜 : ℕ → Submodule R B) [GradedAlgebra 𝒜]
    (d : B →ₗ[R] B) [IsDifferentialGradedAlgebra 𝒜 d]
    {n : ℕ} {x : B} (hx : x ∈ 𝒜 n)
    (hrange : x ∈ LinearMap.range d) :
    ∃ z : B, z ∈ 𝒜 (n + 1) ∧ d z = x := by
  obtain ⟨z, rfl⟩ := hrange
  refine ⟨(DirectSum.decompose 𝒜 z (n + 1) : 𝒜 (n + 1)),
    (DirectSum.decompose 𝒜 z (n + 1)).property, ?_⟩
  rw [differential_decompose_succ]
  exact DirectSum.decompose_of_mem_same 𝒜 hx

private def isPositiveEvenGrade (i : ℕ) : Prop := ∃ d, i = 2 * (d + 1)

private theorem decompose_eq_zero_of_mem_positiveEven_of_not_grade
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [DirectSum.Decomposition 𝒜]
    {x : A} (hx : x ∈ positiveEvenPart 𝒜) {i : ℕ}
    (hi : ¬ isPositiveEvenGrade i) :
    (DirectSum.decompose 𝒜 x i : A) = 0 := by
  have hle : positiveEvenPart 𝒜 ≤ ⨆ j : ℕ, ⨆ (_ : j ≠ i), 𝒜 j :=
    iSup_le fun d => le_iSup_of_le (2 * (d + 1))
      (le_iSup_of_le (show 2 * (d + 1) ≠ i from fun h => hi ⟨d, h.symm⟩) le_rfl)
  exact decompose_eq_zero_of_mem_iSup_ne 𝒜 i x (hle hx)

private def isEvenGrade (i : ℕ) : Prop := ∃ d, i = 2 * d

private theorem decompose_eq_zero_of_mem_evenPart_of_not_even_grade
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [DirectSum.Decomposition 𝒜]
    {x : A} (hx : x ∈ evenPart 𝒜) {i : ℕ} (hi : ¬ isEvenGrade i) :
    (DirectSum.decompose 𝒜 x i : A) = 0 := by
  have hle : evenPart 𝒜 ≤ ⨆ j : ℕ, ⨆ (_ : j ≠ i), 𝒜 j :=
    iSup_le fun d => le_iSup_of_le (2 * d)
      (le_iSup_of_le (show 2 * d ≠ i from fun h => hi ⟨d, h.symm⟩) le_rfl)
  exact decompose_eq_zero_of_mem_iSup_ne 𝒜 i x (hle hx)

/-- An element of `N` with a preimage under `f` has a preimage in `M` built from the components
of degrees satisfying `P`. -/
private theorem exists_lift_of_grade_pred
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule R B)
    [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition ℬ]
    (f : A →ₗ[R] B)
    (hf_grade : ∀ {n : ℕ} {x : A}, x ∈ 𝒜 n → f x ∈ ℬ n)
    (P : ℕ → Prop) (M : Submodule R A) (N : Submodule R B)
    (hM : ∀ {i : ℕ} {a : A}, a ∈ 𝒜 i → P i → a ∈ M)
    (hN : ∀ {x : B}, x ∈ N → ∀ {i : ℕ}, ¬ P i → (DirectSum.decompose ℬ x i : B) = 0)
    {x : B} (hx : x ∈ N) (hpre : ∃ y, f y = x) :
    ∃ y : A, y ∈ M ∧ f y = x := by
  classical
  obtain ⟨y, rfl⟩ := hpre
  let S := (DirectSum.decompose 𝒜 y).support
  have hsum : (∑ i ∈ S, ((DirectSum.decompose 𝒜 y i : 𝒜 i) : A)) = y := by
    simpa [S] using (DirectSum.sum_support_decompose 𝒜 y)
  let comp (i : ℕ) : A := ((DirectSum.decompose 𝒜 y i : 𝒜 i) : A)
  let chosen (i : ℕ) : A := if P i then comp i else 0
  have hchosen (i : ℕ) : chosen i ∈ M := by
    by_cases hi : P i
    · simpa [chosen, hi] using hM (DirectSum.decompose 𝒜 y i).property hi
    · simp [chosen, hi]
  have hcomp (i : ℕ) : f (comp i) =
      (DirectSum.decompose ℬ (f y) i : B) :=
    (comp_of_graded 𝒜 ℬ f (fun i z hz => hf_grade hz) y i).symm
  refine ⟨∑ i ∈ S, chosen i, Submodule.sum_mem _ fun i _ => hchosen i, ?_⟩
  calc
    f (∑ i ∈ S, chosen i) = ∑ i ∈ S, (DirectSum.decompose ℬ (f y) i : B) := by
      simp only [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : P i
      · simp [chosen, comp, h, hcomp]
      · simp [chosen, h, hN hx h]
    _ = f (∑ i ∈ S, comp i) := by simp only [map_sum, hcomp]
    _ = f y := congrArg f hsum

private theorem exists_positiveEven_lift_of_preimage
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule R B)
    [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition ℬ]
    (f : A →ₗ[R] B)
    (hf_grade : ∀ {n : ℕ} {x : A}, x ∈ 𝒜 n → f x ∈ ℬ n)
    {x : B} (hx : x ∈ positiveEvenPart ℬ) (hpre : ∃ y, f y = x) :
    ∃ y : A, y ∈ positiveEvenPart 𝒜 ∧ f y = x :=
  exists_lift_of_grade_pred 𝒜 ℬ f hf_grade isPositiveEvenGrade _ _
    (fun {i _} ha ⟨d, hd⟩ => mem_positiveEvenPart_of_mem_grade 𝒜 (by omega : 0 < d + 1) (hd ▸ ha))
    (fun hx' _ hi => decompose_eq_zero_of_mem_positiveEven_of_not_grade ℬ hx' hi) hx hpre

private theorem exists_even_lift
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule R B)
    [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition ℬ]
    (f : A →ₗ[R] B)
    (hf_grade : ∀ {n : ℕ} {x : A}, x ∈ 𝒜 n → f x ∈ ℬ n)
    (hf_surjective : Function.Surjective f)
    {x : B} (hx : x ∈ evenPart ℬ) :
    ∃ y : A, y ∈ evenPart 𝒜 ∧ f y = x :=
  exists_lift_of_grade_pred 𝒜 ℬ f hf_grade isEvenGrade _ _
    (fun {_ _} ha ⟨d, hd⟩ => Submodule.mem_iSup_of_mem d (hd ▸ ha))
    (fun hx' _ hi => decompose_eq_zero_of_mem_evenPart_of_not_even_grade ℬ hx' hi) hx
    (hf_surjective x)

private theorem dpow_cycle_of_cycle {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (d : A →ₗ[R] A) [IsDifferentialGradedAlgebra 𝒜 d]
    (γ : DividedPowerStructure 𝒜) [IsCompatibleWithDifferential γ d]
    {x : A} (hx : x ∈ positiveEvenPart 𝒜) (hcycle : d x = 0) (n : ℕ) :
    d (γ.dpow n x) = 0 := by
  cases n with
  | zero =>
      rw [γ.dpow_zero hx]
      exact IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒜) (d := d)
        SetLike.GradedOne.one_mem
  | succ n =>
      rw [IsCompatibleWithDifferential.d_dpow (γ := γ) (d := d)
        (by omega) hx, hcycle, zero_mul]

private theorem dpow_is_boundary_of_positive_cycle {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (d : A →ₗ[R] A) [IsDifferentialGradedAlgebra 𝒜 d]
    (γ : DividedPowerStructure 𝒜) [IsCompatibleWithDifferential γ d]
    (hA : ∀ {n : ℕ}, 0 < n → ∀ {x : A}, x ∈ 𝒜 n → d x = 0 →
      ∃ z : A, z ∈ 𝒜 (n + 1) ∧ d z = x)
    {dgr j : ℕ} {x : A} (hdgr : 0 < dgr) (hj : 0 < j)
    (hx : x ∈ 𝒜 (2 * dgr)) (hpos : x ∈ positiveEvenPart 𝒜)
    (hcycle : d x = 0) :
    ∃ z : A, d z = γ.dpow j x := by
  obtain ⟨z, _, hz⟩ := hA (by positivity) (γ.dpow_mem_grade hj.ne' hpos hx)
    (dpow_cycle_of_cycle 𝒜 d γ hpos hcycle j)
  exact ⟨z, hz⟩

private theorem dpow_homogeneous_eq_mod_boundary
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule R B)
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    [IsStrictlyGradedComm 𝒜] [IsStrictlyGradedComm ℬ]
    (dA : A →ₗ[R] A) (dB : B →ₗ[R] B)
    [IsDifferentialGradedAlgebra 𝒜 dA] [IsDifferentialGradedAlgebra ℬ dB]
    (γA : DividedPowerStructure 𝒜) (γB : DividedPowerStructure ℬ)
    [IsCompatibleWithDifferential γA dA] [IsCompatibleWithDifferential γB dB]
    (f : A →ₐ[R] B)
    (hf_grade : ∀ {n : ℕ} {x : A}, x ∈ 𝒜 n → f x ∈ ℬ n)
    (hf_d : ∀ x : A, f (dA x) = dB (f x))
    (hf_dpow : ∀ {n : ℕ} {x : A}, x ∈ positiveEvenPart 𝒜 →
      f (γA.dpow n x) = γB.dpow n (f x))
    (hf_surjective : Function.Surjective f)
    (hA : ∀ {n : ℕ}, 0 < n → ∀ {x : A}, x ∈ 𝒜 n → dA x = 0 →
      ∃ z : A, z ∈ 𝒜 (n + 1) ∧ dA z = x)
    {dgr n : ℕ} (hdgr : 0 < dgr) (_hn : 0 < n)
    {x y : B} (hx : x ∈ ℬ (2 * dgr)) (hy : y ∈ ℬ (2 * dgr))
    (hxc : dB x = 0) (_hyc : dB y = 0)
    (hxy : ∃ z : B, dB z = y - x) :
    γB.dpow n y - γB.dpow n x ∈ LinearMap.range dB := by
  classical
  obtain ⟨z, hzgrade, hdz⟩ := exists_homogeneous_boundary_preimage ℬ dB
    (Submodule.sub_mem _ hy hx) (LinearMap.mem_range.mpr hxy)
  obtain ⟨u, hugrade, hfu⟩ := exists_homogeneous_lift 𝒜 ℬ f hf_grade
    hf_surjective hx
  obtain ⟨v, hvgrade, hfv⟩ := exists_homogeneous_lift 𝒜 ℬ f hf_grade
    hf_surjective hzgrade
  have hdugrade : dA v ∈ 𝒜 (2 * dgr) := by
    simpa using IsDifferentialGradedAlgebra.d_mem (𝒜 := 𝒜) (d := dA)
      (n := 2 * dgr) (by simpa using hvgrade)
  have hupos := mem_positiveEvenPart_of_mem_grade 𝒜 hdgr hugrade
  have hdvpos := mem_positiveEvenPart_of_mem_grade 𝒜 hdgr hdugrade
  have hxpos := mem_positiveEvenPart_of_mem_grade ℬ hdgr hx
  have hsumgrade : u + dA v ∈ 𝒜 (2 * dgr) := (𝒜 (2 * dgr)).add_mem hugrade hdugrade
  have hsumpos := mem_positiveEvenPart_of_mem_grade 𝒜 hdgr hsumgrade
  have hf_sum : f (u + dA v) = y := by
    rw [map_add, hfu, hf_d, hfv, hdz]
    abel
  have hformulaA := γA.dpow_add (n := n) hupos hdvpos
  have hformula : γB.dpow n y =
      ∑ ij ∈ Finset.antidiagonal n,
        γB.dpow ij.1 x * γB.dpow ij.2 (y - x) := by
    calc
      γB.dpow n y = f (γA.dpow n (u + dA v)) := by
        rw [hf_dpow hsumpos, hf_sum]
      _ = f (∑ ij ∈ Finset.antidiagonal n,
            γA.dpow ij.1 u * γA.dpow ij.2 (dA v)) := congrArg f hformulaA
      _ = _ := by
        simp only [map_sum, map_mul]
        refine Finset.sum_congr rfl ?_
        intro ij hij
        rw [hf_dpow hupos, hfu, hf_dpow hdvpos, hf_d, hfv, hdz]
  have hterm_boundary (ij : ℕ × ℕ) (hij : ij ∈ Finset.antidiagonal n)
      (hijpos : 0 < ij.2) :
      γB.dpow ij.1 x * γB.dpow ij.2 (y - x) ∈ LinearMap.range dB := by
    have hzcycle : dA (dA v) = 0 := IsDifferentialGradedAlgebra.d_sq_zero (𝒜 := 𝒜) (d := dA) v
    have hsource := dpow_is_boundary_of_positive_cycle 𝒜 dA γA hA hdgr hijpos
      hdugrade hdvpos hzcycle
    obtain ⟨w, hw⟩ := hsource
    have hsecond : ∃ wB : B, dB wB = γB.dpow ij.2 (y - x) := by
      refine ⟨f w, ?_⟩
      rw [← hf_d w, hw, hf_dpow hdvpos, hf_d, hfv, hdz]
    have hfirst_cycle : dB (γB.dpow ij.1 x) = 0 :=
      dpow_cycle_of_cycle ℬ dB γB hxpos hxc ij.1
    exact cycle_mul_boundary_exists_preimage ℬ dB hfirst_cycle hsecond
  have hsum_quot :
      Submodule.mkQ (LinearMap.range dB)
        (∑ ij ∈ Finset.antidiagonal n,
          γB.dpow ij.1 x * γB.dpow ij.2 (y - x)) =
      Submodule.mkQ (LinearMap.range dB) (γB.dpow n x) := by
    rw [map_sum, Finset.sum_eq_single (n, 0)]
    · rw [γB.dpow_zero (mem_positiveEvenPart_of_mem_grade ℬ hdgr
        (Submodule.sub_mem _ hy hx)), mul_one]
    · intro ij hij hne
      by_cases hzero : ij.2 = 0
      · rcases ij with ⟨i, j⟩
        simp only at hzero
        subst j
        have hi : i = n := by simpa [Finset.mem_antidiagonal] using hij
        subst i
        exact (hne rfl).elim
      · rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hterm_boundary ij hij (Nat.pos_of_ne_zero hzero)
    · intro hnot
      exact (hnot (by simp [Finset.mem_antidiagonal])).elim
  have hquot :
      Submodule.mkQ (LinearMap.range dB) (γB.dpow n y) =
      Submodule.mkQ (LinearMap.range dB) (γB.dpow n x) := by
    rw [hformula]
    exact hsum_quot
  exact (Submodule.Quotient.eq (LinearMap.range dB)).mp hquot

private theorem product_difference_is_boundary {R : Type u} {B : Type w}
    [CommRing R] [Ring B] [Algebra R B]
    (𝒜 : ℕ → Submodule R B) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (d : B →ₗ[R] B) [IsDifferentialGradedAlgebra 𝒜 d]
    {a a' b b' : B}
    (_ha : d a = 0) (ha' : d a' = 0) (hb : d b = 0) (_hb' : d b' = 0)
    (hab : a - a' ∈ LinearMap.range d) (hbb' : b - b' ∈ LinearMap.range d) :
    a * b - a' * b' ∈ LinearMap.range d := by
  have hleft : a * b - a' * b ∈ LinearMap.range d := by
    rw [← sub_mul]
    exact LinearMap.mem_range.mpr (boundary_mul_cycle_exists_preimage 𝒜 d hab hb)
  have hright : a' * b - a' * b' ∈ LinearMap.range d := by
    rw [← mul_sub]
    exact LinearMap.mem_range.mpr (cycle_mul_boundary_exists_preimage 𝒜 d ha' hbb')
  rw [show a * b - a' * b' = (a * b - a' * b) + (a' * b - a' * b') by abel]
  exact Submodule.add_mem _ hleft hright

private theorem dpow_finset_sum_congr {R : Type u} {B : Type w} {ι : Type t}
    [CommRing R] [Ring B] [Algebra R B]
    (𝒜 : ℕ → Submodule R B) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (d : B →ₗ[R] B) [IsDifferentialGradedAlgebra 𝒜 d]
    (γ : DividedPowerStructure 𝒜) [IsCompatibleWithDifferential γ d]
    (s : Finset ι) (f g : ι → B)
    (hf : ∀ i ∈ s, f i ∈ positiveEvenPart 𝒜)
    (hg : ∀ i ∈ s, g i ∈ positiveEvenPart 𝒜)
    (hfc : ∀ i ∈ s, d (f i) = 0)
    (hgc : ∀ i ∈ s, d (g i) = 0)
    (heq : ∀ i ∈ s, ∀ n, γ.dpow n (f i) - γ.dpow n (g i) ∈ LinearMap.range d) :
    ∀ n, γ.dpow n (∑ i ∈ s, f i) - γ.dpow n (∑ i ∈ s, g i) ∈ LinearMap.range d := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro n
      simp
  | @insert a s has ih =>
      intro n
      have hfs : (∑ i ∈ s, f i) ∈ positiveEvenPart 𝒜 :=
        Submodule.sum_mem _ fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hgs : (∑ i ∈ s, g i) ∈ positiveEvenPart 𝒜 :=
        Submodule.sum_mem _ fun i hi => hg i (Finset.mem_insert_of_mem hi)
      have hfcs : d (∑ i ∈ s, f i) = 0 := by
        rw [map_sum]
        exact Finset.sum_eq_zero fun i hi => hfc i (Finset.mem_insert_of_mem hi)
      have hgcs : d (∑ i ∈ s, g i) = 0 := by
        rw [map_sum]
        exact Finset.sum_eq_zero fun i hi => hgc i (Finset.mem_insert_of_mem hi)
      have hleftpos := hf a (Finset.mem_insert_self a s)
      have hrightpos := hg a (Finset.mem_insert_self a s)
      have hleftcyc := hfc a (Finset.mem_insert_self a s)
      have hrightcyc := hgc a (Finset.mem_insert_self a s)
      rw [Finset.sum_insert has, Finset.sum_insert has, γ.dpow_add hleftpos hfs,
        γ.dpow_add hrightpos hgs, ← Finset.sum_sub_distrib]
      refine Submodule.sum_mem _ fun ij _ => ?_
      have hdiffa : γ.dpow ij.1 (f a) - γ.dpow ij.1 (g a) ∈ LinearMap.range d :=
        heq a (Finset.mem_insert_self a s) ij.1
      have hdiffs : γ.dpow ij.2 (∑ i ∈ s, f i) -
          γ.dpow ij.2 (∑ i ∈ s, g i) ∈ LinearMap.range d :=
        ih
          (fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (fun i hi => hg i (Finset.mem_insert_of_mem hi))
          (fun i hi => hfc i (Finset.mem_insert_of_mem hi))
          (fun i hi => hgc i (Finset.mem_insert_of_mem hi))
          (fun i hi k => heq i (Finset.mem_insert_of_mem hi) k) ij.2
      have hcyca : d (γ.dpow ij.1 (f a)) = 0 :=
        dpow_cycle_of_cycle 𝒜 d γ hleftpos hleftcyc ij.1
      have hcyca' : d (γ.dpow ij.1 (g a)) = 0 :=
        dpow_cycle_of_cycle 𝒜 d γ hrightpos hrightcyc ij.1
      have hcycs : d (γ.dpow ij.2 (∑ i ∈ s, f i)) = 0 :=
        dpow_cycle_of_cycle 𝒜 d γ hfs hfcs ij.2
      have hcycs' : d (γ.dpow ij.2 (∑ i ∈ s, g i)) = 0 :=
        dpow_cycle_of_cycle 𝒜 d γ hgs hgcs ij.2
      exact product_difference_is_boundary 𝒜 d hcyca hcyca' hcycs hcycs' hdiffa hdiffs

private theorem dpow_positiveEven_eq_mod_boundary {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule R B)
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    [IsStrictlyGradedComm 𝒜] [IsStrictlyGradedComm ℬ]
    (dA : A →ₗ[R] A) (dB : B →ₗ[R] B)
    [IsDifferentialGradedAlgebra 𝒜 dA] [IsDifferentialGradedAlgebra ℬ dB]
    (γA : DividedPowerStructure 𝒜) (γB : DividedPowerStructure ℬ)
    [IsCompatibleWithDifferential γA dA] [IsCompatibleWithDifferential γB dB]
    (f : A →ₐ[R] B)
    (hf_grade : ∀ {n : ℕ} {x : A}, x ∈ 𝒜 n → f x ∈ ℬ n)
    (hf_d : ∀ x : A, f (dA x) = dB (f x))
    (hf_dpow : ∀ {n : ℕ} {x : A}, x ∈ positiveEvenPart 𝒜 →
      f (γA.dpow n x) = γB.dpow n (f x))
    (hf_surjective : Function.Surjective f)
    (hA : ∀ {n : ℕ}, 0 < n → ∀ {x : A}, x ∈ 𝒜 n → dA x = 0 →
      ∃ z : A, z ∈ 𝒜 (n + 1) ∧ dA z = x)
    {x y : B} (hx : x ∈ positiveEvenPart ℬ) (hy : y ∈ positiveEvenPart ℬ)
    (hxc : dB x = 0) (hyc : dB y = 0)
    (hxy : ∃ z : B, dB z = y - x) (n : ℕ) :
    γB.dpow n y - γB.dpow n x ∈ LinearMap.range dB := by
  classical
  let s := (DirectSum.decompose ℬ x).support ∪ (DirectSum.decompose ℬ y).support
  let c (z : B) (i : ℕ) : B := if isPositiveEvenGrade i then
    (DirectSum.decompose ℬ z i : ℬ i) else 0
  have hc : ∀ z : B, z ∈ positiveEvenPart ℬ → dB z = 0 →
      (DirectSum.decompose ℬ z).support ⊆ s →
      (∀ i, c z i ∈ positiveEvenPart ℬ) ∧ (∀ i, dB (c z i) = 0) ∧ ∑ i ∈ s, c z i = z := by
    intro z hz hzc hsub
    have hdec (i : ℕ) : c z i = (DirectSum.decompose ℬ z i : B) := by
      by_cases hi : isPositiveEvenGrade i
      · simp [c, hi]
      · simp [c, hi, decompose_eq_zero_of_mem_positiveEven_of_not_grade ℬ hz hi]
    refine ⟨fun i => ?_, fun i => ?_, ?_⟩
    · by_cases hi : isPositiveEvenGrade i
      · obtain ⟨k, rfl⟩ := hi
        rw [hdec]
        exact mem_positiveEvenPart_of_mem_grade ℬ (by omega)
          (DirectSum.decompose ℬ z (2 * (k + 1))).property
      · simp [c, hi]
    · rw [hdec]
      exact differential_of_component_of_cycle ℬ dB hzc i
    · calc
        ∑ i ∈ s, c z i = ∑ i ∈ s, (DirectSum.decompose ℬ z i : B) :=
          Finset.sum_congr rfl fun i _ => hdec i
        _ = ∑ i ∈ (DirectSum.decompose ℬ z).support, (DirectSum.decompose ℬ z i : B) :=
          (Finset.sum_subset hsub fun i _ hi => by simpa using hi).symm
        _ = z := by simpa using DirectSum.sum_support_decompose ℬ z
  obtain ⟨hcxpos, hcxcyc, hsumx⟩ := hc x hx hxc Finset.subset_union_left
  obtain ⟨hcypos, hcycyc, hsumy⟩ := hc y hy hyc Finset.subset_union_right
  have heq (i : ℕ) (hi : i ∈ s) (j : ℕ) :
      γB.dpow j (c x i) - γB.dpow j (c y i) ∈ LinearMap.range dB := by
    by_cases hgrade : isPositiveEvenGrade i
    · obtain ⟨k, rfl⟩ := hgrade
      have hxgrade : (DirectSum.decompose ℬ x (2 * (k + 1)) : B) ∈ ℬ (2 * (k + 1)) :=
        (DirectSum.decompose ℬ x (2 * (k + 1))).property
      have hygrade : (DirectSum.decompose ℬ y (2 * (k + 1)) : B) ∈ ℬ (2 * (k + 1)) :=
        (DirectSum.decompose ℬ y (2 * (k + 1))).property
      have hdiff : (DirectSum.decompose ℬ y (2 * (k + 1)) : B) -
          (DirectSum.decompose ℬ x (2 * (k + 1)) : B) ∈ LinearMap.range dB := by
        obtain ⟨z, hz⟩ := hxy
        have hb := differential_component_is_boundary ℬ dB z (2 * (k + 1))
        rw [hz, DirectSum.decompose_sub] at hb
        simpa only [DirectSum.sub_apply, Submodule.coe_sub] using hb
      have hxy' : ∃ z : B, dB z =
          (DirectSum.decompose ℬ y (2 * (k + 1)) : B) -
            (DirectSum.decompose ℬ x (2 * (k + 1)) : B) :=
        LinearMap.mem_range.mp hdiff
      by_cases hj : j = 0
      · subst j
        have hxpos' : c x (2 * (k + 1)) ∈ positiveEvenPart ℬ := by
          simpa [c, isPositiveEvenGrade] using
            mem_positiveEvenPart_of_mem_grade ℬ (by omega) hxgrade
        have hypos' : c y (2 * (k + 1)) ∈ positiveEvenPart ℬ := by
          simpa [c, isPositiveEvenGrade] using
            mem_positiveEvenPart_of_mem_grade ℬ (by omega) hygrade
        rw [γB.dpow_zero hxpos', γB.dpow_zero hypos']
        simp
      · have hsame := dpow_homogeneous_eq_mod_boundary 𝒜 ℬ dA dB γA γB f
          hf_grade hf_d hf_dpow hf_surjective hA (dgr := k + 1) (n := j)
          (by omega) (Nat.pos_of_ne_zero hj) hxgrade hygrade
          (differential_of_component_of_cycle ℬ dB hxc _)
          (differential_of_component_of_cycle ℬ dB hyc _) hxy'
        have hsame' := Submodule.neg_mem (LinearMap.range dB) hsame
        simpa [c, isPositiveEvenGrade] using hsame'
    · simp [c, hgrade]
  have hcongr := dpow_finset_sum_congr ℬ dB γB s (c x) (c y)
    (fun i hi => hcxpos i) (fun i hi => hcypos i)
    (fun i hi => hcxcyc i) (fun i hi => hcycyc i)
    (fun i hi j => heq i hi j) n
  have hneg := Submodule.neg_mem (LinearMap.range dB) hcongr
  simpa [hsumx, hsumy] using hneg

end DividedPowers.TateResolution
