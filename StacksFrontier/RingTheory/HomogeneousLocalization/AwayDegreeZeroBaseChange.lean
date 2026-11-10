module

public import StacksFrontier.RingTheory.HomogeneousLocalization.GradedLocalizedModule
public import StacksFrontier.RingTheory.GradedAlgebra.Proj.LaurentAway
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DegreeZeroLocalizationArbitraryDegree
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Localization at an element of degree one as a base change of the degree-zero part

Let `S = ⨁_{d ≥ 0} S_d` be a graded ring, `M = ⨁_{n ∈ ℤ} M_n` a graded `S`-module and `f ∈ S_1`.
Write `S₍f₎` for the degree-zero part of `S_f` and `M₍f₎` for the degree-zero part of `M_f`. Then

`S_f ⊗_{S₍f₎} M₍f₎ ⟶ M_f`, `a ⊗ m ↦ a · m`

is an isomorphism: `M_f` is the base change of `M₍f₎` along `S₍f₎ ⟶ S_f`. Both sides are graded by
the integer powers of `f`, which is a unit of degree one: every element of `S_f` is a combination
of the powers `fⁿ` with coefficients in `S₍f₎`, and the degree-`n` part of `M_f` is `fⁿ · M₍f₎`.
This is the algebraic form of the statement that the punctured cone over the standard open
`D₊(f)` is `D₊(f) × 𝔾ₘ`.

## Main results

* `Stacks.GradedLocalization.mem_gradedModuleDegreeZeroLocalization_iff`: the two spellings of the
  degree-zero part of `M_f` agree.
* `Stacks.GradedLocalization.zpow_smul_mem_gradedPiece`: multiplication by `fᵏ` shifts degrees by
  `k`.
* `Stacks.GradedLocalization.isBaseChange_degreeZero`: the base change statement above.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
-/

@[expose] public noncomputable section

open DirectSum TensorProduct Stacks.GradedLaurent

attribute [local instance] instVAddNatIntGradedLocalizedModule

namespace Stacks.GradedLocalization

variable {S : Type*} {M : Type*} {σ : Type*} {τ : Type*}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒜 𝒨]

/-- For `f` homogeneous, an element of `M_f` lies in the degree-zero localization
`GradedModuleDegreeZeroLocalization 𝒜 𝒨 f` if and only if it lies in the degree-zero graded piece
`gradedPiece 𝒜 𝒨 f 0`. -/
theorem mem_gradedModuleDegreeZeroLocalization_iff {f : S} {d : ℕ} (hf : f ∈ 𝒜 d)
    (z : LocalizedModule.Away (R := S) f M) :
    letI := Module.compHom (R := Localization.Away f) (LocalizedModule.Away (R := S) f M)
      (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))
    z ∈ GradedModuleDegreeZeroLocalization 𝒜 𝒨 f ↔ z ∈ gradedPiece 𝒜 𝒨 f 0 := by
  let := Module.compHom (R := Localization.Away f) (LocalizedModule.Away (R := S) f M)
    (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))
  constructor
  · intro hz
    obtain ⟨n, x, hx, hzx⟩ :=
      Stacks.SheafOfModules.degreeZeroLocalization_exists_fraction_of_degree 𝒜 𝒨 hf ⟨z, hz⟩
    change z = _ at hzx
    rw [hzx]
    refine mk_mem_gradedPiece 𝒜 𝒨 hf ?_
    convert hx using 2
    simp [mul_comm]
  · intro hz
    obtain ⟨n, x, hx, rfl⟩ := (mem_gradedPiece_iff 𝒜 𝒨 hf 0 z).1 hz
    refine Submodule.subset_span ⟨d, n, hf, x, ?_, rfl⟩
    simpa using hx

omit [DirectSum.Decomposition 𝒨] in
/-- **Multiplication by an integer power of an element `f` of degree one shifts the degree.** -/
theorem zpow_smul_mem_gradedPiece {f : S} (hf : f ∈ 𝒜 1) (k e : ℤ)
    {z : LocalizedModule.Away (R := S) f M} (hz : z ∈ gradedPiece 𝒜 𝒨 f e) :
    ((awayUnit f ^ k : (Localization.Away f)ˣ) : Localization.Away f) • z ∈
      gradedPiece 𝒜 𝒨 f (e + k) := by
  obtain ⟨n, x, hx, rfl⟩ := (mem_gradedPiece_iff 𝒜 𝒨 hf e z).1 hz
  obtain ⟨b, hb⟩ : ∃ b : ℕ, 0 ≤ k + b := ⟨k.natAbs, by omega⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (a : ℤ) = k + b := ⟨(k + b).toNat, Int.toNat_of_nonneg hb⟩
  rw [coe_awayUnit_zpow_eq_mk f ha, LocalizedModule.mk_smul_mk]
  have hmem : f ^ a • x ∈ 𝒨 (e + k + (b + n : ℕ) • ((1 : ℕ) : ℤ)) := by
    have h := SetLike.GradedSMul.smul_mem (A := 𝒜) (B := 𝒨) (SetLike.pow_mem_graded a hf) hx
    convert h using 2
    change e + k + (b + n : ℕ) • ((1 : ℕ) : ℤ) = ((a • 1 : ℕ) : ℤ) + (e + n • ((1 : ℕ) : ℤ))
    simp only [nsmul_eq_mul, Nat.cast_one, mul_one, Nat.cast_add, smul_eq_mul]
    omega
  convert mk_mem_gradedPiece 𝒜 𝒨 hf hmem using 2
  exact Subtype.ext (by simp [pow_add])

/-- **Every element of `S_f` is a combination of the integer powers of `f` with coefficients in
`S₍f₎`**, for `f` of degree one. -/
theorem exists_sum_zpow_eq {f : S} (hf : f ∈ 𝒜 1) (z : Localization.Away f) :
    ∃ (s : Finset ℤ) (c : ℤ → HomogeneousLocalization.Away 𝒜 f),
      z = ∑ n ∈ s,
        (c n).val * ((awayUnit f ^ n : (Localization.Away f)ˣ) : Localization.Away f) := by
  classical
  induction z using Localization.induction_on with
  | H y =>
  obtain ⟨x, ⟨_, k, rfl⟩⟩ := y
  refine ⟨((DirectSum.decompose 𝒜 x).support).image (fun d : ℕ => (d : ℤ) - k),
    fun n => if h : 0 ≤ n + k then HomogeneousLocalization.Away.mk 𝒜 hf (n + k).toNat
      ((DirectSum.decompose 𝒜 x ((n + k).toNat) : S))
      (by rw [smul_eq_mul, mul_one]; exact (DirectSum.decompose 𝒜 x _).2) else 0, ?_⟩
  rw [Finset.sum_image (fun d₁ _ d₂ _ h => by simpa using h)]
  dsimp only
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 x]
  rw [Localization.mk_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have h0 : 0 ≤ ((d : ℤ) - k) + k := by omega
  dsimp only
  rw [dite_eq_left h0, HomogeneousLocalization.Away.val_mk]
  have hd : (((d : ℤ) - k) + k).toNat = d := by omega
  rw [coe_awayUnit_zpow_eq_mk f (k := (d : ℤ) - k) (a := d) (b := k) (by ring),
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  rw [hd]
  ring

variable {f : S}

/-- The `S₍f₎`-module structure on `M_f`, restricted from its `S_f`-module structure. -/
abbrev awayModule (f : S) : Module (HomogeneousLocalization.Away 𝒜 f)
    (LocalizedModule.Away (R := S) f M) :=
  Module.compHom (R := Localization.Away f) (LocalizedModule.Away (R := S) f M)
    (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))

attribute [local instance] awayModule

/-- The actions of `S₍f₎` and `S_f` on `M_f` form a scalar tower over `S₍f₎ ⟶ S_f`. -/
instance awayScalarTower (f : S) : IsScalarTower (HomogeneousLocalization.Away 𝒜 f)
    (Localization.Away f) (LocalizedModule.Away (R := S) f M) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- **`M_f` is the base change of its degree-zero part `M₍f₎` along `S₍f₎ ⟶ S_f`**, for `f` of
degree one. -/
theorem isBaseChange_degreeZero (hf : f ∈ 𝒜 1) :
    IsBaseChange (Localization.Away f) (GradedModuleDegreeZeroLocalization 𝒜 𝒨 f).subtype := by
  classical
  set B := HomogeneousLocalization.Away 𝒜 f
  set Af := Localization.Away f
  set Mf := LocalizedModule.Away (R := S) f M
  set M0 := GradedModuleDegreeZeroLocalization 𝒜 𝒨 f
  let b : ℤ → Af := fun n => ((awayUnit f ^ n : Afˣ) : Af)
  have hbb : ∀ (n m : ℤ) (x : Mf), n + m = 0 → b n • b m • x = x := fun n m x h => by
    simp only [b, smul_smul, ← Units.val_mul, ← zpow_add, h, zpow_zero, Units.val_one, one_smul]
  have hM0 : ∀ z : Mf, z ∈ M0 ↔ z ∈ gradedPiece 𝒜 𝒨 f 0 :=
    mem_gradedModuleDegreeZeroLocalization_iff 𝒜 𝒨 hf
  let Φ : (ℤ →₀ M0) →+ Mf := Finsupp.liftAddHom fun n =>
    { toFun := fun m => b n • (m : Mf), map_zero' := by simp, map_add' := by simp [smul_add] }
  let θ : (ℤ →₀ M0) →+ Af ⊗[B] M0 := Finsupp.liftAddHom fun n =>
    (TensorProduct.mk B Af M0 (b n)).toAddMonoidHom
  let Λ := M0.subtype.liftBaseChange Af
  have hΛθ : ∀ g, Λ (θ g) = Φ g := by
    intro g
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g₁ g₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
    | single n m =>
      simp only [θ, Φ, Finsupp.liftAddHom_apply_single, LinearMap.toAddMonoidHom_coe,
        TensorProduct.mk_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Λ]
      rfl
  have hθ : Function.Surjective θ := by
    intro t
    induction t using TensorProduct.inductionOn with
    | add t₁ t₂ h₁ h₂ =>
      obtain ⟨g₁, rfl⟩ := h₁
      obtain ⟨g₂, rfl⟩ := h₂
      exact ⟨g₁ + g₂, map_add _ _ _⟩
    | tmul a m =>
      obtain ⟨s, c, rfl⟩ := exists_sum_zpow_eq 𝒜 hf a
      refine ⟨∑ n ∈ s, Finsupp.single n (c n • m), ?_⟩
      rw [map_sum, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [θ, Finsupp.liftAddHom_apply_single, LinearMap.toAddMonoidHom_coe,
        TensorProduct.mk_apply]
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]
      rfl
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro g hg
    have hint := isInternal_gradedPiece 𝒜 𝒨 hf (M := M)
    have hmem : ∀ n, b n • ((g n : M0) : Mf) ∈ gradedPiece 𝒜 𝒨 f n := fun n => by
      have h := zpow_smul_mem_gradedPiece 𝒜 𝒨 hf n 0 ((hM0 _).1 (g n).2)
      rwa [zero_add] at h
    let ξ : DirectSum ℤ fun e => ↥(gradedPiece 𝒜 𝒨 f e) :=
      ∑ n ∈ g.support, DirectSum.of (fun e => ↥(gradedPiece 𝒜 𝒨 f e)) n ⟨_, hmem n⟩
    have hξ : DirectSum.coeAddMonoidHom (gradedPiece 𝒜 𝒨 f) ξ = 0 := by
      rw [map_sum]
      refine ((Finset.sum_congr rfl fun n _ => DirectSum.coeAddMonoidHom_of _ n _)).trans ?_
      rw [← hg]
      simp only [Φ, Finsupp.liftAddHom_apply, Finsupp.sum]
      rfl
    have hξ0 : ξ = 0 := hint.1 (hξ.trans (map_zero _).symm)
    ext n
    have hcomp := congrArg (fun ζ : DirectSum ℤ fun e => ↥(gradedPiece 𝒜 𝒨 f e) =>
      ((ζ n : LocalizedModule.Away (R := S) f M))) hξ0
    simp only [ξ, DirectSum.zero_apply, ZeroMemClass.coe_zero] at hcomp
    rw [DFinsupp.finsetSum_apply, AddSubgroup.val_finsetSum] at hcomp
    by_cases hn : n ∈ g.support
    · rw [Finset.sum_eq_single_of_mem n hn (fun m _ hmn => by
        rw [DirectSum.of_eq_of_ne m n _ (Ne.symm hmn)]; rfl)] at hcomp
      rw [DirectSum.of_eq_same] at hcomp
      refine (hbb (-n) n _ (neg_add_cancel n)).symm.trans ?_
      simp only at hcomp
      rw [hcomp, smul_zero]
      rfl
    · simpa using hn
  have hΦs : Function.Surjective Φ := by
    intro y
    obtain ⟨ξ, rfl⟩ := (isInternal_gradedPiece 𝒜 𝒨 hf (M := M)).2 y
    have hmem : ∀ e, b (-e) • ((ξ e : LocalizedModule.Away (R := S) f M)) ∈ M0 := fun e => by
      rw [hM0]
      have h := zpow_smul_mem_gradedPiece 𝒜 𝒨 hf (-e) e (ξ e).2
      rwa [add_neg_cancel] at h
    refine ⟨∑ e ∈ DFinsupp.support ξ, Finsupp.single e ⟨_, hmem e⟩, ?_⟩
    rw [map_sum]
    conv_rhs => rw [← DirectSum.sum_support_of ξ, map_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [Φ, Finsupp.liftAddHom_apply_single, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      DirectSum.coeAddMonoidHom_of]
    change b e • b (-e) • _ = _
    exact hbb e (-e) _ (add_neg_cancel e)
  have hΛ : Function.Bijective Λ := by
    refine ⟨?_, ?_⟩
    · rw [injective_iff_map_eq_zero]
      intro t ht
      obtain ⟨g, rfl⟩ := hθ t
      rw [hΛθ] at ht
      rw [hΦ (ht.trans (map_zero _).symm), map_zero]
    · intro y
      obtain ⟨g, rfl⟩ := hΦs y
      exact ⟨θ g, hΛθ g⟩
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective Λ hΛ) fun x => ?_
  simp [Λ, LinearMap.liftBaseChange_tmul]

end Stacks.GradedLocalization

end
