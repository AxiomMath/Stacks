module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.ULift
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.Logic.Small.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Jacobson.Ring
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Tor.ProZero
public import StacksFrontier.RingTheory.AdicCompletion.KerEval
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Coherent.Flat
public import StacksFrontier.RingTheory.Flat.TorCriterion
public import StacksFrontier.RingTheory.Flat.UniversallyInjective
public import StacksFrontier.RingTheory.Tor.Balancing
public import StacksFrontier.RingTheory.Ideal.SmulTop
public import StacksFrontier.CategoryTheory.MittagLefflerSections
public import StacksFrontier.RingTheory.UniversallyExact
public import StacksFrontier.RingTheory.Flat.FibreCriterionNilpotent

/-!
# The map `(⊕_{α ∈ A} R)^∧ → ∏_{α ∈ A} R`

For `R` Noetherian and `I`-adically complete, this file proves that the canonical map
`AdicCompletion.directSumToPi : (⊕_{α ∈ A} R)^∧ → ∏_{α ∈ A} R` out of the completion of a direct
sum of copies of `R` into the product is universally injective.

## Main definitions

* `AdicCompletion.directSumToPi`

## Main results

* `AdicCompletion.universallyInjective_directSumToPi`
-/

@[expose] public section

universe u v

section DirectSumToPi

open scoped DirectSum TensorProduct

/-- The `I`-adic completion `(⊕_{α ∈ A} R)^∧` of a direct sum of copies of `R`. -/
abbrev completedDirectSum (R : Type u) [CommRing R] (I : Ideal R) (A : Type v) :=
  AdicCompletion I (⨁ _ : A, R)

/-- The canonical map from the `I`-adic completion of a direct sum `⊕_{α ∈ A} R` of copies of an
`I`-adically complete ring `R` to the product `∏_{α ∈ A} R`. It is given coordinatewise: the
`α`-th component is the map induced on `I`-adic completions by `DirectSum.component`, followed by
the inverse of the canonical isomorphism `R ≃ₗ[R] R^∧`. -/
noncomputable def AdicCompletion.directSumToPi (R : Type u) [CommRing R]
    (I : Ideal R) (A : Type v) [IsAdicComplete I R] :
    AdicCompletion I (⨁ _ : A, R) →ₗ[R] (A → R) :=
  LinearMap.pi fun a =>
    (AdicCompletion.ofLinearEquiv I R).symm.toLinearMap.comp
      ((AdicCompletion.map I (DirectSum.component R A (fun _ : A => R) a)).restrictScalars R)

/-- Modulo `Iⁿ`, the `a`-th coordinate of `AdicCompletion.directSumToPi R I A x` is the image of
the `n`-th level of `x` under the `a`-th component map. -/
theorem coordinate_eval {R : Type u} [CommRing R] (I : Ideal R) (A : Type v)
    [IsAdicComplete I R] (x : completedDirectSum R I A) (a : A) (n : ℕ) :
    Submodule.mkQ (I ^ n • (⊤ : Submodule R R))
        (AdicCompletion.directSumToPi R I A x a) =
      (DirectSum.component R A (fun _ : A => R) a).reduceModIdeal (I ^ n) (x.val n) := by
  let c := DirectSum.component R A (fun _ : A => R) a
  rw [← AdicCompletion.eval_of I R n (AdicCompletion.directSumToPi R I A x a)]
  show AdicCompletion.eval I R n
      (AdicCompletion.of I R ((AdicCompletion.ofLinearEquiv I R).symm
        (AdicCompletion.map I c x))) =
    c.reduceModIdeal (I ^ n) (x.val n)
  rw [AdicCompletion.of_ofLinearEquiv_symm, AdicCompletion.eval_apply,
    AdicCompletion.map_val_apply]

/-- Membership in `Iⁿ • ⊤ ⊆ R` is membership in `Iⁿ`. -/
private lemma mem_pow_smul_top_iff {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) (x : R) :
    x ∈ I ^ n • (⊤ : Submodule R R) ↔ x ∈ I ^ n := by
  simp [smul_eq_mul]

/-- A linear form maps `J • ⊤` into `J`. -/
private lemma apply_mem_of_mem_smul_top {R : Type u} [CommRing R] (J : Ideal R)
    {M : Type*} [AddCommGroup M] [Module R M] (f : M →ₗ[R] R) {x : M}
    (hx : x ∈ J • (⊤ : Submodule R M)) : f x ∈ J := by
  refine Submodule.smul_induction_on hx (fun r hr z _ => ?_) fun _ _ hx hy => ?_
  · rw [map_smul]
    exact J.mul_mem_right _ hr
  · rw [map_add]
    exact J.add_mem hx hy

/-- The `a`-th component of the class of `t` modulo `Iⁿ` vanishes iff `t a ∈ Iⁿ`. -/
private lemma reduceModIdeal_component_mk_eq_zero_iff {R : Type u} [CommRing R] (I : Ideal R)
    (A : Type v) (n : ℕ) (t : ⨁ _ : A, R) (a : A) :
    (DirectSum.component R A (fun _ : A => R) a).reduceModIdeal (I ^ n)
        (Submodule.Quotient.mk (p := I ^ n • (⊤ : Submodule R (⨁ _ : A, R))) t) = 0 ↔
      t a ∈ I ^ n := by
  rw [LinearMap.reduceModIdeal_apply, Submodule.Quotient.mk_eq_zero, mem_pow_smul_top_iff]
  rfl

private lemma directSum_mem_pow_smul_top {R : Type u} [CommRing R] (I : Ideal R)
    (A : Type v) (x : ⨁ _ : A, R) (n : ℕ)
    (hx : ∀ a, x a ∈ I ^ n) : x ∈ I ^ n • (⊤ : Submodule R (⨁ _ : A, R)) := by
  classical
  rw [← DirectSum.sum_support_of x]
  apply Submodule.sum_mem
  intro a ha
  rw [← DirectSum.lof_eq_of R]
  have hterm : x a • DirectSum.lof R A (fun _ : A => R) a (1 : R) ∈
      I ^ n • (⊤ : Submodule R (⨁ _ : A, R)) :=
    Submodule.smul_mem_smul (hx a) Submodule.mem_top
  convert hterm using 1
  rw [show (x a : R) = (x a) • (1 : R) by simp, map_smul]
  simp

/-- If the `a`-th component of the `n`-th level of `x` vanishes, then the `a`-th coordinate of
`AdicCompletion.directSumToPi R I A x` lies in `Iⁿ`. -/
theorem coordinate_mem_pow_of_level_zero {R : Type u} [CommRing R]
    (I : Ideal R) (A : Type v) [IsAdicComplete I R]
    (x : completedDirectSum R I A) (n : ℕ) {a : A}
    (hx : (DirectSum.component R A (fun _ : A => R) a).reduceModIdeal (I ^ n)
      (x.val n) = 0) : AdicCompletion.directSumToPi R I A x a ∈ I ^ n := by
  have hq := coordinate_eval I A x a n
  rw [hx] at hq
  exact (mem_pow_smul_top_iff I n _).mp ((Submodule.Quotient.mk_eq_zero _).mp hq)

/-- For every `n`, only finitely many coordinates of `AdicCompletion.directSumToPi R I A x` lie
outside `Iⁿ`. -/
theorem coordinate_support_finite {R : Type u} [CommRing R]
    (I : Ideal R) (A : Type v) [IsAdicComplete I R]
    (x : completedDirectSum R I A) (n : ℕ) :
    {a : A | AdicCompletion.directSumToPi R I A x a ∉ I ^ n}.Finite := by
  classical
  obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective
    (I ^ n • (⊤ : Submodule R (⨁ _ : A, R))) (x.val n)
  refine t.support.finite_toSet.subset fun a ha => ?_
  by_contra hnot
  refine ha (coordinate_mem_pow_of_level_zero I A x n ?_)
  rw [← ht, reduceModIdeal_component_mk_eq_zero_iff]
  simp [show t a = 0 by simpa using hnot]

private theorem AdicCompletion.directSumToPi_injective {R : Type u} [CommRing R]
    (I : Ideal R) (A : Type v) [IsAdicComplete I R]
    (x : completedDirectSum R I A)
    (hx : AdicCompletion.directSumToPi R I A x = 0) : x = 0 := by
  refine AdicCompletion.ext fun n => ?_
  show x.val n = 0
  obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective
    (I ^ n • (⊤ : Submodule R (⨁ _ : A, R))) (x.val n)
  rw [← ht]
  apply (Submodule.Quotient.mk_eq_zero _).2
  apply directSum_mem_pow_smul_top I A t n
  intro a
  have hq := coordinate_eval I A x a n
  rw [congrFun hx a, ← ht] at hq
  exact (reduceModIdeal_component_mk_eq_zero_iff I A n t a).mp (by simpa using hq.symm)

private theorem product_module_flat {R : Type u} [CommRing R] [IsNoetherianRing R]
    (A : Type v) : Module.Flat R (A → R) := by
  classical
  let R' := ULift.{max u v} R
  let A' := Shrink.{max u v} A
  let eRing : ULift.{max u v} R ≃+* R := ULift.ringEquiv
  have : IsNoetherianRing R' :=
    isNoetherianRing_of_surjective R R' eRing.symm.toRingHom eRing.symm.surjective
  have hflat : Module.Flat R' (A' → R') := by
    have hPi := ((IsCoherentRing.tfae_flat_pi R').out 1 3).mp
      (isCoherentRing_of_isNoetherianRing R')
    exact hPi A'
  let eR : R' ≃ₗ[R'] R :=
    { toFun := ULift.down
      invFun := ULift.up
      left_inv := by intro x; cases x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro r x; rfl }
  let eA : A' ≃ A := (equivShrink A).symm
  let e : (A' → R') ≃ₗ[R'] (A → R) :=
    (LinearEquiv.piCongrRight fun _ => eR).trans
      (LinearEquiv.funCongrLeft R' R eA.symm)
  have hflat' : Module.Flat R' (A → R) := Module.Flat.of_linearEquiv e.symm
  exact (Module.Flat.ulift_left_iff (R := R) (M := A → R)).mp hflat'

private noncomputable def decayTruncation {R : Type u} [CommRing R] (I : Ideal R)
    (A : Type v) (z : A → R)
    (hdecay : ∀ n, {a : A | z a ∉ I ^ n}.Finite) (n : ℕ) : ⨁ _ : A, R := by
  classical
  exact ∑ a ∈ (hdecay n).toFinset, z a • DirectSum.lof R A (fun _ : A => R) a 1

private theorem decayTruncation_component {R : Type u} [CommRing R] (I : Ideal R)
    (A : Type v) [DecidableEq A] (z : A → R) (hdecay : ∀ n, {a : A | z a ∉ I ^ n}.Finite)
    (n : ℕ) (a : A) :
    DirectSum.component R A (fun _ : A => R) a (decayTruncation I A z hdecay n) =
      if a ∈ (hdecay n).toFinset then z a else 0 := by
  classical
  by_cases ha : a ∈ (hdecay n).toFinset <;> simp [decayTruncation, DirectSum.component.of, ha]

private theorem decayTruncation_cauchy {R : Type u} [CommRing R] (I : Ideal R)
    (A : Type v) (z : A → R) (hdecay : ∀ n, {a : A | z a ∉ I ^ n}.Finite)
    {n m : ℕ} (hnm : n ≤ m) :
    Submodule.Quotient.mk (p := I ^ n • (⊤ : Submodule R (⨁ _ : A, R)))
        (decayTruncation I A z hdecay m) =
      Submodule.Quotient.mk (p := I ^ n • (⊤ : Submodule R (⨁ _ : A, R)))
        (decayTruncation I A z hdecay n) := by
  classical
  rw [Submodule.Quotient.eq]
  apply directSum_mem_pow_smul_top I A _ n
  intro a
  have hm := decayTruncation_component I A z hdecay m a
  have hn := decayTruncation_component I A z hdecay n a
  have hm' : (decayTruncation I A z hdecay m) a =
      if a ∈ (hdecay m).toFinset then z a else 0 := by
    simpa [DirectSum.component, DFinsupp.lapply] using hm
  have hn' : (decayTruncation I A z hdecay n) a =
      if a ∈ (hdecay n).toFinset then z a else 0 := by
    simpa [DirectSum.component, DFinsupp.lapply] using hn
  have hsub : (decayTruncation I A z hdecay m - decayTruncation I A z hdecay n) a =
      (decayTruncation I A z hdecay m) a - (decayTruncation I A z hdecay n) a := by
    simp
  rw [hsub, hm', hn']
  by_cases ha : a ∈ (hdecay n).toFinset
  · have ham : a ∈ (hdecay m).toFinset := (hdecay m).mem_toFinset.mpr fun hm =>
      (hdecay n).mem_toFinset.mp ha (Ideal.pow_le_pow_right hnm hm)
    simp [ha, ham]
  · have haz : z a ∈ I ^ n := not_not.mp fun hnot => ha ((hdecay n).mem_toFinset.mpr hnot)
    by_cases ham : a ∈ (hdecay m).toFinset <;> simp [ha, ham, haz]

private noncomputable def decayQuotientMap {R : Type u} [CommRing R] (I : Ideal R)
    (A : Type v) (z : A → R) (hdecay : ∀ n, {a : A | z a ∉ I ^ n}.Finite)
    (n : ℕ) : R →ₗ[R] (⨁ _ : A, R) ⧸ (I ^ n • (⊤ : Submodule R (⨁ _ : A, R))) where
  toFun r := Submodule.Quotient.mk (r • decayTruncation I A z hdecay n)
  map_add' r s := by
    change Submodule.Quotient.mk ((r + s) • decayTruncation I A z hdecay n) = _
    rw [add_smul, Submodule.Quotient.mk_add]
  map_smul' r s := by
    change Submodule.Quotient.mk ((r * s) • decayTruncation I A z hdecay n) =
      r • Submodule.Quotient.mk (s • decayTruncation I A z hdecay n)
    rw [mul_smul, Submodule.Quotient.mk_smul]

private theorem decayQuotientMap_compatible {R : Type u} [CommRing R] (I : Ideal R)
    (A : Type v) (z : A → R) (hdecay : ∀ n, {a : A | z a ∉ I ^ n}.Finite)
    {n m : ℕ} (hnm : n ≤ m) :
    Submodule.factorPow I (⨁ _ : A, R) hnm ∘ₗ decayQuotientMap I A z hdecay m =
      decayQuotientMap I A z hdecay n := by
  refine LinearMap.ext fun r => ?_
  show Submodule.factorPow I (⨁ _ : A, R) hnm
      (Submodule.Quotient.mk (r • decayTruncation I A z hdecay m)) =
    Submodule.Quotient.mk (r • decayTruncation I A z hdecay n)
  have hsub : (I ^ m • (⊤ : Submodule R (⨁ _ : A, R))) ≤
      I ^ n • (⊤ : Submodule R (⨁ _ : A, R)) :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right hnm)
  show Submodule.factor hsub
      ((I ^ m • (⊤ : Submodule R (⨁ _ : A, R))).mkQ
        (r • decayTruncation I A z hdecay m)) =
    (I ^ n • (⊤ : Submodule R (⨁ _ : A, R))).mkQ
      (r • decayTruncation I A z hdecay n)
  rw [Submodule.factor_mk, map_smul, map_smul]
  exact congrArg (fun x : (⨁ _ : A, R) ⧸ (I ^ n • ⊤) => r • x)
    (decayTruncation_cauchy I A z hdecay hnm)

private noncomputable def decayAssemble {R : Type u} [CommRing R] (I : Ideal R)
    (A : Type v) [IsAdicComplete I R]
    (z : A → R) (hdecay : ∀ n, {a : A | z a ∉ I ^ n}.Finite) : completedDirectSum R I A :=
  AdicCompletion.lift I (decayQuotientMap I A z hdecay)
    (fun hnm => decayQuotientMap_compatible I A z hdecay hnm) 1

private theorem decayAssemble_apply {R : Type u} [CommRing R] (I : Ideal R)
    (A : Type v) [IsAdicComplete I R]
    (z : A → R) (hdecay : ∀ n, {a : A | z a ∉ I ^ n}.Finite) (a : A) :
    AdicCompletion.directSumToPi R I A (decayAssemble I A z hdecay) a = z a := by
  classical
  refine (AdicCompletion.ofLinearEquiv I R).injective (AdicCompletion.ext fun n => ?_)
  show Submodule.mkQ (I ^ n • (⊤ : Submodule R R))
      (AdicCompletion.directSumToPi R I A (decayAssemble I A z hdecay) a) =
    Submodule.mkQ (I ^ n • (⊤ : Submodule R R)) (z a)
  rw [coordinate_eval, decayAssemble, AdicCompletion.eval_lift_apply]
  let c := DirectSum.component R A (fun _ : A => R) a
  show (LinearMap.reduceModIdeal (I ^ n) c)
      (Submodule.Quotient.mk (1 • decayTruncation I A z hdecay n)) =
    Submodule.Quotient.mk (z a)
  rw [one_smul, LinearMap.reduceModIdeal_apply, decayTruncation_component]
  by_cases ha : z a ∉ I ^ n
  · simp [ha]
  · have han : z a ∈ I ^ n := by simpa using ha
    have ha' : a ∉ (hdecay n).toFinset := by simpa using ha
    rw [ite_eq_right ha']
    symm
    apply (Submodule.Quotient.mk_eq_zero _).2
    exact (mem_pow_smul_top_iff I n _).mpr han

private theorem exists_adic_order {R : Type u} [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] {x : R} (hx : x ≠ 0) :
    ∃ n : ℕ, x ∈ I ^ n ∧ x ∉ I ^ (n + 1) := by
  classical
  have hbad : ∃ n : ℕ, x ∉ I ^ n := by
    by_contra h
    push Not at h
    have hxinf : x ∈ (⨅ n : ℕ, I ^ n • (⊤ : Submodule R R)) := by
      simpa [Ideal.smul_top_eq_map] using (Submodule.mem_iInf _).mpr h
    rw [IsHausdorff.iInf_pow_smul (inferInstance : IsHausdorff I R)] at hxinf
    exact hx (by simpa using hxinf)
  let d := Nat.find hbad
  have hdnot : x ∉ I ^ d := Nat.find_spec hbad
  have hdpos : 0 < d := Nat.pos_of_ne_zero fun hd0 => hdnot (by simp [hd0])
  have hprev : x ∈ I ^ (d - 1) := not_not.mp (Nat.find_min hbad (show d - 1 < d by omega))
  refine ⟨d - 1, hprev, ?_⟩
  simpa [Nat.sub_add_cancel hdpos] using hdnot

private theorem exists_preimage_smul_top {R : Type u} [CommRing R] (I : Ideal R)
    {M : Type*} [AddCommGroup M] [Module R M] (f : M →ₗ[R] R) {n : ℕ} {x : R}
    (hx : x ∈ I ^ n • LinearMap.range f) :
    ∃ y : M, f y = x ∧ y ∈ I ^ n • (⊤ : Submodule R M) := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr z hz
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hz
    refine ⟨r • y, by simp, Submodule.smul_mem_smul hr Submodule.mem_top⟩
  · rintro x y ⟨x', hx', hxpow⟩ ⟨y', hy', hypow⟩
    refine ⟨x' + y', ?_, add_mem hxpow hypow⟩
    simp [map_add, hx', hy']

private theorem exists_adic_preimage {R : Type u} [CommRing R] (I J : Ideal R)
    [IsNoetherianRing R] [IsAdicComplete I R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (f : M →ₗ[R] R) (hfrange : LinearMap.range f = J) (c : ℕ)
    (hAR : ∀ n ≥ c,
      (I ^ n • (⊤ : Submodule R R)) ⊓ (J : Submodule R R) =
        I ^ (n - c) • (I ^ c • (⊤ : Submodule R R) ⊓ (J : Submodule R R)))
    {x : R} (hx : x ∈ J) :
    ∃ y : M, f y = x ∧ ∀ n : ℕ, x ∈ I ^ (n + c) →
      y ∈ I ^ n • (⊤ : Submodule R M) := by
  classical
  by_cases hx0 : x = 0
  · exact ⟨0, by simp [hx0], fun _ _ => Submodule.zero_mem _⟩
  obtain ⟨d, hxd, hxdone⟩ := exists_adic_order I hx0
  by_cases hcd : c ≤ d
  · have hInf : x ∈ (I ^ d • (⊤ : Submodule R R)) ⊓ (J : Submodule R R) :=
      ⟨by simpa [Ideal.smul_top_eq_map] using hxd, hx⟩
    rw [hAR d hcd] at hInf
    have hsmul : x ∈ I ^ (d - c) • LinearMap.range f := by
      rw [hfrange]
      exact Submodule.smul_mono (le_refl _) inf_le_right hInf
    obtain ⟨y, hy, hypow⟩ := exists_preimage_smul_top I f hsmul
    refine ⟨y, hy, fun n hxn => ?_⟩
    by_cases hnd : n + c ≤ d
    · exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (show n ≤ d - c by omega)) hypow
    · exact (hxdone (Ideal.pow_le_pow_right (show d + 1 ≤ n + c by omega) hxn)).elim
  · obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (show x ∈ LinearMap.range f by rwa [hfrange])
    exact ⟨y, hy, fun n hxn =>
      (hxdone (Ideal.pow_le_pow_right (show d + 1 ≤ n + c by omega) hxn)).elim⟩

private theorem completion_mem_fg_ideal {R : Type u} [CommRing R] (I : Ideal R)
    (A : Type v) [IsNoetherianRing R] [IsAdicComplete I R]
    (J : Ideal R) (hJ : J.FG) (x : completedDirectSum R I A)
    (hx : ∀ a, AdicCompletion.directSumToPi R I A x a ∈ J) :
    x ∈ J • (⊤ : Submodule R (completedDirectSum R I A)) := by
  classical
  obtain ⟨k, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hJ
  let φ : (Fin k →₀ R) →ₗ[R] R := Finsupp.linearCombination R g
  have hφ : LinearMap.range φ = J := by
    show LinearMap.range (Finsupp.linearCombination R g) = J
    rw [Finsupp.range_linearCombination, hg]
  obtain ⟨c, hc⟩ := I.exists_pow_inf_eq_pow_smul (J : Submodule R R)
  let z : A → R := AdicCompletion.directSumToPi R I A x
  have hdecay : ∀ n, {a : A | z a ∉ I ^ n}.Finite := coordinate_support_finite I A x
  let w : A → (Fin k →₀ R) := fun a =>
    Classical.choose (exists_adic_preimage I J φ hφ c hc (hx a))
  have hw (a : A) : φ (w a) = z a :=
    (Classical.choose_spec (exists_adic_preimage I J φ hφ c hc (hx a))).1
  have hwdecay (a : A) (n : ℕ) (hn : z a ∈ I ^ (n + c)) :
      w a ∈ I ^ n • (⊤ : Submodule R (Fin k →₀ R)) :=
    (Classical.choose_spec (exists_adic_preimage I J φ hφ c hc (hx a))).2 n hn
  have hcoeff : ∀ i n, {a : A | w a i ∉ I ^ n}.Finite := by
    intro i n
    apply (hdecay (n + c)).subset
    intro a ha
    change w a i ∉ I ^ n at ha
    show z a ∉ I ^ (n + c)
    intro hza
    exact ha (apply_mem_of_mem_smul_top (I ^ n) (Finsupp.lapply i) (hwdecay a n hza))
  let u : Fin k → completedDirectSum R I A := fun i =>
    decayAssemble I A (fun a => w a i) (fun n => hcoeff i n)
  let y : completedDirectSum R I A := ∑ i, g i • u i
  have hycoord : AdicCompletion.directSumToPi R I A y = z := by
    funext a
    simp only [y, map_sum, LinearMap.map_smul, Finset.sum_apply, Pi.smul_apply]
    simpa [u, decayAssemble_apply, φ,
      Stacks.RingTheory.UniversalExactTFAE.linearCombination_apply_fin, smul_eq_mul, mul_comm]
      using hw a
  have hdiff : AdicCompletion.directSumToPi R I A (x - y) = 0 := by
    simp [map_sub, z, hycoord]
  rw [sub_eq_zero.mp (AdicCompletion.directSumToPi_injective I A (x - y) hdiff)]
  show (∑ i, g i • u i) ∈ J • (⊤ : Submodule R (completedDirectSum R I A))
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
  rw [← hg]
  exact Submodule.subset_span ⟨i, rfl⟩

/-- Let `R` be a Noetherian ring that is `I`-adically complete. Then the canonical map
`(⊕_{α ∈ A} R)^∧ → ∏_{α ∈ A} R` from the `I`-adic completion of a direct sum of copies of `R`
into the product of copies of `R` is universally injective. -/
@[stacks 05BC]
theorem AdicCompletion.universallyInjective_directSumToPi
    (R : Type u) [CommRing R] (I : Ideal R) (A : Type v)
    [IsNoetherianRing R] [IsAdicComplete I R] :
    UniversallyInjective (AdicCompletion.directSumToPi R I A) := by
  classical
  let f := AdicCompletion.directSumToPi R I A
  have hfg : ∀ ⦃J : Ideal R⦄, J.FG →
      Function.Injective ((J • ⊤ : Submodule R (completedDirectSum R I A)).mapQ
        (J • ⊤ : Submodule R (A → R)) f (Submodule.smul_top_le_comap_smul_top J f)) := by
    intro J hJ
    rw [Stacks.UniversalInjectivity.FGIdealTest.injective_mapQ_iff]
    intro x hx
    have hx' : f x ∈ J • (⊤ : Submodule R (A → R)) := by
      simpa [Submodule.mem_comap] using hx
    exact completion_mem_fg_ideal I A J hJ x fun a =>
      apply_mem_of_mem_smul_top J (LinearMap.proj a) hx'
  have : Module.Flat R (A → R) := product_module_flat (R := R) A
  exact (Module.Flat.rTensor_injective_iff_injective_mapQ_smul_top
    (R := R) (M := completedDirectSum R I A) (M' := A → R) f).mpr hfg

end DirectSumToPi

end
