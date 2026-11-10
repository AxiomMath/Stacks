module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Topology
public import StacksFrontier.Examples.Completion.CompleteModuleCategory
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.Flat.CompleteDevissageStep
import StacksCore.Tactic.StacksAttribute

/-!
# Adically complete modules need not form an abelian category

Although the category of `I`-adically complete modules has kernels and cokernels, it need not
be abelian: for the `p`-adic integers and the ideal `(p)` it is not.

## Main results

* `Stacks.Examples.not_abelian_iAdicallyCompleteModuleCat_of_principal`: for a Noetherian ring
  without zero divisors, complete for a principal ideal whose generator is neither zero nor a
  unit, the category of adically complete modules is not abelian.
* `Stacks.Examples.not_abelian_iAdicallyCompleteModuleCat_of_span_singleton`: the same for the
  ideal `(π)`, with modules in `Type (max u v)`.
* `Stacks.Examples.exists_not_abelian_iAdicallyCompleteModuleCat`: there is a commutative ring
  with a finitely generated ideal for which the category of adically complete modules is not
  abelian.

## References

* [Stacks Project, Tag 07JR](https://stacks.math.columbia.edu/tag/07JR)
* [Stacks Project, Tag 05BC](https://stacks.math.columbia.edu/tag/05BC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum TensorProduct

namespace Stacks.Examples

universe u v

/-- A linear map carries `Iⁿ • ⊤` elements to `Iⁿ • ⊤` elements. -/
private lemma map_mem_pow_smul_top
    {R : Type u} [CommRing R] {I : Ideal R} {M N : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) {n : ℕ} {x : M}
    (hx : x ∈ I ^ n • (⊤ : Submodule R M)) : f x ∈ I ^ n • (⊤ : Submodule R N) :=
  map_pow_smul_top_le f n ⟨x, hx, rfl⟩

/-- `aⁿ • x` lies in `(a)ⁿ • ⊤`. -/
private lemma pow_smul_mem_span_pow_smul_top
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (a : R) (n : ℕ) (x : M) :
    a ^ n • x ∈ Ideal.span {a} ^ n • (⊤ : Submodule R M) :=
  Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self a) n)
    Submodule.mem_top

/-- A countable product of modules complete for a principal ideal is complete. -/
private lemma isAdicComplete_pi_principal
    {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]
    (a : R) [IsAdicComplete (Ideal.span {a}) E] :
    IsAdicComplete (Ideal.span {a}) (ℕ → E) := by
  let I : Ideal R := Ideal.span {a}
  have hpow (n : ℕ) : I ^ n = Ideal.span {a ^ n} := by
    simp [I, Ideal.span_singleton_pow]
  have hHaus : IsHausdorff I (ℕ → E) := ⟨fun x hx ↦ funext fun i ↦
    IsHausdorff.haus (inferInstance : IsHausdorff I E) (x i) fun n ↦ SModEq.zero.mpr
      (map_mem_pow_smul_top (LinearMap.proj i) (SModEq.zero.mp (hx n)))⟩
  have hPre : IsPrecomplete I (ℕ → E) := ⟨fun f hf ↦ by
    have hcoordCauchy (i : ℕ) : ∀ {m n}, m ≤ n → f m i ≡ f n i
        [SMOD (I ^ m • (⊤ : Submodule R E))] := by
      intro m n hmn
      have hi : (f m - f n) i ∈ I ^ m • (⊤ : Submodule R E) :=
        map_mem_pow_smul_top (LinearMap.proj i) (SModEq.sub_mem.mp (hf hmn))
      exact SModEq.sub_mem.mpr (by simpa using hi)
    choose L hL using fun i ↦ IsPrecomplete.prec
      (inferInstance : IsPrecomplete I E) (hcoordCauchy i)
    refine ⟨L, fun n ↦ ?_⟩
    rw [SModEq.sub_mem]
    have hquot (i : ℕ) : ∃ z : E, a ^ n • z = f n i - L i := by
      have hm : f n i - L i ∈ I ^ n • (⊤ : Submodule R E) := SModEq.sub_mem.mp (hL i n)
      rw [hpow n, Submodule.ideal_span_singleton_smul] at hm
      obtain ⟨z, -, hz⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hm
      exact ⟨z, hz⟩
    choose qn hqn using hquot
    rw [show f n - L = a ^ n • qn from funext fun i ↦ (hqn i).symm]
    exact pow_smul_mem_span_pow_smul_top a n qn⟩
  exact ⟨⟩

private theorem directSumToPi_of_apply
    {R : Type u} [CommRing R] (I : Ideal R) (A : Type v) [IsAdicComplete I R]
    (x : DirectSum A (fun _ : A => R)) (a : A) :
    AdicCompletion.directSumToPi R I A (AdicCompletion.of I _ x) a = x a := by
  simp [AdicCompletion.directSumToPi, AdicCompletion.map_of]
  rfl

/-- The sum of the first `k` standard basis vectors of `⊕ₙ R`. -/
private noncomputable def truncDirectSum
    (R : Type u) [CommRing R] (k : ℕ) : DirectSum ℕ (fun _ : ℕ => R) :=
  finsuppLEquivDirectSum R R ℕ (∑ i ∈ Finset.range k, Finsupp.single i (1 : R))

private theorem truncDirectSum_component
    {R : Type u} [CommRing R] (k i : ℕ) :
    DirectSum.component R ℕ (fun _ : ℕ => R) i (truncDirectSum R k) =
      if i < k then 1 else 0 := by
  classical
  change Finsupp.lapply (R := R) (M := R) i
    (∑ j ∈ Finset.range k, Finsupp.single j (1 : R)) = _
  rw [map_sum]
  simp [Finsupp.lapply_apply, Finsupp.single_apply, Finset.sum_ite_eq']

/-- If `R` is a Noetherian ring without zero divisors which is complete for a principal ideal
`I = (π)` whose generator is neither zero nor a unit, and `E : Type v` is an `R`-module with a
linear equivalence `E ≃ₗ[R] R`, then the category of `I`-adically complete `R`-modules in
`Type v` is not abelian. -/
@[stacks 07JR "not_abelian, for a named ring and a named principal ideal"]
theorem not_abelian_iAdicallyCompleteModuleCat_of_principal
    (R : Type u) [CommRing R] [IsNoetherianRing R] [NoZeroDivisors R]
    (I : Ideal R) (hR : IsAdicComplete I R) (π : R) (hIspan : I = Ideal.span {π})
    (hπ : π ≠ 0) (hπnonunit : ¬ IsUnit π)
    (E : Type v) [AddCommGroup E] [Module R E] (eER : E ≃ₗ[R] R) :
    ¬ Nonempty (Abelian (IAdicallyCompleteModuleCat.{v} R I)) := by
  classical
  let _ : IsAdicComplete I R := hR
  have hE : IsAdicComplete I E := isAdicComplete_of_linearEquiv eER hR
  let _ : IsAdicComplete I E := hE
  let N := ℕ → E
  have hN : IsAdicComplete I N := by
    let _ : IsAdicComplete (Ideal.span {π}) E := by simpa [hIspan] using hE
    simpa [hIspan, N] using (isAdicComplete_pi_principal (R := R) (E := E) π)
  have hIFG : I.FG := hIspan ▸ Submodule.fg_span (Set.finite_singleton π)
  let _ : IsAdicComplete I N := hN
  let D := DirectSum ℕ (fun _ : ℕ ↦ R)
  let DE := DirectSum ℕ (fun _ : ℕ ↦ E)
  let eD : DE ≃ₗ[R] D := DirectSum.congrLinearEquiv fun _ ↦ eER
  let M := AdicCompletion I DE
  let eC : M ≃ₗ[R] AdicCompletion I D :=
    (AdicCompletion.congr I eD).restrictScalars R
  let ePi : N ≃ₗ[R] (ℕ → R) := LinearEquiv.piCongrRight fun _ ↦ eER
  let fBase : M →ₗ[R] (ℕ → R) :=
    (AdicCompletion.directSumToPi R I ℕ).comp eC.toLinearMap
  let f : M →ₗ[R] N := ePi.symm.toLinearMap.comp fBase
  let d : N →ₗ[R] N :=
    { toFun := fun z i ↦ π ^ i • z i
      map_add' := by
        intro x y
        funext i
        change π ^ i • (x i + y i) = π ^ i • x i + π ^ i • y i
        exact smul_add _ _ _
      map_smul' := by
        intro r x
        funext i
        change π ^ i • (r • x i) = r • (π ^ i • x i)
        rw [smul_comm] }
  let g : M →ₗ[R] N := d.comp f
  have h1not : (1 : R) ∉ I := by
    rw [hIspan, Ideal.mem_span_singleton]
    exact fun h ↦ hπnonunit (isUnit_of_dvd_one h)
  have hfBase : Function.Injective fBase := by
    intro x y hxy
    apply eC.injective
    apply Module.injective_of_universallyInjective _
      (AdicCompletion.universallyInjective_directSumToPi R I ℕ)
    simpa [fBase] using hxy
  have hf : Function.Injective f := fun x y hxy ↦ hfBase (by simpa [f] using congrArg ePi hxy)
  have hd : Function.Injective d := by
    intro x y hxy
    funext i
    apply eER.injective
    apply mul_left_cancel₀ (pow_ne_zero i hπ)
    simpa [d, eER.map_smul, smul_eq_mul] using congrArg eER (congrFun hxy i)
  have hg : Function.Injective g := hd.comp hf
  have hMobj : IsAdicComplete I M := AdicCompletion.isAdicComplete hIFG
  have hNobj : IsAdicComplete I N := hN
  let C := IAdicallyCompleteModuleCat.{v} R I
  let X : C := ⟨ModuleCat.of R M, hMobj⟩
  let Y : C := ⟨ModuleCat.of R N, hNobj⟩
  let fcat : X ⟶ Y := ObjectProperty.homMk (ModuleCat.ofHom g)
  have hmono : Mono fcat := by
    refine ⟨?_⟩
    intro Z a b hab
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply hg
    exact congrArg (fun t : Z ⟶ Y ↦ t.hom.hom z) hab
  let _ : Mono fcat := hmono
  intro hAb
  let _ : Abelian C := hAb.some
  let hAbPre : Preadditive C := hAb.some.toPreadditive
  let _ : Preadditive C := hAbPre
  let hzm : HasZeroMorphisms C := @Preadditive.preadditiveHasZeroMorphisms C _ hAbPre
  let _ : HasZeroMorphisms C := hzm
  let _ : IsNormalMonoCategory C := hAb.some.toIsNormalMonoCategory
  let nm : @NormalMono C _ X Y hzm fcat := normalMonoOfMono fcat
  let q : N →ₗ[R] nm.Z.obj := nm.g.hom.hom
  have hZ : IsAdicComplete I nm.Z.obj := nm.Z.property
  let hzmCanonical : HasZeroMorphisms C := ObjectProperty.instHasZeroMorphismsFullSubcategory _
  have hzeroMap (A B : C) :
      ModuleCat.Hom.hom ((@Zero.zero _ (hzm.zero A B)).hom) = 0 := by
    let zCurrent : A ⟶ B := @Zero.zero _ (hzm.zero A B)
    let zCanonical : A ⟶ B := @Zero.zero _ (hzmCanonical.zero A B)
    have hzmEq := Limits.HasZeroMorphisms.ext hzm hzmCanonical
    have hzEq : zCurrent = zCanonical :=
      congrArg (fun H : HasZeroMorphisms C ↦ @Zero.zero _ (H.zero A B)) hzmEq
    calc
      ModuleCat.Hom.hom zCurrent.hom = ModuleCat.Hom.hom zCanonical.hom :=
        congrArg (fun z : A ⟶ B ↦ ModuleCat.Hom.hom z.hom) hzEq
      _ = 0 := congrArg ModuleCat.Hom.hom (ObjectProperty.zero_hom _ A B)
  let y : N := fun i ↦ eER.symm (π ^ i)
  have hcoord (z : M) (i : ℕ) : eER (f z i) = fBase z i :=
    congrFun (show ePi (f z) = fBase z by simp [f]) i
  have hweight (z : M) (i : ℕ) : eER (g z i) = π ^ i * fBase z i := by
    change eER (π ^ i • f z i) = π ^ i * fBase z i
    rw [eER.map_smul]
    simp [smul_eq_mul, hcoord]
  have hqg (z : M) : q (g z) = 0 := by
    have hw' : nm.g.hom.hom.comp g = 0 := by
      have hw := congrArg (fun t : X ⟶ nm.Z ↦ t.hom.hom) nm.w
      rw [ObjectProperty.FullSubcategory.comp_hom, ModuleCat.hom_comp] at hw
      change nm.g.hom.hom ∘ₗ g =
        ModuleCat.Hom.hom ((@Zero.zero _ (hzm.zero X nm.Z)).hom) at hw
      rwa [hzeroMap X nm.Z] at hw
    simpa [q, LinearMap.comp_apply] using congrArg (fun F : M →ₗ[R] nm.Z.obj ↦ F z) hw'
  have hqzero : q y = 0 := by
    apply IsHausdorff.haus (inferInstance : IsHausdorff I nm.Z.obj) (q y)
    intro k
    let xk : M := eC.symm (AdicCompletion.of I D (truncDirectSum R k))
    let wk : N := fun i ↦ eER.symm (if k ≤ i then π ^ (i - k) else 0)
    have hbasek (i : ℕ) : fBase xk i = if i < k then 1 else 0 := by
      change AdicCompletion.directSumToPi R I ℕ
        (eC (eC.symm (AdicCompletion.of I D (truncDirectSum R k)))) i = _
      rw [eC.apply_symm_apply, directSumToPi_of_apply]
      exact truncDirectSum_component (R := R) k i
    have hclose : y - g xk = π ^ k • wk := by
      funext i
      apply eER.injective
      change eER (y i - g xk i) = eER (π ^ k • wk i)
      rw [map_sub, hweight xk i, eER.map_smul]
      simp only [y, wk, eER.apply_symm_apply]
      by_cases hik : i < k
      · have hki : ¬ k ≤ i := Nat.not_le_of_gt hik
        have hw0 : fBase xk i = 1 := by simpa [hik] using hbasek i
        simp [hki, hw0, smul_eq_mul]
      · have hki : k ≤ i := le_of_not_gt hik
        have hbase0 : fBase xk i = 0 := by simpa [hik] using hbasek i
        have hiEq : i = k + (i - k) := (Nat.add_sub_of_le hki).symm
        simp only [hbase0, mul_zero, sub_zero, hki, ite_eq_left, smul_eq_mul]
        rw [hiEq, pow_add]
        simp
    have hmem : y - g xk ∈ I ^ k • (⊤ : Submodule R N) := by
      rw [hclose, hIspan]
      exact pow_smul_mem_span_pow_smul_top π k wk
    have hqmem : q y ∈ I ^ k • (⊤ : Submodule R nm.Z.obj) := by
      have hqdiff : q (y - g xk) = q y := by simp [map_sub, hqg]
      rw [← hqdiff]
      exact map_mem_pow_smul_top q hmem
    exact SModEq.zero.mpr hqmem
  have hEobj : IsAdicComplete I E := hE
  let W : C := ⟨ModuleCat.of R E, hEobj⟩
  let kLin : E →ₗ[R] N :=
    { toFun := fun s ↦ eER s • y
      map_add' := by intro s t; simp [map_add, add_smul]
      map_smul' := by
        intro r s
        simp [eER.map_smul, mul_smul] }
  let k : W ⟶ Y := ObjectProperty.homMk (ModuleCat.ofHom kLin)
  have hk : k ≫ nm.g = @Zero.zero _ (hzm.zero W nm.Z) := by
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    rw [ObjectProperty.FullSubcategory.comp_hom, ModuleCat.hom_comp,
      LinearMap.comp_apply]
    change q (eER r • y) =
      ModuleCat.Hom.hom ((@Zero.zero _ (hzm.zero W nm.Z)).hom) r
    rw [hzeroMap W nm.Z, map_smul, hqzero, smul_zero]
    simp
  let fac := @NormalMono.lift' C _ X Y hzm W fcat nm k hk
  let z : M := fac.val.hom.hom (eER.symm 1)
  have hzy : g z = y := by
    have hfac := congrArg (fun t : W ⟶ Y ↦ t.hom.hom (eER.symm 1)) fac.property
    rw [ObjectProperty.FullSubcategory.comp_hom, ModuleCat.hom_comp] at hfac
    change (ModuleCat.Hom.hom fcat.hom)
        (ModuleCat.Hom.hom fac.val.hom (eER.symm 1)) =
      (ModuleCat.Hom.hom k.hom) (eER.symm 1) at hfac
    simpa [z, fcat, k, kLin, ModuleCat.hom_ofHom, eER.apply_symm_apply] using hfac
  have hcoordOne (i : ℕ) : fBase z i = 1 := by
    have hi : π ^ i * fBase z i = π ^ i :=
      calc
        π ^ i * fBase z i = eER (g z i) := (hweight z i).symm
        _ = eER (y i) := by rw [hzy]
        _ = π ^ i := by simp [y]
    exact (mul_left_cancel₀ (pow_ne_zero i hπ)) (by simpa using hi)
  have hfinite := coordinate_support_finite I ℕ (eC z) 1
  have hsubset : (Set.univ : Set ℕ) ⊆
      {i | AdicCompletion.directSumToPi R I ℕ (eC z) i ∉ I ^ 1} := by
    intro i _
    have hi : fBase z i ∉ I ^ 1 := by
      rw [pow_one, hcoordOne i]
      exact h1not
    simpa [fBase] using hi
  exact Set.infinite_univ.not_finite (hfinite.subset hsubset)

/-- If `R` is a Noetherian ring without zero divisors, complete for `(π)` with `π` neither zero
nor a unit, then the category of `(π)`-adically complete `R`-modules in `Type (max u v)` is not
abelian. -/
theorem not_abelian_iAdicallyCompleteModuleCat_of_span_singleton
    (R : Type u) [CommRing R] [IsNoetherianRing R] [NoZeroDivisors R] (π : R)
    (hR : IsAdicComplete (Ideal.span {π}) R) (hπ : π ≠ 0) (hπnonunit : ¬ IsUnit π) :
    ¬ Nonempty (Abelian (IAdicallyCompleteModuleCat.{max u v} R (Ideal.span {π}))) :=
  not_abelian_iAdicallyCompleteModuleCat_of_principal R (Ideal.span {π}) hR π rfl hπ hπnonunit
    (ULift.{v} R) ULift.moduleEquiv

/-- There is a commutative ring with a finitely generated ideal for which the category of
adically complete modules is not abelian. -/
@[stacks 07JR "not_abelian"]
theorem exists_not_abelian_iAdicallyCompleteModuleCat :
    ∃ (R : Type u) (_ : CommRing R) (I : Ideal R),
      I.FG ∧ ¬ Nonempty (Abelian (IAdicallyCompleteModuleCat.{v} R I)) := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P := PadicInt 2
  let I₀ : Ideal P := Ideal.span {(2 : P)}
  have hP : IsAdicComplete I₀ P := by
    rw [show I₀ = IsLocalRing.maximalIdeal P from PadicInt.maximalIdeal_eq_span_p.symm]
    infer_instance
  let R := ULift.{u} P
  let eRP : P ≃+* R := ULift.ringEquiv.symm
  let I : Ideal R := I₀.map eRP
  let π : R := eRP (2 : P)
  have hIspan : I = Ideal.span {π} := by
    simp [I, I₀, π, Ideal.map_span]
  have hR : IsAdicComplete I R := by
    change IsAdicComplete (I₀.map eRP) R
    exact (IsAdicComplete.congr_ringEquiv I₀ eRP).mpr hP
  have : IsNoetherianRing R :=
    isNoetherianRing_of_surjective P R eRP.toRingHom eRP.surjective
  let _ : IsDomain R := eRP.toMulEquiv.isDomain_iff.mp (inferInstance : IsDomain P)
  let _ : Module R P := Module.compHom P eRP.symm.toRingHom
  let E := ULift.{v} P
  let eER : E ≃ₗ[R] R :=
    { toFun := fun x ↦ eRP x.down
      invFun := fun r ↦ ULift.up (eRP.symm r)
      left_inv := fun _ ↦ rfl
      right_inv := eRP.apply_symm_apply
      map_add' := fun x y ↦ map_add eRP x.down y.down
      map_smul' := by
        intro r x
        change eRP (eRP.symm r * x.down) = r * eRP x.down
        simp }
  have hIFG : I.FG := hIspan ▸ Submodule.fg_span (Set.finite_singleton π)
  have hπ : π ≠ 0 := fun h ↦ by
    have h2 : (2 : P) = 0 := eRP.injective (h.trans (map_zero eRP).symm)
    norm_num at h2
  have h2nonunit : ¬ IsUnit (2 : P) := mod_cast PadicInt.p_nonunit (p := 2)
  have hπnonunit : ¬ IsUnit π := fun hu ↦
    h2nonunit (by simpa [π] using hu.map eRP.symm.toMonoidHom)
  exact ⟨R, inferInstance, I, hIFG,
    not_abelian_iAdicallyCompleteModuleCat_of_principal R I hR π hIspan hπ hπnonunit E eER⟩

end Stacks.Examples

end
