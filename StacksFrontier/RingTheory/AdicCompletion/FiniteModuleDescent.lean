module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.RingTheory.AdicCompletion.FiniteModuleTorsion
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingEquivalence
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingFlatIsomorphism
public import StacksFrontier.RingTheory.Localization.Glueing.IdealPowerTorsion
public import StacksFrontier.RingTheory.AdicCompletion.QuotientBijective

/-!
# Descending a map of finite modules along an adic completion

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `A^∧` the `I`-adic completion of `A`. Write
`J = I A^∧` for the extension of `I`. Given a finite `A`-module `N`, a finite `A^∧`-module `M'`
and an `A^∧`-linear map `φ : M' → A^∧ ⊗_A N` whose kernel and cokernel are `J`-power torsion,
the map `φ` is the completion of a map of finite `A`-modules: there are a finite `A`-module `M`,
an `A`-linear map `ψ : M → N` with `I`-power torsion kernel and cokernel, and an `A^∧`-linear
isomorphism `e : A^∧ ⊗_A M ≅ M'` with `φ ∘ e = ψ ⊗ 1`. Moreover the triple `(M, ψ, e)` is unique
up to a unique isomorphism.

## Main results

* `AdicCompletion.existsUnique_of_descent`: a descent of `φ` realizes `M` as the fibre product of
  `N` and `M'` over `A^∧ ⊗_A N`.
* `AdicCompletion.exists_finite_descent_of_isIPowerTorsion`: existence of the descent `(M, ψ, e)`,
  with `M` finite over `A` and with `I`-power torsion kernel and cokernel for `ψ`.
* `AdicCompletion.descent_unique`: two descents of the same `φ` are related by a unique
  isomorphism compatible with the maps to `N` and with the identifications of `M'`.

## References

* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 0ALK](https://stacks.math.columbia.edu/tag/0ALK)
* [Stacks Project, Tag 05EU](https://stacks.math.columbia.edu/tag/05EU)
-/

universe u v w

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped ChangeOfRings
open Stacks.AdicCompletion.FiniteModule

/-! ### Extension of scalars as a tensor product -/

/-- Two `S`-linear maps out of `S ⊗[R] M` agree as soon as they agree on the elements `1 ⊗ m`. -/
private lemma tensor_linearMap_ext
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {M : Type w} [AddCommGroup M] [Module R M]
    {P : Type*} [AddCommGroup P] [Module S P]
    (f g : TensorProduct R S M →ₗ[S] P)
    (h : ∀ m : M, f ((1 : S) ⊗ₜ[R] m) = g ((1 : S) ⊗ₜ[R] m)) :
    f = g := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
    have hs : (s ⊗ₜ[R] m : TensorProduct R S M) = s • ((1 : S) ⊗ₜ[R] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hs, map_smul, map_smul, h]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-! ### Finiteness of the descended module -/

/-- A module mapping to a finite module over a Noetherian ring is finite once its kernel is
finite. -/
private theorem finite_of_finite_kernel_of_finite_target
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M N : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (f : M →ₗ[R] N) [Module.Finite R (LinearMap.ker f)] :
    Module.Finite R M := by
  have : Module.Finite R (LinearMap.range f) :=
    Module.Finite.of_fg (Submodule.FG.of_le Module.Finite.fg_top le_top)
  exact Module.Finite.of_exact
    (f := (LinearMap.ker f).subtype) (g := f.rangeRestrict)
    (by rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])
    f.surjective_rangeRestrict

/-- Over a Noetherian ring `R`, the source `M` of a map `ψ : M ⟶ N` with `N` finite is finite as
soon as the kernel of `ψ` is isomorphic to an `R`-module that is finite. -/
private theorem finite_descended_module_of_finite_restricted_kernel
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsNoetherianRing R] (a : R →+* S)
    (M N : ModuleCat.{w} R) [Module.Finite R N]
    (M' N' : ModuleCat.{w} S) (φ : M' ⟶ N') (ψ : M ⟶ N)
    (eK : (ModuleCat.restrictScalars.{w} a).obj (kernel φ) ≅ kernel ψ)
    [Module.Finite R ((ModuleCat.restrictScalars.{w} a).obj (kernel φ))] :
    Module.Finite R M := by
  have : Module.Finite R ((kernel ψ : ModuleCat R) : Type _) :=
    Module.Finite.equiv eK.toLinearEquiv
  have : Module.Finite R (LinearMap.ker ψ.hom) :=
    Module.Finite.equiv (ModuleCat.kernelIsoKer ψ).toLinearEquiv
  exact finite_of_finite_kernel_of_finite_target ψ.hom

/-! ### Descent along a flat map which is an isomorphism modulo `I` -/

/-- Formal glueing descent of a map to a finite module, with finiteness of the descended module
and power torsion of its kernel and cokernel. -/
private theorem finite_formalGlueing_descent
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (I : Ideal R) (hI : I.FG) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (N : ModuleCat.{max u v} R) (M' : ModuleCat.{max u v} S)
    [Module.Finite R N] [Module.Finite S M']
    (φ : M' ⟶ (ModuleCat.extendScalars.{u, u, max u v} (algebraMap R S)).obj N)
    (hK : IsIPowerTorsion S (↥(kernel φ : ModuleCat.{max u v} S)) (I.map (algebraMap R S)))
    (hC : IsIPowerTorsion S (↥(cokernel φ : ModuleCat.{max u v} S)) (I.map (algebraMap R S))) :
    ∃ (M : ModuleCat.{max u v} R) (ψ : M ⟶ N)
      (e : (ModuleCat.extendScalars.{u, u, max u v} (algebraMap R S)).obj M ≅ M'),
      Module.Finite R M ∧
        IsIPowerTorsion R (↥(kernel ψ : ModuleCat.{max u v} R)) I ∧
        IsIPowerTorsion R (↥(cokernel ψ : ModuleCat.{max u v} R)) I ∧
        e.hom ≫ φ = (ModuleCat.extendScalars.{u, u, max u v} (algebraMap R S)).map ψ := by
  obtain ⟨M, ψ, e, eK, eC, he⟩ :=
    (FormalGlueing.exists_descent_of_idealPowerTorsion_kernel_cokernel.{u, u, v}
      R S I hI hflat hq).1 N M' φ hK hC
  let J := I.map (algebraMap R S)
  have : Module.Finite S (LinearMap.ker φ.hom) :=
    Module.Finite.of_fg (Submodule.FG.of_le Module.Finite.fg_top le_top)
  have : Module.Finite S (kernel φ : ModuleCat.{max u v} S) :=
    Module.Finite.equiv (ModuleCat.kernelIsoKer φ).toLinearEquiv.symm
  obtain ⟨n, hn⟩ := ideal_smul_eq_bot_of_finite_power_torsion J (hI.map (algebraMap R S))
    (kernel φ : ModuleCat.{max u v} S) hK
  have : Module.Finite R (S ⧸ J ^ n) := by
    have hfinite := finite_quotient_of_quotientMap_surjective (I ^ n)
      (quotientMap_pow_surjective_of_flat I hflat hq n)
    rwa [Ideal.map_pow] at hfinite
  have : Module.Finite R
      ((ModuleCat.restrictScalars.{max u v} (algebraMap R S)).obj (kernel φ)) :=
    finite_restrictScalars_of_annihilated (M := (kernel φ : ModuleCat.{max u v} S)) (J ^ n) hn
  have hM : Module.Finite R M :=
    finite_descended_module_of_finite_restricted_kernel (algebraMap R S) M N M'
      ((ModuleCat.extendScalars.{u, u, max u v} (algebraMap R S)).obj N) φ ψ eK
  have hT := map_kernel_cokernel_isIPowerTorsion I φ ψ eK eC hK hC
  exact ⟨M, ψ, e, hM, hT.1, hT.2, he⟩

/-! ### The fibre-product property of a descent -/

/-- Let `S` be a flat `R`-algebra such that `R ⧸ I → S ⧸ I S` is bijective, and let `f : M → N`
have `I`-power torsion kernel and cokernel. Then every pair `(n, x)` with `(f ⊗ S) x = n ⊗ 1`
comes from a unique `m : M`, that is, `M` is the fibre product of `N` and `M ⊗[R] S` over
`N ⊗[R] S`. -/
private theorem module_pullback_of_idealPowerTorsion
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    {M N : Type (max u v)} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N)
    (hK : IsIPowerTorsion R (LinearMap.ker f) I)
    (hC : IsIPowerTorsion R (N ⧸ LinearMap.range f) I)
    (n : N) (x : TensorProduct R M S)
    (hx : (f.rTensor S) x = IPowerTorsion.unitMap R S N n) :
    ∃! m : M, f m = n ∧ IPowerTorsion.unitMap R S M m = x := by
  have : Module.Flat R S := hflat
  have hu :=
    (IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective.{u, u, v}
      R S I hflat).2 hq
  have huK : Function.Bijective (IPowerTorsion.unitMap R S (LinearMap.ker f)) := hu _ hK
  have huC : Function.Bijective (IPowerTorsion.unitMap R S (N ⧸ LinearMap.range f)) := hu _ hC
  let q : N →ₗ[R] N ⧸ LinearMap.range f := (LinearMap.range f).mkQ
  have hqf : q.comp f = 0 := by
    ext m
    exact Submodule.Quotient.mk_eq_zero (LinearMap.range f) |>.2 ⟨m, rfl⟩
  have hqzero : q n = 0 := by
    apply huC.1
    have hc : (q.rTensor S).comp (f.rTensor S) = 0 := by
      rw [← LinearMap.rTensor_comp, hqf]
      simp
    simp only [map_zero]
    calc
      _ = (q.rTensor S) (IPowerTorsion.unitMap R S N n) := by simp [IPowerTorsion.unitMap]
      _ = (q.rTensor S) ((f.rTensor S) x) := by rw [hx]
      _ = 0 := LinearMap.congr_fun hc x
  obtain ⟨m₀, hm₀⟩ := (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).1 hqzero
  let y := x - IPowerTorsion.unitMap R S M m₀
  have hy : (f.rTensor S) y = 0 := by
    have hnat : (f.rTensor S) (IPowerTorsion.unitMap R S M m₀) =
        IPowerTorsion.unitMap R S N (f m₀) := by simp [IPowerTorsion.unitMap]
    dsimp only [y]
    rw [map_sub, hx, hnat, hm₀, sub_self]
  obtain ⟨z, hz⟩ := (Module.Flat.rTensor_exact S f.exact_subtype_ker_map y).mp hy
  obtain ⟨k, hk⟩ := huK.2 z
  have hzk : (f.ker.subtype.rTensor S) z = IPowerTorsion.unitMap R S M k.1 := by
    rw [← hk]
    simp [IPowerTorsion.unitMap]
  have hy' : y = IPowerTorsion.unitMap R S M k.1 := by rw [← hzk, hz]
  have hmk : IPowerTorsion.unitMap R S M (m₀ + k.1) = x := by
    have hsum := congrArg (fun t => t + IPowerTorsion.unitMap R S M m₀) hy'
    simp only [y, sub_add_cancel] at hsum
    calc
      _ = IPowerTorsion.unitMap R S M m₀ + IPowerTorsion.unitMap R S M k.1 := map_add _ _ _
      _ = IPowerTorsion.unitMap R S M k.1 + IPowerTorsion.unitMap R S M m₀ := add_comm _ _
      _ = x := hsum.symm
  refine ⟨m₀ + k.1, ⟨by simp [hm₀], hmk⟩, ?_⟩
  intro m hm
  have hdiff : m - (m₀ + k.1) ∈ f.ker := by
    show f (m - (m₀ + k.1)) = 0
    rw [map_sub, hm.1]
    simp [hm₀]
  let d : f.ker := ⟨m - (m₀ + k.1), hdiff⟩
  have hd : IPowerTorsion.unitMap R S f.ker d = 0 := by
    apply (Module.Flat.rTensor_preserves_injective_linearMap
      f.ker.subtype f.ker.injective_subtype)
    have hdz : IPowerTorsion.unitMap R S M (m - (m₀ + k.1)) = 0 := by
      rw [map_sub, hm.2, hmk, sub_self]
    have hnat : (f.ker.subtype.rTensor S) (IPowerTorsion.unitMap R S f.ker d) =
        IPowerTorsion.unitMap R S M (m - (m₀ + k.1)) := by
      show (f.ker.subtype.rTensor S) (d ⊗ₜ[R] (1 : S)) = (m - (m₀ + k.1)) ⊗ₜ[R] (1 : S)
      rw [LinearMap.rTensor_tmul]
      rfl
    simpa only [map_zero] using hnat.trans hdz
  have hd0 : d = 0 := huK.1 (by simpa using hd)
  exact sub_eq_zero.mp (congrArg Subtype.val hd0)

/-- The fibre-product property of `module_pullback_of_idealPowerTorsion`, with the base change
written as `S ⊗[R] M`. -/
private theorem module_pullback_of_idealPowerTorsion'
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    {M N : Type (max u v)} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N)
    (hK : IsIPowerTorsion R (LinearMap.ker f) I)
    (hC : IsIPowerTorsion R (N ⧸ LinearMap.range f) I)
    (n : N) (x : TensorProduct R S M)
    (hx : LinearMap.baseChange S f x = (1 : S) ⊗ₜ[R] n) :
    ∃! m : M, f m = n ∧ (1 : S) ⊗ₜ[R] m = x := by
  let cM := TensorProduct.comm R S M
  let cN := TensorProduct.comm R S N
  have hcomm (z : TensorProduct R S M) :
      (f.rTensor S) (cM z) = cN (LinearMap.baseChange S f z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s m => simp [cM, cN]
    | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]
  have hx' : (f.rTensor S) (cM x) = IPowerTorsion.unitMap R S N n := by
    rw [hcomm, hx]
    rfl
  obtain ⟨m, hm, huniq⟩ :=
    module_pullback_of_idealPowerTorsion.{u, v} I hflat hq f hK hC n (cM x) hx'
  refine ⟨m, ⟨hm.1, cM.injective ?_⟩, fun m' hm' => huniq m' ⟨hm'.1, ?_⟩⟩
  · exact (by rfl : cM ((1 : S) ⊗ₜ[R] m) = IPowerTorsion.unitMap R S M m).trans hm.2
  · exact (by rfl : IPowerTorsion.unitMap R S M m' = cM ((1 : S) ⊗ₜ[R] m')).trans
      (congrArg cM hm'.2)

/-! ### Descent along the adic completion -/

/-- Let `A` be a Noetherian ring, `I ⊆ A` an ideal
and `S = A^∧` its `I`-adic completion. Suppose `ψ : M → N` is a map of `A`-modules with
`I`-power torsion kernel and cokernel, and that `e : S ⊗_A M ≅ M'` identifies the base change of
`ψ` with a map `φ : M' → S ⊗_A N`. Then `M` is the fibre product of `N` and `M'` over `S ⊗_A N`:
every pair `(n, y)` with `φ y = 1 ⊗ n` comes from a unique element of `M`. -/
public theorem AdicCompletion.existsUnique_of_descent
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {M N : Type (max u v)} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {M' : Type (max u v)} [AddCommGroup M'] [Module (AdicCompletion I A) M']
    (ψ : M →ₗ[A] N) (φ : M' →ₗ[AdicCompletion I A] TensorProduct A (AdicCompletion I A) N)
    (e : TensorProduct A (AdicCompletion I A) M ≃ₗ[AdicCompletion I A] M')
    (he : φ.comp e.toLinearMap = LinearMap.baseChange (AdicCompletion I A) ψ)
    (hK : IsIPowerTorsion A (LinearMap.ker ψ) I)
    (hC : IsIPowerTorsion A (N ⧸ LinearMap.range ψ) I)
    (n : N) (y : M') (hy : φ y = (1 : AdicCompletion I A) ⊗ₜ[A] n) :
    ∃! m : M, ψ m = n ∧ e ((1 : AdicCompletion I A) ⊗ₜ[A] m) = y := by
  have hbase : LinearMap.baseChange (AdicCompletion I A) ψ (e.symm y) =
      (1 : AdicCompletion I A) ⊗ₜ[A] n := by
    rw [← he]
    show φ (e (e.symm y)) = _
    rw [e.apply_symm_apply, hy]
  obtain ⟨m, hm, huniq⟩ :=
    module_pullback_of_idealPowerTorsion'.{u, v} I (AdicCompletion.flat_of_isNoetherian I)
      (AdicCompletion.quotientMap_bijective I I.fg_of_isNoetherianRing) ψ hK hC n (e.symm y) hbase
  refine ⟨m, ⟨hm.1, ?_⟩, fun m' hm' => huniq m' ⟨hm'.1, ?_⟩⟩
  · rw [hm.2, e.apply_symm_apply]
  · rw [← hm'.2, e.symm_apply_apply]

/-- Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `S = A^∧` its
`I`-adic completion. Let `N` be a finite `A`-module, `M'` a finite `S`-module, and
`φ : M' → S ⊗_A N` an `S`-linear map whose kernel and cokernel are `IS`-power torsion. Then there
are a finite `A`-module `M`, an `A`-linear map `ψ : M → N` with `I`-power torsion kernel and
cokernel, and an `S`-linear isomorphism `e : S ⊗_A M ≅ M'` with `φ ∘ e` the base change of `ψ`. -/
public theorem AdicCompletion.exists_finite_descent_of_isIPowerTorsion
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (N : ModuleCat.{max u v} A) [Module.Finite A N]
    (M' : ModuleCat.{max u v} (AdicCompletion I A))
    [Module.Finite (AdicCompletion I A) M']
    (φ : M' →ₗ[AdicCompletion I A] TensorProduct A (AdicCompletion I A) N)
    (hK : IsIPowerTorsion (AdicCompletion I A) (LinearMap.ker φ)
      (I.map (algebraMap A (AdicCompletion I A))))
    (hC : IsIPowerTorsion (AdicCompletion I A)
      (TensorProduct A (AdicCompletion I A) N ⧸ LinearMap.range φ)
      (I.map (algebraMap A (AdicCompletion I A)))) :
    ∃ (M : ModuleCat.{max u v} A) (ψ : M →ₗ[A] N)
      (e : TensorProduct A (AdicCompletion I A) M ≃ₗ[AdicCompletion I A] M'),
      Module.Finite A M ∧ IsIPowerTorsion A (LinearMap.ker ψ) I ∧
        IsIPowerTorsion A (N ⧸ LinearMap.range ψ) I ∧
        φ.comp e.toLinearMap = LinearMap.baseChange (AdicCompletion I A) ψ := by
  set S := AdicCompletion I A
  let φ' : M' ⟶ (ModuleCat.extendScalars.{u, u, max u v} (algebraMap A S)).obj N :=
    ModuleCat.ofHom (X := M')
      (Y := (ModuleCat.extendScalars.{u, u, max u v} (algebraMap A S)).obj N)
      ((extendScalarsTensorEquiv.{u, u, max u v} (S := S) N).toLinearMap.comp φ)
  have hφ' : φ'.hom =
      (extendScalarsTensorEquiv.{u, u, max u v} (S := S) N).toLinearMap.comp φ := rfl
  have hker : LinearMap.ker φ'.hom = LinearMap.ker φ := by
    rw [hφ', LinearEquiv.ker_comp]
  have hrange : LinearMap.range φ'.hom =
      (LinearMap.range φ).map
        (extendScalarsTensorEquiv.{u, u, max u v} (S := S) N).toLinearMap := by
    rw [hφ', LinearMap.range_comp]
  have hK' : IsIPowerTorsion S (↥(kernel φ' : ModuleCat.{max u v} S))
      (I.map (algebraMap A S)) :=
    isIPowerTorsion_of_linearEquiv _ (ModuleCat.kernelIsoKer φ').toLinearEquiv.symm
      (by rw [hker]; exact hK)
  have hC' : IsIPowerTorsion S (↥(cokernel φ' : ModuleCat.{max u v} S))
      (I.map (algebraMap A S)) :=
    isIPowerTorsion_of_linearEquiv _ (ModuleCat.cokernelIsoRangeQuotient φ').toLinearEquiv.symm
      (isIPowerTorsion_of_linearEquiv _
        (Submodule.Quotient.equiv (LinearMap.range φ) (LinearMap.range φ'.hom)
          (extendScalarsTensorEquiv.{u, u, max u v} (S := S) N) hrange.symm) hC)
  obtain ⟨M, ψ', e', hM, hKψ, hCψ, he⟩ :=
    finite_formalGlueing_descent.{u, v} I I.fg_of_isNoetherianRing
      (AdicCompletion.flat_of_isNoetherian I)
      (AdicCompletion.quotientMap_bijective I I.fg_of_isNoetherianRing) N M' φ' hK' hC'
  refine ⟨M, ψ'.hom,
    (extendScalarsTensorEquiv.{u, u, max u v} (S := S) M).trans e'.toLinearEquiv,
    hM, ?_, ?_, ?_⟩
  · exact isIPowerTorsion_of_linearEquiv I (ModuleCat.kernelIsoKer ψ').toLinearEquiv hKψ
  · exact isIPowerTorsion_of_linearEquiv I
      (ModuleCat.cokernelIsoRangeQuotient ψ').toLinearEquiv hCψ
  · have key (x : TensorProduct A S M) :
        (extendScalarsTensorEquiv.{u, u, max u v} (S := S) N)
            (φ (e'.hom (extendScalarsTensorEquiv.{u, u, max u v} (S := S) M x))) =
          (extendScalarsTensorEquiv.{u, u, max u v} (S := S) N)
            (LinearMap.baseChange S ψ'.hom x) := by
      have h1 := congrArg
        (fun k : (ModuleCat.extendScalars.{u, u, max u v} (algebraMap A S)).obj M ⟶
          (ModuleCat.extendScalars.{u, u, max u v} (algebraMap A S)).obj N =>
            k (extendScalarsTensorEquiv.{u, u, max u v} (S := S) M x)) he
      exact h1.trans (extendScalarsTensorEquiv_map ψ' x)
    exact LinearMap.ext fun x =>
      (extendScalarsTensorEquiv.{u, u, max u v} (S := S) N).injective (key x)

/-- An `S`-linear equivalence out of `S ⊗[R] M` sends `1 ⊗ r • m` to `r • (1 ⊗ m)`. -/
private lemma tmul_one_smul_apply
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {M : Type w} [AddCommGroup M] [Module R M]
    {P : Type*} [AddCommGroup P] [Module S P]
    (f : TensorProduct R S M ≃ₗ[S] P) (r : R) (m : M) :
    f ((1 : S) ⊗ₜ[R] (r • m)) = algebraMap R S r • f ((1 : S) ⊗ₜ[R] m) := by
  rw [TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul S r, map_smul]

/-- If `φ ∘ e` is the base change of `ψ`, then `φ (e (1 ⊗ m)) = 1 ⊗ ψ m`. -/
private lemma descent_compat
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {M N : Type (max u v)} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {M' : Type (max u v)} [AddCommGroup M'] [Module (AdicCompletion I A) M']
    (φ : M' →ₗ[AdicCompletion I A] TensorProduct A (AdicCompletion I A) N)
    (ψ : M →ₗ[A] N)
    (e : TensorProduct A (AdicCompletion I A) M ≃ₗ[AdicCompletion I A] M')
    (he : φ.comp e.toLinearMap = LinearMap.baseChange (AdicCompletion I A) ψ) (m : M) :
    φ (e ((1 : AdicCompletion I A) ⊗ₜ[A] m)) = (1 : AdicCompletion I A) ⊗ₜ[A] ψ m := by
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul] using
    LinearMap.congr_fun he ((1 : AdicCompletion I A) ⊗ₜ[A] m)

/-- A descent `(M, ψ, e)` is determined by the images under `ψ` and `m ↦ e (1 ⊗ m)`. -/
private lemma descent_injective
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {M N : Type (max u v)} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {M' : Type (max u v)} [AddCommGroup M'] [Module (AdicCompletion I A) M']
    (ψ : M →ₗ[A] N) (φ : M' →ₗ[AdicCompletion I A] TensorProduct A (AdicCompletion I A) N)
    (e : TensorProduct A (AdicCompletion I A) M ≃ₗ[AdicCompletion I A] M')
    (he : φ.comp e.toLinearMap = LinearMap.baseChange (AdicCompletion I A) ψ)
    (hK : IsIPowerTorsion A (LinearMap.ker ψ) I)
    (hC : IsIPowerTorsion A (N ⧸ LinearMap.range ψ) I) (a b : M) (hψ : ψ a = ψ b)
    (hu : e ((1 : AdicCompletion I A) ⊗ₜ[A] a) = e ((1 : AdicCompletion I A) ⊗ₜ[A] b)) :
    a = b := by
  obtain ⟨c, -, huniq⟩ := AdicCompletion.existsUnique_of_descent.{u, v} I ψ φ e he hK hC (ψ b)
    (e ((1 : AdicCompletion I A) ⊗ₜ[A] b)) (descent_compat.{u, v} I φ ψ e he b)
  exact (huniq a ⟨hψ, hu⟩).trans (huniq b ⟨rfl, rfl⟩).symm

/-- Two descents of the same map `φ : M' → S ⊗_A N` along the
`I`-adic completion `S = A^∧` of a Noetherian ring `A` are related by a unique isomorphism
compatible with the maps to `N` and with the identifications of `M'`. -/
public theorem AdicCompletion.descent_unique
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {N : Type (max u v)} [AddCommGroup N] [Module A N]
    {M' : Type (max u v)} [AddCommGroup M'] [Module (AdicCompletion I A) M']
    (φ : M' →ₗ[AdicCompletion I A] TensorProduct A (AdicCompletion I A) N)
    {M₁ M₂ : Type (max u v)} [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
    (ψ₁ : M₁ →ₗ[A] N) (ψ₂ : M₂ →ₗ[A] N)
    (e₁ : TensorProduct A (AdicCompletion I A) M₁ ≃ₗ[AdicCompletion I A] M')
    (e₂ : TensorProduct A (AdicCompletion I A) M₂ ≃ₗ[AdicCompletion I A] M')
    (he₁ : φ.comp e₁.toLinearMap = LinearMap.baseChange (AdicCompletion I A) ψ₁)
    (he₂ : φ.comp e₂.toLinearMap = LinearMap.baseChange (AdicCompletion I A) ψ₂)
    (hK₁ : IsIPowerTorsion A (LinearMap.ker ψ₁) I)
    (hC₁ : IsIPowerTorsion A (N ⧸ LinearMap.range ψ₁) I)
    (hK₂ : IsIPowerTorsion A (LinearMap.ker ψ₂) I)
    (hC₂ : IsIPowerTorsion A (N ⧸ LinearMap.range ψ₂) I) :
    ∃! d : M₁ ≃ₗ[A] M₂,
      ψ₂.comp d.toLinearMap = ψ₁ ∧
        e₂.toLinearMap.comp (LinearMap.baseChange (AdicCompletion I A) d.toLinearMap) =
          e₁.toLinearMap := by
  set S := AdicCompletion I A
  have key₁ := AdicCompletion.existsUnique_of_descent.{u, v} I ψ₁ φ e₁ he₁ hK₁ hC₁
  have key₂ := AdicCompletion.existsUnique_of_descent.{u, v} I ψ₂ φ e₂ he₂ hK₂ hC₂
  have hinj₁ := descent_injective.{u, v} I ψ₁ φ e₁ he₁ hK₁ hC₁
  have hinj₂ := descent_injective.{u, v} I ψ₂ φ e₂ he₂ hK₂ hC₂
  choose g₁ hg₁ using fun m : M₁ =>
    (key₂ (ψ₁ m) (e₁ ((1 : S) ⊗ₜ[A] m)) (descent_compat I φ ψ₁ e₁ he₁ m)).exists
  choose g₂ hg₂ using fun m : M₂ =>
    (key₁ (ψ₂ m) (e₂ ((1 : S) ⊗ₜ[A] m)) (descent_compat I φ ψ₂ e₂ he₂ m)).exists
  let d₀ : M₁ →ₗ[A] M₂ :=
    { toFun := g₁
      map_add' := fun a b => hinj₂ _ _
        (by rw [(hg₁ (a + b)).1]; simp only [map_add, (hg₁ a).1, (hg₁ b).1])
        (by simp only [(hg₁ (a + b)).2, TensorProduct.tmul_add, map_add, (hg₁ a).2, (hg₁ b).2])
      map_smul' := fun r a => hinj₂ _ _
        (by simp only [RingHom.id_apply, (hg₁ (r • a)).1, map_smul, (hg₁ a).1])
        (by rw [(hg₁ (r • a)).2, tmul_one_smul_apply e₁, tmul_one_smul_apply e₂, (hg₁ a).2,
          RingHom.id_apply]) }
  have hleft (m : M₁) : g₂ (g₁ m) = m :=
    hinj₁ _ _ (by rw [(hg₂ (g₁ m)).1, (hg₁ m).1]) (by rw [(hg₂ (g₁ m)).2, (hg₁ m).2])
  have hright (m : M₂) : g₁ (g₂ m) = m :=
    hinj₂ _ _ (by rw [(hg₁ (g₂ m)).1, (hg₂ m).1]) (by rw [(hg₁ (g₂ m)).2, (hg₂ m).2])
  let d : M₁ ≃ₗ[A] M₂ := { d₀ with invFun := g₂, left_inv := hleft, right_inv := hright }
  have hdψ (m : M₁) : ψ₂ (d m) = ψ₁ m := (hg₁ m).1
  have hdu (m : M₁) : e₂ ((1 : S) ⊗ₜ[A] d m) = e₁ ((1 : S) ⊗ₜ[A] m) := (hg₁ m).2
  have htensor (f : M₁ →ₗ[A] M₂) (hf : ∀ m, e₂ ((1 : S) ⊗ₜ[A] f m) = e₁ ((1 : S) ⊗ₜ[A] m)) :
      e₂.toLinearMap.comp (LinearMap.baseChange S f) = e₁.toLinearMap := by
    refine tensor_linearMap_ext _ _ fun m => ?_
    show e₂ (LinearMap.baseChange S f ((1 : S) ⊗ₜ[A] m)) = e₁ ((1 : S) ⊗ₜ[A] m)
    rw [LinearMap.baseChange_tmul]
    exact hf m
  refine ⟨d, ⟨LinearMap.ext hdψ, htensor d.toLinearMap hdu⟩, fun d' hd' => ?_⟩
  refine LinearEquiv.ext fun m => hinj₂ _ _ ?_ ?_
  · exact (LinearMap.congr_fun hd'.1 m).trans (hdψ m).symm
  · have h := LinearMap.congr_fun hd'.2 ((1 : S) ⊗ₜ[A] m)
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe] at h
    exact h.trans (hdu m).symm

end
