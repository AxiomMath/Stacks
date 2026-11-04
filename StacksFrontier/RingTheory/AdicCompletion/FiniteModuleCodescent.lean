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
# Algebraizing a map out of an adic completion

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `A^∧` the `I`-adic completion of `A`. Write
`J = I A^∧`. Given a finite `A`-module `N`, a finite `A^∧`-module `M'` and an `A^∧`-linear map
`φ : A^∧ ⊗_A N → M'` whose kernel and cokernel are `J`-power torsion, the map `φ` is the
completion of a map of finite `A`-modules in the direction *out of* `N`: there are a finite
`A`-module `M`, an `A`-linear map `ψ : N → M` with `I`-power torsion kernel and cokernel, and an
`A^∧`-linear isomorphism `e : A^∧ ⊗_A M ≅ M'` with `e ∘ (ψ ⊗ 1) = φ`. The triple `(M, ψ, e)` is
unique up to a unique isomorphism.

The construction rests on formal glueing. Completion is flat over a Noetherian ring and induces an
isomorphism `A / I ≅ A^∧ / J`, so a map whose kernel and cokernel are power torsion descends; the
descent replaces the *target* of a map out of an extended module, which is the direction dual to
the one that replaces the source. Finiteness of the descended module runs along the cokernel
rather than the kernel: the cokernel of `φ` is finite over `A^∧` and annihilated by a power `J^n`,
and `A^∧ / J^n` is a finite `A`-module because `A → A^∧` is surjective modulo every power of `I`,
so the cokernel of `ψ` is already finite over `A`; since `N` is finite, so is `M`.

Uniqueness is the statement that the canonical glueing functor is fully faithful. A map `ψ` with
`I`-power torsion kernel and cokernel becomes an isomorphism after inverting any element of `I`,
so two codescents `ψ₁ : N → M₁` and `ψ₂ : N → M₂` of the same `φ` are compared by the glueing
datum whose generic component is the isomorphism `A^∧ ⊗_A M₁ ≅ M' ≅ A^∧ ⊗_A M₂` and whose local
component at a generator `f` of `I` is `(ψ₂)_f ∘ (ψ₁)_f⁻¹`. Full faithfulness turns that datum
into a unique isomorphism `M₁ ≅ M₂` compatible with the maps out of `N` and with the
identifications of `M'`.

## Main results

* `AdicCompletion.exists_finite_codescent_of_isIPowerTorsion`: existence of the codescent
  `(M, ψ, e)`, with `M` finite over `A` and with `I`-power torsion kernel and cokernel for `ψ`.
* `AdicCompletion.codescent_unique`: two codescents of the same `φ` are related by a unique
  isomorphism compatible with the maps out of `N` and with the identifications of `M'`.
* `bijective_isLocalizedModule_map_of_isIPowerTorsion`: the step the uniqueness argument runs on,
  stated for an arbitrary localization rather than for `LocalizedModule` — a map with `I`-power
  torsion kernel and cokernel is bijective after inverting an element of `I`.

## Implementation notes

Extension of scalars appears in two shapes. The formal glueing descent statement is phrased with
`ModuleCat.extendScalars`, whose underlying type is a tensor product formed with the `A`-module
structure on `A^∧` obtained by restricting scalars along the ring map, while the statements below
use the plain tensor product `TensorProduct A (AdicCompletion I A) M` formed with the `Algebra`
instance. The two are identified by a linear equivalence which is the only place the distinction
has to be handled. The glueing *category*, by contrast, has the plain tensor product as its
generic component, so the comparison of two codescents needs no such bridge.

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

/-! ### Transport of ideal-power torsion -/

/-- Precomposing with a linear equivalence does not change the power-torsion property of the
kernel. -/
private theorem isIPowerTorsion_ker_comp_equiv
    {R : Type u} [CommRing R] {M N P : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (I : Ideal R) (e : M ≃ₗ[R] N) (g : N →ₗ[R] P)
    (hg : IsIPowerTorsion R (LinearMap.ker g) I) :
    IsIPowerTorsion R (LinearMap.ker (g.comp e.toLinearMap)) I := by
  intro x
  have hx : e x.1 ∈ LinearMap.ker g := x.2
  obtain ⟨n, hn, hkill⟩ := hg ⟨e x.1, hx⟩
  refine ⟨n, hn, fun a ha => ?_⟩
  apply Subtype.ext
  apply e.injective
  have h0 : a • e x.1 = 0 := congrArg Subtype.val (hkill a ha)
  simpa using h0

/-! ### Finiteness of the codescended module -/

/-- A module receiving a map from a finite module is finite once the cokernel of that map is
finite. -/
private theorem finite_of_finite_source_of_finite_cokernel
    {R : Type u} [CommRing R] {M N : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M]
    (f : M →ₗ[R] N) [Module.Finite R (N ⧸ LinearMap.range f)] :
    Module.Finite R N := by
  have : Module.Finite R (LinearMap.range f) :=
    Module.Finite.of_surjective f.rangeRestrict f.surjective_rangeRestrict
  exact Module.Finite.of_submodule_quotient (LinearMap.range f)

/-- Finiteness of the codescended module follows from finiteness of the restricted cokernel
supplied by formal glueing. -/
private theorem finite_codescended_module_of_finite_restricted_cokernel
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (a : R →+* S)
    (M N : ModuleCat.{w} R) [Module.Finite R M]
    (M' N' : ModuleCat.{w} S) (φ : M' ⟶ N') (ψ : M ⟶ N)
    (eC : (ModuleCat.restrictScalars.{w} a).obj (cokernel φ) ≅ cokernel ψ)
    [Module.Finite R ((ModuleCat.restrictScalars.{w} a).obj (cokernel φ))] :
    Module.Finite R N := by
  let : Module.Finite R ((cokernel ψ : ModuleCat R) : Type _) :=
    Module.Finite.equiv eC.toLinearEquiv
  let : Module.Finite R (N ⧸ LinearMap.range ψ.hom) :=
    Module.Finite.equiv (ModuleCat.cokernelIsoRangeQuotient ψ).toLinearEquiv
  exact finite_of_finite_source_of_finite_cokernel ψ.hom

/-! ### Codescent along a flat map which is an isomorphism modulo `I` -/

/-- Formal glueing codescent of a map out of a finite module, with finiteness of the codescended
module and power torsion of the kernel and cokernel of the codescended map. -/
private theorem finite_formalGlueing_codescent
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (I : Ideal R) (hI : I.FG) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (N : ModuleCat.{max u v} R) (M' : ModuleCat.{max u v} S)
    [Module.Finite R N] [Module.Finite S M']
    (φ : (ModuleCat.extendScalars.{u, u, max u v} (algebraMap R S)).obj N ⟶ M')
    (hK : IsIPowerTorsion S (↥(kernel φ : ModuleCat.{max u v} S)) (I.map (algebraMap R S)))
    (hC : IsIPowerTorsion S (↥(cokernel φ : ModuleCat.{max u v} S)) (I.map (algebraMap R S))) :
    ∃ (M : ModuleCat.{max u v} R) (ψ : N ⟶ M)
      (e : (ModuleCat.extendScalars.{u, u, max u v} (algebraMap R S)).obj M ≅ M'),
      Module.Finite R M ∧
        IsIPowerTorsion R (↥(kernel ψ : ModuleCat.{max u v} R)) I ∧
        IsIPowerTorsion R (↥(cokernel ψ : ModuleCat.{max u v} R)) I ∧
        (ModuleCat.extendScalars.{u, u, max u v} (algebraMap R S)).map ψ ≫ e.hom = φ := by
  obtain ⟨M, ψ, e, eK, eC, he⟩ :=
    (FormalGlueing.exists_descent_of_idealPowerTorsion_kernel_cokernel.{u, u, v}
      R S I hI hflat hq).2 N M' φ hK hC
  let J := I.map (algebraMap R S)
  have : Module.Finite S (M' ⧸ LinearMap.range φ.hom) := Module.Finite.quotient S _
  have : Module.Finite S (cokernel φ : ModuleCat.{max u v} S) :=
    Module.Finite.equiv (ModuleCat.cokernelIsoRangeQuotient φ).toLinearEquiv.symm
  obtain ⟨n, hn⟩ := ideal_smul_eq_bot_of_finite_power_torsion J (hI.map (algebraMap R S))
    (cokernel φ : ModuleCat.{max u v} S) hC
  have : Module.Finite R (S ⧸ J ^ n) := by
    have hfinite := finite_quotient_of_quotientMap_surjective (I ^ n)
      (quotientMap_pow_surjective_of_flat I hflat hq n)
    rwa [Ideal.map_pow] at hfinite
  have : Module.Finite R
      ((ModuleCat.restrictScalars.{max u v} (algebraMap R S)).obj (cokernel φ)) :=
    finite_restrictScalars_of_annihilated (M := (cokernel φ : ModuleCat.{max u v} S)) (J ^ n) hn
  have hM : Module.Finite R M :=
    finite_codescended_module_of_finite_restricted_cokernel (algebraMap R S) N M
      ((ModuleCat.extendScalars.{u, u, max u v} (algebraMap R S)).obj N) M' φ ψ eC
  have hT := map_kernel_cokernel_isIPowerTorsion I φ ψ eK eC hK hC
  exact ⟨M, ψ, e, hM, hT.1, hT.2, he⟩

/-! ### Codescent along the adic completion -/

/-- **Stacks 0889** (existence, the direction out of the completion). Let `A` be a Noetherian
ring, `I ⊆ A` an ideal and `S = A^∧` its `I`-adic completion. Let `N` be a finite `A`-module,
`M'` a finite `S`-module, and `φ : S ⊗_A N → M'` an `S`-linear map whose kernel and cokernel are
`IS`-power torsion. Then there are a finite `A`-module `M`, an `A`-linear map `ψ : N → M` with
`I`-power torsion kernel and cokernel, and an `S`-linear isomorphism `e : S ⊗_A M ≅ M'` with
`e ∘ (ψ ⊗ 1) = φ`. -/
public theorem AdicCompletion.exists_finite_codescent_of_isIPowerTorsion
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (N : ModuleCat.{max u v} A) [Module.Finite A N]
    (M' : ModuleCat.{max u v} (AdicCompletion I A))
    [Module.Finite (AdicCompletion I A) M']
    (φ : TensorProduct A (AdicCompletion I A) N →ₗ[AdicCompletion I A] M')
    (hK : IsIPowerTorsion (AdicCompletion I A) (LinearMap.ker φ)
      (I.map (algebraMap A (AdicCompletion I A))))
    (hC : IsIPowerTorsion (AdicCompletion I A) (M' ⧸ LinearMap.range φ)
      (I.map (algebraMap A (AdicCompletion I A)))) :
    ∃ (M : ModuleCat.{max u v} A) (ψ : N →ₗ[A] M)
      (e : TensorProduct A (AdicCompletion I A) M ≃ₗ[AdicCompletion I A] M'),
      Module.Finite A M ∧ IsIPowerTorsion A (LinearMap.ker ψ) I ∧
        IsIPowerTorsion A (M ⧸ LinearMap.range ψ) I ∧
        e.toLinearMap.comp (LinearMap.baseChange (AdicCompletion I A) ψ) = φ := by
  set S := AdicCompletion I A with hS
  let φ' : (ModuleCat.extendScalars.{u, u, max u v} (algebraMap A S)).obj N ⟶ M' :=
    ModuleCat.ofHom (X := (ModuleCat.extendScalars.{u, u, max u v} (algebraMap A S)).obj N)
      (Y := M')
      (φ.comp (extendScalarsTensorEquiv.{u, u, max u v} (S := S) N).symm.toLinearMap)
  have hφ' : φ'.hom =
      φ.comp (extendScalarsTensorEquiv.{u, u, max u v} (S := S) N).symm.toLinearMap := rfl
  have hrange : LinearMap.range φ'.hom = LinearMap.range φ := by
    rw [hφ']
    exact LinearEquiv.range_comp _ _
  have hK' : IsIPowerTorsion S (↥(kernel φ' : ModuleCat.{max u v} S))
      (I.map (algebraMap A S)) :=
    isIPowerTorsion_of_linearEquiv _ (ModuleCat.kernelIsoKer φ').toLinearEquiv.symm
      (by rw [hφ']; exact isIPowerTorsion_ker_comp_equiv _ _ _ hK)
  have hC' : IsIPowerTorsion S (↥(cokernel φ' : ModuleCat.{max u v} S))
      (I.map (algebraMap A S)) :=
    isIPowerTorsion_of_linearEquiv _ (ModuleCat.cokernelIsoRangeQuotient φ').toLinearEquiv.symm
      (by rw [hrange]; exact hC)
  obtain ⟨M, ψ', e', hM, hKψ, hCψ, he⟩ :=
    finite_formalGlueing_codescent.{u, v} I I.fg_of_isNoetherianRing
      (AdicCompletion.flat_of_isNoetherian I)
      (AdicCompletion.quotientMap_bijective I I.fg_of_isNoetherianRing) N M' φ' hK' hC'
  refine ⟨M, ψ'.hom,
    (extendScalarsTensorEquiv.{u, u, max u v} (S := S) M).trans e'.toLinearEquiv,
    hM, ?_, ?_, ?_⟩
  · exact isIPowerTorsion_of_linearEquiv I (ModuleCat.kernelIsoKer ψ').toLinearEquiv hKψ
  · exact isIPowerTorsion_of_linearEquiv I
      (ModuleCat.cokernelIsoRangeQuotient ψ').toLinearEquiv hCψ
  · refine LinearMap.ext fun x => ?_
    have h1 := congrArg
      (fun k : (ModuleCat.extendScalars.{u, u, max u v} (algebraMap A S)).obj N ⟶ M' =>
          k (extendScalarsTensorEquiv.{u, u, max u v} (S := S) N x)) he
    have h2 : e'.hom ((ModuleCat.extendScalars.{u, u, max u v} (algebraMap A S)).map ψ'
          (extendScalarsTensorEquiv.{u, u, max u v} (S := S) N x)) =
        φ ((extendScalarsTensorEquiv.{u, u, max u v} (S := S) N).symm
          (extendScalarsTensorEquiv.{u, u, max u v} (S := S) N x)) := h1
    rw [LinearEquiv.symm_apply_apply, extendScalarsTensorEquiv_map] at h2
    exact h2

/-! ### Comparing two codescents -/

/-- Two linear maps out of `N` agree once they agree after composing with a map `g : M → N` whose
cokernel is annihilated by powers of a single element `a`, provided the powers of `a` act
injectively on the target. -/
private theorem eq_of_comp_eq_of_pow_smul_mem_range
    {A : Type*} [CommRing A] {M N P : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module A M] [Module A N] [Module A P]
    (g : M →ₗ[A] N) (a : A)
    (hrange : ∀ y : N, ∃ (n : ℕ) (x : M), g x = a ^ n • y)
    (hinj : ∀ n : ℕ, Function.Injective fun x : P => a ^ n • x)
    (h k : N →ₗ[A] P) (he : h.comp g = k.comp g) : h = k := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨n, x, hx⟩ := hrange y
  refine hinj n ?_
  show a ^ n • h y = a ^ n • k y
  rw [← map_smul, ← map_smul, ← hx]
  exact LinearMap.congr_fun he x

/-- If the cokernel of `g` is `I`-power torsion, some power of any `a ∈ I` times `m` is in the
range of `g`. -/
private theorem exists_pow_smul_mem_range_of_isIPowerTorsion
    {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module A M]
    [Module A N] (I : Ideal A) (g : M →ₗ[A] N) (hC : IsIPowerTorsion A (N ⧸ LinearMap.range g) I)
    (a : A) (ha : a ∈ I) (m : N) : ∃ n : ℕ, a ^ n • m ∈ LinearMap.range g := by
  obtain ⟨n, -, h⟩ := hC ((LinearMap.range g).mkQ m)
  refine ⟨n, (Submodule.Quotient.mk_eq_zero _).1 ?_⟩
  simpa using h (a ^ n) (Ideal.pow_mem_pow ha n)

/-- A map with `I`-power torsion kernel and cokernel becomes bijective after inverting an element
of `I`. -/
private theorem localizedMap_bijective_of_isIPowerTorsion
    {A : Type u} [CommRing A] {M N : Type v}
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    (I : Ideal A) (g : M →ₗ[A] N)
    (hK : IsIPowerTorsion A (LinearMap.ker g) I)
    (hC : IsIPowerTorsion A (N ⧸ LinearMap.range g) I)
    (a : A) (ha : a ∈ I) :
    Function.Bijective (LocalizedModule.map (Submonoid.powers a) g) := by
  let T := Submonoid.powers a
  constructor
  · apply IsLocalizedModule.injective_of_map_zero T (LocalizedModule.mkLinearMap T M)
    intro m hm
    change LocalizedModule.map T g (LocalizedModule.mk m 1) = 0 at hm
    rw [LocalizedModule.map_mk] at hm
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff T
      (LocalizedModule.mkLinearMap T N)).1 hm
    have hg : g ((t : A) • m) = 0 := by simpa only [map_smul, Submonoid.smul_def] using ht
    obtain ⟨n, hn, h⟩ := hK ⟨(t : A) • m, hg⟩
    apply (IsLocalizedModule.eq_zero_iff T (LocalizedModule.mkLinearMap T M)).2
    refine ⟨⟨a ^ n, ⟨n, rfl⟩⟩ * t, ?_⟩
    have hh : a ^ n • ((t : A) • m) = 0 :=
      congrArg (fun z : LinearMap.ker g => (z : M)) (h (a ^ n) (Ideal.pow_mem_pow ha n))
    simpa only [Submonoid.smul_def, Submonoid.coe_mul, mul_smul] using hh
  · intro x
    induction x using LocalizedModule.induction_on with
    | h m s =>
      obtain ⟨n, y, hy⟩ := exists_pow_smul_mem_range_of_isIPowerTorsion I g hC a ha m
      let t : T := ⟨a ^ n, ⟨n, rfl⟩⟩
      refine ⟨LocalizedModule.mk y (t * s), ?_⟩
      rw [LocalizedModule.map_mk, hy]
      exact LocalizedModule.mk_cancel_common_left t s m

/-- **A map with `I`-power torsion kernel and cokernel becomes bijective after inverting an
element of `I`**, read in an arbitrary pair of localizations at the powers of that element.

This is `localizedMap_bijective_of_isIPowerTorsion` with the concrete `LocalizedModule` replaced
by any two modules presented as localizations; that statement is the case
`lM = LocalizedModule.mkLinearMap`, `lN = LocalizedModule.mkLinearMap`. The two localized maps
are conjugate by `IsLocalizedModule.iso`, because both become `lN ∘ g` after precomposition with
the localization map, and `IsLocalizedModule.linearMap_ext` says a map out of a localization is
determined by that composite. -/
public theorem bijective_isLocalizedModule_map_of_isIPowerTorsion
    {A : Type u} [CommRing A] {M N M' N' : Type v}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
    [Module A M] [Module A N] [Module A M'] [Module A N']
    (I : Ideal A) (g : M →ₗ[A] N) (lM : M →ₗ[A] M') (lN : N →ₗ[A] N') {a : A}
    [IsLocalizedModule (Submonoid.powers a) lM] [IsLocalizedModule (Submonoid.powers a) lN]
    (hK : IsIPowerTorsion A (LinearMap.ker g) I)
    (hC : IsIPowerTorsion A (N ⧸ LinearMap.range g) I) (ha : a ∈ I) :
    Function.Bijective (IsLocalizedModule.map (Submonoid.powers a) lM lN g) := by
  set T := Submonoid.powers a with hT
  have hb : Function.Bijective (LocalizedModule.map T g) :=
    localizedMap_bijective_of_isIPowerTorsion I g hK hC a ha
  have key : (IsLocalizedModule.map T lM lN g) ∘ₗ (IsLocalizedModule.iso T lM).toLinearMap =
      (IsLocalizedModule.iso T lN).toLinearMap ∘ₗ
        (LocalizedModule.map T g).restrictScalars A := by
    refine IsLocalizedModule.linearMap_ext T (LocalizedModule.mkLinearMap T M) lN ?_
    refine LinearMap.ext fun m => ?_
    simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply,
      LinearEquiv.coe_coe, IsLocalizedModule.iso_mk_one, IsLocalizedModule.map_apply,
      LinearMap.coe_restrictScalars, LocalizedModule.map_mk]
  have hmap : ∀ x : LocalizedModule T M,
      IsLocalizedModule.map T lM lN g (IsLocalizedModule.iso T lM x) =
        IsLocalizedModule.iso T lN (LocalizedModule.map T g x) :=
    fun x => LinearMap.congr_fun key x
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · have h := hb.1 (a₁ := (IsLocalizedModule.iso T lM).symm x)
      (a₂ := (IsLocalizedModule.iso T lM).symm y) ((IsLocalizedModule.iso T lN).injective
        (by rw [← hmap, ← hmap, LinearEquiv.apply_symm_apply,
          LinearEquiv.apply_symm_apply, hxy]))
    simpa using congrArg (IsLocalizedModule.iso T lM) h
  · obtain ⟨w, hw⟩ := hb.2 ((IsLocalizedModule.iso T lN).symm z)
    exact ⟨IsLocalizedModule.iso T lM w, by rw [hmap, hw, LinearEquiv.apply_symm_apply]⟩

section Comparison

open FormalGlueing

variable {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
  {r : ℕ} (f : Fin r → R)

/-- The generic/local comparison of a canonical glueing datum, evaluated on a fraction with
denominator one. -/
private lemma canonicalAlpha_mkLinearMap (M : ModuleCat.{max u v} R) (i : Fin r)
    (x : TensorProduct R S M) :
    canonicalAlpha S f M i
        (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S (f i))) _ x) =
      AlgebraTensorModule.lTensor S S (canonicalLocalMk f M i) x :=
  IsLocalizedModule.iso_mk_one _ _ _

/-- Localization of a composite of linear maps, applied to an element. -/
private lemma localizedMap_apply_comp {P₁ P₂ P₃ : Type*}
    [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂]
    [AddCommGroup P₃] [Module R P₃]
    (s : Finset (Fin r)) (b : P₁ →ₗ[R] P₂) (a : P₂ →ₗ[R] P₃) (X : Cech.cechMod f P₁ s) :
    localizedMap f s (a.comp b) X = localizedMap f s a (localizedMap f s b X) := by
  induction X using LocalizedModule.induction_on with
  | h y t => simp

variable {N M₁ M₂ : ModuleCat.{max u v} R} (ψ₁ : N ⟶ M₁) (ψ₂ : N ⟶ M₂)
  (hψ₁ : ∀ i, Function.Bijective (canonicalLocalMap f ψ₁ i).hom)

/-- The local component at `fᵢ` of the comparison between two codescents: the composite
`(ψ₂)_{fᵢ} ∘ (ψ₁)_{fᵢ}⁻¹`. -/
private noncomputable def localComparison (i : Fin r) :
    canonicalLocalPiece f M₁ i ⟶ canonicalLocalPiece f M₂ i :=
  ModuleCat.ofHom ((canonicalLocalMap f ψ₂ i).hom.comp
    (LinearEquiv.ofBijective (canonicalLocalMap f ψ₁ i).hom (hψ₁ i)).symm.toLinearMap)

/-- The local component of a canonical glueing datum is functorial. -/
private lemma canonicalLocalMap_comp_apply {P₁ P₂ P₃ : ModuleCat.{max u v} R}
    (a : P₁ ⟶ P₂) (b : P₂ ⟶ P₃) (i : Fin r) (z : canonicalLocalPiece f P₁ i) :
    canonicalLocalMap f b i (canonicalLocalMap f a i z) = canonicalLocalMap f (a ≫ b) i z := by
  induction z using LocalizedModule.induction_on with
  | h y t =>
    show LocalizedModule.map _ b.hom (LocalizedModule.map _ a.hom (LocalizedModule.mk y t)) =
      LocalizedModule.map _ (a ≫ b).hom (LocalizedModule.mk y t)
    rw [LocalizedModule.map_mk, LocalizedModule.map_mk, LocalizedModule.map_mk]
    rfl

private lemma localComparison_apply (i : Fin r) (m : canonicalLocalPiece f N i) :
    localComparison f ψ₁ ψ₂ hψ₁ i (canonicalLocalMap f ψ₁ i m) =
      canonicalLocalMap f ψ₂ i m := by
  show (canonicalLocalMap f ψ₂ i).hom
      ((LinearEquiv.ofBijective (canonicalLocalMap f ψ₁ i).hom (hψ₁ i)).symm
        ((LinearEquiv.ofBijective (canonicalLocalMap f ψ₁ i).hom (hψ₁ i)) m)) =
    canonicalLocalMap f ψ₂ i m
  rw [LinearEquiv.symm_apply_apply]

/-- The morphism of canonical glueing data comparing two codescents of the same map. -/
private noncomputable def canonicalComparisonMap
    (hrange : ∀ (i : Fin r) (y : TensorProduct R S M₁), ∃ (n : ℕ) (w : TensorProduct R S N),
      LinearMap.baseChange S ψ₁.hom w = f i ^ n • y)
    (gen : ModuleCat.of S (TensorProduct R S M₁) ⟶ ModuleCat.of S (TensorProduct R S M₂))
    (hgen : ∀ x : TensorProduct R S N,
      gen (LinearMap.baseChange S ψ₁.hom x) = LinearMap.baseChange S ψ₂.hom x) :
    ModuleGlueingMap S f (localizationComparisons f)
      (canonicalDatum.{u, u, v} S f M₁) (canonicalDatum.{u, u, v} S f M₂) where
  generic := gen
  localPiece i := localComparison f ψ₁ ψ₂ hψ₁ i
  alpha_compatibility i m := by
    have hinj : ∀ n : ℕ, Function.Injective fun x :
        TensorProduct R S (restrictFromAway f i (canonicalLocalPiece f M₂ i)) =>
          f i ^ n • x := by
      intro n
      have H : IsLocalizedModule (Submonoid.powers (f i))
          ((AlgebraTensorModule.lTensor S S (canonicalLocalMk f M₂ i)).restrictScalars R) :=
        isLocalized_lTensor S _ _
      have hu := H.map_units ⟨f i ^ n, ⟨n, rfl⟩⟩
      rw [Module.End.isUnit_iff] at hu
      exact hu.1
    have key :
        ((AlgebraTensorModule.lTensor S S (canonicalLocalMk f M₂ i)).comp
            gen.hom).restrictScalars R =
          (TensorProduct.map LinearMap.id
            (((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map
              (localComparison f ψ₁ ψ₂ hψ₁ i)).hom)).comp
            ((AlgebraTensorModule.lTensor S S (canonicalLocalMk f M₁ i)).restrictScalars R) := by
      refine eq_of_comp_eq_of_pow_smul_mem_range
        ((LinearMap.baseChange S ψ₁.hom).restrictScalars R) (f i) (hrange i) hinj _ _ ?_
      refine LinearMap.ext fun x => ?_
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul s n =>
        change AlgebraTensorModule.lTensor S S (canonicalLocalMk f M₂ i)
            (gen (LinearMap.baseChange S ψ₁.hom (s ⊗ₜ[R] n))) =
          TensorProduct.map LinearMap.id _
            (AlgebraTensorModule.lTensor S S (canonicalLocalMk f M₁ i)
              (LinearMap.baseChange S ψ₁.hom (s ⊗ₜ[R] n)))
        rw [hgen]
        change AlgebraTensorModule.lTensor S S (canonicalLocalMk f M₂ i) (s ⊗ₜ[R] ψ₂ n) =
          TensorProduct.map LinearMap.id _
            (AlgebraTensorModule.lTensor S S (canonicalLocalMk f M₁ i) (s ⊗ₜ[R] ψ₁ n))
        rw [AlgebraTensorModule.lTensor_tmul, AlgebraTensorModule.lTensor_tmul,
          TensorProduct.map_tmul]
        refine congrArg (TensorProduct.mk R S _ s) ?_
        rw [← canonicalLocalMap_mk f ψ₁ i n, ← canonicalLocalMap_mk f ψ₂ i n]
        exact (localComparison_apply f ψ₁ ψ₂ hψ₁ i
          (canonicalLocalMk f N i n)).symm
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    calc canonicalAlpha S f M₂ i
            (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S (f i))) _ (gen m))
        = AlgebraTensorModule.lTensor S S (canonicalLocalMk f M₂ i) (gen m) :=
          canonicalAlpha_mkLinearMap f M₂ i (gen m)
      _ = TensorProduct.map LinearMap.id
            (((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map
              (localComparison f ψ₁ ψ₂ hψ₁ i)).hom)
            (AlgebraTensorModule.lTensor S S (canonicalLocalMk f M₁ i) m) :=
          LinearMap.congr_fun key m
      _ = TensorProduct.map LinearMap.id
            (((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map
              (localComparison f ψ₁ ψ₂ hψ₁ i)).hom)
            (canonicalAlpha S f M₁ i
              (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S (f i))) _ m)) :=
          congrArg _ (canonicalAlpha_mkLinearMap f M₁ i m).symm
  alphaIJ_compatibility i j m := by
    obtain ⟨m', rfl⟩ := (hψ₁ i).2 m
    have h₁ := (canonicalDatumMap S f ψ₁).alphaIJ_compatibility i j m'
    have h₂ := (canonicalDatumMap S f ψ₂).alphaIJ_compatibility i j m'
    have hmaps : (((ModuleCat.restrictScalars
          (algebraMap R (Localization.Away (f j)))).map
            (localComparison f ψ₁ ψ₂ hψ₁ j)).hom).comp
        (((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f j)))).map
          ((canonicalDatumMap S f ψ₁).localPiece j)).hom) =
        ((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f j)))).map
          ((canonicalDatumMap S f ψ₂).localPiece j)).hom :=
      LinearMap.ext fun z => localComparison_apply f ψ₁ ψ₂ hψ₁ j z
    refine Eq.trans (congrArg (fun z => (canonicalDatum S f M₂).alphaIJ i j
        (LocalizedModule.mkLinearMap (Cech.cechSub f ({j} : Finset (Fin r))) _ z))
      (localComparison_apply f ψ₁ ψ₂ hψ₁ i m')) ?_
    refine Eq.trans h₂ (Eq.trans ?_ (congrArg (localizedMap f {i}
      (((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f j)))).map
        (localComparison f ψ₁ ψ₂ hψ₁ j)).hom)) h₁).symm)
    rw [← hmaps]
    exact localizedMap_apply_comp f {i} _ _ _

/-- The two comparison morphisms between the canonical data of two codescents are mutually
inverse on the local pieces. -/
private lemma localComparison_comp_symm
    (hψ₂ : ∀ i, Function.Bijective (canonicalLocalMap f ψ₂ i).hom) (i : Fin r) :
    localComparison f ψ₁ ψ₂ hψ₁ i ≫ localComparison f ψ₂ ψ₁ hψ₂ i = 𝟙 _ := by
  refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  obtain ⟨y, rfl⟩ := (hψ₁ i).2 z
  show localComparison f ψ₂ ψ₁ hψ₂ i
      (localComparison f ψ₁ ψ₂ hψ₁ i (canonicalLocalMap f ψ₁ i y)) = _
  rw [localComparison_apply, localComparison_apply]
  rfl

end Comparison

/-- A map whose cokernel is `I`-power torsion stays surjective up to a power of any element of `I`
after base change. -/
private lemma exists_baseChange_eq_pow_smul
    {A : Type*} [CommRing A] {S : Type*} [CommRing S] [Algebra A S]
    {N M : Type*} [AddCommGroup N] [Module A N] [AddCommGroup M] [Module A M]
    (I : Ideal A) (ψ : N →ₗ[A] M) (hC : IsIPowerTorsion A (M ⧸ LinearMap.range ψ) I)
    (a : A) (ha : a ∈ I) (y : TensorProduct A S M) :
    ∃ (n : ℕ) (w : TensorProduct A S N), LinearMap.baseChange S ψ w = a ^ n • y := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul s m =>
    obtain ⟨n, w, hw⟩ := exists_pow_smul_mem_range_of_isIPowerTorsion I ψ hC a ha m
    refine ⟨n, s ⊗ₜ[A] w, ?_⟩
    rw [LinearMap.baseChange_tmul, hw, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  | add y z hy hz =>
    obtain ⟨n, w, hw⟩ := hy
    obtain ⟨p, v, hv⟩ := hz
    refine ⟨n + p, a ^ p • w + a ^ n • v, ?_⟩
    rw [map_add, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, hw, hv,
      smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm p n, smul_add]

/-- The generic comparison `e₂⁻¹ ∘ e₁` of two codescents sends `ψ₁ x` to `ψ₂ x`. -/
private lemma symm_apply_eq_baseChange_of_comp_eq
    {A : Type*} [CommRing A] {S : Type*} [CommRing S] [Algebra A S]
    {N M₁ M₂ M' : Type*} [AddCommGroup N] [Module A N] [AddCommGroup M₁] [Module A M₁]
    [AddCommGroup M₂] [Module A M₂] [AddCommGroup M'] [Module S M']
    (φ : TensorProduct A S N →ₗ[S] M') (ψ₁ : N →ₗ[A] M₁) (ψ₂ : N →ₗ[A] M₂)
    (e₁ : TensorProduct A S M₁ ≃ₗ[S] M') (e₂ : TensorProduct A S M₂ ≃ₗ[S] M')
    (he₁ : e₁.toLinearMap.comp (LinearMap.baseChange S ψ₁) = φ)
    (he₂ : e₂.toLinearMap.comp (LinearMap.baseChange S ψ₂) = φ) (x : TensorProduct A S N) :
    e₂.symm (e₁ (LinearMap.baseChange S ψ₁ x)) = LinearMap.baseChange S ψ₂ x := by
  have h₁ : e₁ (LinearMap.baseChange S ψ₁ x) = φ x := LinearMap.congr_fun he₁ x
  rw [h₁, ← LinearMap.congr_fun he₂ x]
  simp

/-- **Stacks 0889** (uniqueness, the direction out of the completion). Two codescents of the same
map `φ : S ⊗_A N → M'` along the `I`-adic completion `S = A^∧` of a Noetherian ring `A` are
related by a unique isomorphism compatible with the maps out of `N` and with the identifications
of `M'`. -/
public theorem AdicCompletion.codescent_unique
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {N : Type (max u v)} [AddCommGroup N] [Module A N]
    {M' : Type (max u v)} [AddCommGroup M'] [Module (AdicCompletion I A) M']
    (φ : TensorProduct A (AdicCompletion I A) N →ₗ[AdicCompletion I A] M')
    {M₁ M₂ : Type (max u v)} [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
    (ψ₁ : N →ₗ[A] M₁) (ψ₂ : N →ₗ[A] M₂)
    (e₁ : TensorProduct A (AdicCompletion I A) M₁ ≃ₗ[AdicCompletion I A] M')
    (e₂ : TensorProduct A (AdicCompletion I A) M₂ ≃ₗ[AdicCompletion I A] M')
    (he₁ : e₁.toLinearMap.comp (LinearMap.baseChange (AdicCompletion I A) ψ₁) = φ)
    (he₂ : e₂.toLinearMap.comp (LinearMap.baseChange (AdicCompletion I A) ψ₂) = φ)
    (hK₁ : IsIPowerTorsion A (LinearMap.ker ψ₁) I)
    (hC₁ : IsIPowerTorsion A (M₁ ⧸ LinearMap.range ψ₁) I)
    (hK₂ : IsIPowerTorsion A (LinearMap.ker ψ₂) I)
    (hC₂ : IsIPowerTorsion A (M₂ ⧸ LinearMap.range ψ₂) I) :
    ∃! d : M₁ ≃ₗ[A] M₂,
      d.toLinearMap.comp ψ₁ = ψ₂ ∧
        e₂.toLinearMap.comp (LinearMap.baseChange (AdicCompletion I A) d.toLinearMap) =
          e₁.toLinearMap := by
  classical
  obtain ⟨r, f, hf⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp I.fg_of_isNoetherianRing
  change Ideal.span (Set.range f) = I at hf
  have hfmem (i : Fin r) : f i ∈ I := by
    rw [← hf]; exact Ideal.subset_span (Set.mem_range_self i)
  have hflat : Module.Flat A (AdicCompletion I A) := AdicCompletion.flat_of_isNoetherian I
  have hq : Function.Bijective
      (Ideal.quotientMap
        ((Ideal.span (Set.range f)).map (algebraMap A (AdicCompletion I A)))
        (algebraMap A (AdicCompletion I A)) Ideal.le_comap_map) := by
    rw [hf]
    exact AdicCompletion.quotientMap_bijective I I.fg_of_isNoetherianRing
  -- the formal glueing equivalence
  let := FormalGlueing.moduleGlueingCategory (AdicCompletion I A) f
    (FormalGlueing.localizationComparisons f)
  let F := FormalGlueing.canonicalFunctor.{u, u, v} (AdicCompletion I A) f
  obtain ⟨eqv, hfun, -⟩ :=
    FormalGlueing.canonicalFunctor_sections_areQuasiInverse.{u, u, v} A (AdicCompletion I A)
      f hflat hq
  change ModuleCat.{max u v} A ≌
    FormalGlueing.ModuleGlueingDatum.{u, u, v} (AdicCompletion I A) f
      (FormalGlueing.localizationComparisons f) at eqv
  change eqv.functor = F at hfun
  have : F.IsEquivalence := hfun ▸ (inferInstance : eqv.functor.IsEquivalence)
  -- the two codescents as maps in `ModuleCat A`
  let N' : ModuleCat.{max u v} A := ModuleCat.of A N
  let X₁ : ModuleCat.{max u v} A := ModuleCat.of A M₁
  let X₂ : ModuleCat.{max u v} A := ModuleCat.of A M₂
  let g₁ : N' ⟶ X₁ := ModuleCat.ofHom ψ₁
  let g₂ : N' ⟶ X₂ := ModuleCat.ofHom ψ₂
  have hψ₁loc : ∀ i, Function.Bijective (FormalGlueing.canonicalLocalMap f g₁ i).hom :=
    fun i => localizedMap_bijective_of_isIPowerTorsion I ψ₁ hK₁ hC₁ (f i) (hfmem i)
  have hψ₂loc : ∀ i, Function.Bijective (FormalGlueing.canonicalLocalMap f g₂ i).hom :=
    fun i => localizedMap_bijective_of_isIPowerTorsion I ψ₂ hK₂ hC₂ (f i) (hfmem i)
  have hrange₁ : ∀ (i : Fin r) (y : TensorProduct A (AdicCompletion I A) M₁),
      ∃ (n : ℕ) (w : TensorProduct A (AdicCompletion I A) N),
        LinearMap.baseChange (AdicCompletion I A) g₁.hom w = f i ^ n • y :=
    fun i y => exists_baseChange_eq_pow_smul I ψ₁ hC₁ (f i) (hfmem i) y
  have hrange₂ : ∀ (i : Fin r) (y : TensorProduct A (AdicCompletion I A) M₂),
      ∃ (n : ℕ) (w : TensorProduct A (AdicCompletion I A) N),
        LinearMap.baseChange (AdicCompletion I A) g₂.hom w = f i ^ n • y :=
    fun i y => exists_baseChange_eq_pow_smul I ψ₂ hC₂ (f i) (hfmem i) y
  -- the generic comparison in both directions
  let gen : ModuleCat.of (AdicCompletion I A) (TensorProduct A (AdicCompletion I A) M₁) ⟶
      ModuleCat.of (AdicCompletion I A) (TensorProduct A (AdicCompletion I A) M₂) :=
    ModuleCat.ofHom (e₂.symm.toLinearMap.comp e₁.toLinearMap)
  let gen' : ModuleCat.of (AdicCompletion I A) (TensorProduct A (AdicCompletion I A) M₂) ⟶
      ModuleCat.of (AdicCompletion I A) (TensorProduct A (AdicCompletion I A) M₁) :=
    ModuleCat.ofHom (e₁.symm.toLinearMap.comp e₂.toLinearMap)
  have hgen : ∀ x : TensorProduct A (AdicCompletion I A) N,
      gen (LinearMap.baseChange (AdicCompletion I A) g₁.hom x) =
        LinearMap.baseChange (AdicCompletion I A) g₂.hom x :=
    symm_apply_eq_baseChange_of_comp_eq φ ψ₁ ψ₂ e₁ e₂ he₁ he₂
  have hgen' : ∀ x : TensorProduct A (AdicCompletion I A) N,
      gen' (LinearMap.baseChange (AdicCompletion I A) g₂.hom x) =
        LinearMap.baseChange (AdicCompletion I A) g₁.hom x :=
    symm_apply_eq_baseChange_of_comp_eq φ ψ₂ ψ₁ e₂ e₁ he₂ he₁
  -- the comparison morphisms of glueing data
  let h : F.obj X₁ ⟶ F.obj X₂ :=
    canonicalComparisonMap.{u, v} f g₁ g₂ hψ₁loc hrange₁ gen hgen
  let h' : F.obj X₂ ⟶ F.obj X₁ :=
    canonicalComparisonMap.{u, v} f g₂ g₁ hψ₂loc hrange₂ gen' hgen'
  let d₁ : X₁ ⟶ X₂ := F.preimage h
  let d₂ : X₂ ⟶ X₁ := F.preimage h'
  have hd₁ : F.map d₁ = h := F.map_preimage h
  have hd₂ : F.map d₂ = h' := F.map_preimage h'
  -- the comparisons are mutually inverse
  have hgg : (e₁.symm.toLinearMap.comp e₂.toLinearMap).comp
        (e₂.symm.toLinearMap.comp e₁.toLinearMap) =
      LinearMap.id (R := AdicCompletion I A)
        (M := TensorProduct A (AdicCompletion I A) M₁) := by
    refine LinearMap.ext fun x => ?_
    simp
  have hgg' : (e₂.symm.toLinearMap.comp e₁.toLinearMap).comp
        (e₁.symm.toLinearMap.comp e₂.toLinearMap) =
      LinearMap.id (R := AdicCompletion I A)
        (M := TensorProduct A (AdicCompletion I A) M₂) := by
    refine LinearMap.ext fun x => ?_
    simp
  have hinv₁ : d₁ ≫ d₂ = 𝟙 X₁ := by
    refine F.map_injective ?_
    rw [F.map_comp, hd₁, hd₂, F.map_id]
    refine FormalGlueing.ModuleGlueingMap.ext (ModuleCat.hom_ext hgg) (funext fun i => ?_)
    exact localComparison_comp_symm f g₁ g₂ hψ₁loc hψ₂loc i
  have hinv₂ : d₂ ≫ d₁ = 𝟙 X₂ := by
    refine F.map_injective ?_
    rw [F.map_comp, hd₁, hd₂, F.map_id]
    refine FormalGlueing.ModuleGlueingMap.ext (ModuleCat.hom_ext hgg') (funext fun i => ?_)
    exact localComparison_comp_symm f g₂ g₁ hψ₂loc hψ₁loc i
  -- the comparison is compatible with the maps out of `N`
  have hcompat : g₁ ≫ d₁ = g₂ := by
    refine F.map_injective ?_
    rw [F.map_comp, hd₁]
    refine FormalGlueing.ModuleGlueingMap.ext ?_ (funext fun i => ?_)
    · exact ModuleCat.hom_ext (LinearMap.ext hgen)
    · exact ModuleCat.hom_ext
        (LinearMap.ext fun y => localComparison_apply f g₁ g₂ hψ₁loc i y)
  -- the comparison realizes the generic identification
  have hgeneric : LinearMap.baseChange (AdicCompletion I A) d₁.hom =
      e₂.symm.toLinearMap.comp e₁.toLinearMap :=
    congrArg ModuleCat.Hom.hom (congrArg (fun k : F.obj X₁ ⟶ F.obj X₂ => k.generic) hd₁)
  let d : M₁ ≃ₗ[A] M₂ :=
    { d₁.hom with
      invFun := d₂.hom
      left_inv := fun x => congrArg (fun k : X₁ ⟶ X₁ => k x) hinv₁
      right_inv := fun x => congrArg (fun k : X₂ ⟶ X₂ => k x) hinv₂ }
  have hdlin : d.toLinearMap = d₁.hom := rfl
  refine ⟨d, ⟨?_, ?_⟩, ?_⟩
  · exact congrArg ModuleCat.Hom.hom hcompat
  · rw [hdlin, hgeneric]
    refine LinearMap.ext fun x => ?_
    show e₂ (e₂.symm (e₁ x)) = e₁ x
    rw [e₂.apply_symm_apply]
  · rintro c ⟨hc₁, hc₂⟩
    have hc₂' : ∀ x : TensorProduct A (AdicCompletion I A) M₁,
        e₂ (LinearMap.baseChange (AdicCompletion I A) c.toLinearMap x) = e₁ x :=
      fun x => LinearMap.congr_fun hc₂ x
    have hcmap : ModuleCat.ofHom (X := X₁) (Y := X₂) c.toLinearMap = d₁ := by
      refine F.map_injective ?_
      rw [hd₁]
      refine FormalGlueing.ModuleGlueingMap.ext ?_ (funext fun i => ?_)
      · refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
        show LinearMap.baseChange (AdicCompletion I A) c.toLinearMap x = e₂.symm (e₁ x)
        rw [← hc₂' x, e₂.symm_apply_apply]
      · refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
        obtain ⟨y, rfl⟩ := (hψ₁loc i).2 z
        show FormalGlueing.canonicalLocalMap f (ModuleCat.ofHom c.toLinearMap) i
            (FormalGlueing.canonicalLocalMap f g₁ i y) =
          localComparison f g₁ g₂ hψ₁loc i (FormalGlueing.canonicalLocalMap f g₁ i y)
        rw [canonicalLocalMap_comp_apply f g₁ (ModuleCat.ofHom c.toLinearMap) i y,
          localComparison_apply f g₁ g₂ hψ₁loc i y]
        exact congrArg (fun k : N' ⟶ X₂ => FormalGlueing.canonicalLocalMap f k i y)
          (ModuleCat.hom_ext hc₁ : g₁ ≫ ModuleCat.ofHom c.toLinearMap = g₂)
    refine LinearEquiv.ext fun x => ?_
    exact congrArg (fun k : X₁ ⟶ X₂ => k x) hcmap

end
