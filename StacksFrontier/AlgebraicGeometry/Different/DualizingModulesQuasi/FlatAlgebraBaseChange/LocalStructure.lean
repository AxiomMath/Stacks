module

public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.FlatAlgebraBaseChange.FiniteCase
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingBaseChange.Independence
public import StacksFrontier.RingTheory.Etale.LocalStructure
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Arbitrary base change for the dualizing module: local criteria and étale-local structure

This part collects the inputs for reducing the bijectivity of
`Stacks.Discriminant.dualizingModule.baseChangeLinearMap` to the finite case, locally on
`Spec B₁`:

* the value of `baseChangeLinearMap` on elements `1 ⊗ m` (`baseChangeLinearMap_one_tmul`),
  together with its compatibility with towers and with changes of factorization;
* criteria detecting bijectivity of a linear map after a faithfully flat base change and on
  localizations at primes (`linearMap_bijective_of_localizations`,
  `localizedMap_bijective_of_lTensor`);
* the local structure of a quasi-finite algebra: over a prime of `B₁` there are an étale
  `A → A'` and a prime of `A'` with the same residue field for which `A' ⊗[A] B` splits off a
  factor that is finite and projective over `A'` and contains the prime in question
  (`exists_etale_projective_component_at`, `exists_prime_lift_avoiding_after_baseChange`).

## References

* [Stacks Project, Tag 0BVF](https://stacks.math.columbia.edu/tag/0BVF)
* [Stacks Project, Tag 0BVB](https://stacks.math.columbia.edu/tag/0BVB)
* [Stacks Project, Tag 0BT3](https://stacks.math.columbia.edu/tag/0BT3)
-/

@[expose] public section


open scoped TensorProduct

universe u v w x y

namespace Stacks.Discriminant

namespace dualizingModule

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

open Topology CategoryTheory Opposite AlgebraicGeometry

/-- The map `baseChangeLinearMap F A₁` sends `1 ⊗ m` to the image of `m` under
`dualizingModule.baseChange F A₁`. -/
theorem baseChangeLinearMap_one_tmul
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁]
    (m : dualizingModule F) :
    letI : Algebra B (A₁ ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    letI : Module B
        (dualizingModule (FiniteOpenFactorization.baseChange F A₁)) :=
      Module.compHom _ (algebraMap B (A₁ ⊗[A] B))
    letI : IsScalarTower B (A₁ ⊗[A] B)
        (dualizingModule (FiniteOpenFactorization.baseChange F A₁)) :=
      IsScalarTower.of_compHom B (A₁ ⊗[A] B) _
    baseChangeLinearMap F A₁ (1 ⊗ₜ[B] m) =
      dualizingModule.baseChange F A₁ m := by
  let B₁ := A₁ ⊗[A] B
  let F₁ := FiniteOpenFactorization.baseChange F A₁
  let : Algebra B B₁ := Algebra.TensorProduct.rightAlgebra
  let : Module B (dualizingModule F₁) := Module.compHom _ (algebraMap B B₁)
  let : IsScalarTower B B₁ (dualizingModule F₁) := IsScalarTower.of_compHom B B₁ _
  show (((LinearMap.lsmul B₁ (dualizingModule F₁) (1 : B₁)).restrictScalars B).comp
      (dualizingModule.baseChange F A₁)) m = _
  simp

private theorem baseChangeLinearMap_comp_one_tmul
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁]
    (A₂ : Type y) [CommRing A₂] [Algebra A A₂] [Algebra A₁ A₂]
    [IsScalarTower A A₁ A₂]
    (m : dualizingModule F) :
    let F₁ := FiniteOpenFactorization.baseChange F A₁
    let F₁₂ := FiniteOpenFactorization.baseChange F₁ A₂
    let F₂ := FiniteOpenFactorization.baseChange F A₂
    letI : Algebra B (A₁ ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra B (A₂ ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra (A₁ ⊗[A] B) (A₂ ⊗[A₁] (A₁ ⊗[A] B)) :=
      Algebra.TensorProduct.rightAlgebra
    letI : Module (A₁ ⊗[A] B) (dualizingModule F₁) :=
      dualizingModule.instModule F₁
    letI : Module B (dualizingModule F₁) :=
      Module.compHom _ (algebraMap B (A₁ ⊗[A] B))
    letI : IsScalarTower B (A₁ ⊗[A] B) (dualizingModule F₁) :=
      IsScalarTower.of_compHom B (A₁ ⊗[A] B) _
    letI : Module (A₂ ⊗[A₁] (A₁ ⊗[A] B)) (dualizingModule F₁₂) :=
      dualizingModule.instModule F₁₂
    (dualizingModule.baseChangeTowerEquiv F A₁ A₂).1
        (baseChangeLinearMap F₁ A₂
          (1 ⊗ₜ[A₁ ⊗[A] B] baseChangeLinearMap F A₁ (1 ⊗ₜ[B] m))) =
      baseChangeLinearMap F A₂ (1 ⊗ₜ[B] m) := by
  let F₁ := FiniteOpenFactorization.baseChange F A₁
  let F₁₂ := FiniteOpenFactorization.baseChange F₁ A₂
  let F₂ := FiniteOpenFactorization.baseChange F A₂
  let : Algebra B (A₁ ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let : Algebra B (A₂ ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let : Algebra (A₁ ⊗[A] B) (A₂ ⊗[A₁] (A₁ ⊗[A] B)) :=
    Algebra.TensorProduct.rightAlgebra
  let : Module (A₁ ⊗[A] B) (dualizingModule F₁) :=
    dualizingModule.instModule F₁
  let : Module B (dualizingModule F₁) :=
    Module.compHom _ (algebraMap B (A₁ ⊗[A] B))
  let : IsScalarTower B (A₁ ⊗[A] B) (dualizingModule F₁) :=
    IsScalarTower.of_compHom B (A₁ ⊗[A] B) _
  let : Module (A₂ ⊗[A₁] (A₁ ⊗[A] B)) (dualizingModule F₁₂) :=
    dualizingModule.instModule F₁₂
  have hinner := baseChangeLinearMap_one_tmul F A₁ m
  have houter := baseChangeLinearMap_one_tmul F₁ A₂
    (dualizingModule.baseChange F A₁ m)
  have hdirect := baseChangeLinearMap_one_tmul F A₂ m
  rw [← hinner] at houter
  show (dualizingModule.baseChangeTowerEquiv F A₁ A₂).1
      (baseChangeLinearMap F₁ A₂
        (1 ⊗ₜ[A₁ ⊗[A] B]
          baseChangeLinearMap F A₁ (1 ⊗ₜ[B] m))) =
    baseChangeLinearMap F A₂ (1 ⊗ₜ[B] m)
  rw [houter, hdirect, hinner]
  exact dualizingModule.baseChange_comp F A₁ A₂ m

private theorem baseChangeLinearMap_congr
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (G : FiniteOpenFactorization.{u, v, x} A B)
    [IsNoetherianRing A]
    (A₁ : Type y) [CommRing A₁] [Algebra A A₁] [IsNoetherianRing A₁] :
    let B₁ := A₁ ⊗[A] B
    let F₁ := FiniteOpenFactorization.baseChange F A₁
    let G₁ := FiniteOpenFactorization.baseChange G A₁
    letI : Algebra B B₁ := Algebra.TensorProduct.rightAlgebra
    letI : Module B (dualizingModule F₁) := Module.compHom _ (algebraMap B B₁)
    letI : IsScalarTower B B₁ (dualizingModule F₁) := IsScalarTower.of_compHom B B₁ _
    letI : Module B (dualizingModule G₁) := Module.compHom _ (algebraMap B B₁)
    letI : IsScalarTower B B₁ (dualizingModule G₁) := IsScalarTower.of_compHom B B₁ _
    letI : Module B₁ (dualizingModule F₁) := inferInstance
    letI : Module B₁ (dualizingModule G₁) := inferInstance
    (dualizingModuleEquiv F₁ G₁).toLinearMap.comp
        (baseChangeLinearMap F A₁) =
      (baseChangeLinearMap G A₁).comp
        ((dualizingModuleEquiv F G).toLinearMap.baseChange B₁) := by
  classical
  let B₁ := A₁ ⊗[A] B
  let F₁ := FiniteOpenFactorization.baseChange F A₁
  let G₁ := FiniteOpenFactorization.baseChange G A₁
  let : Algebra B B₁ := Algebra.TensorProduct.rightAlgebra
  let : Module B (dualizingModule F₁) := Module.compHom _ (algebraMap B B₁)
  let : IsScalarTower B B₁ (dualizingModule F₁) := IsScalarTower.of_compHom B B₁ _
  let : Module B (dualizingModule G₁) := Module.compHom _ (algebraMap B B₁)
  let : IsScalarTower B B₁ (dualizingModule G₁) := IsScalarTower.of_compHom B B₁ _
  let : Module B₁ (dualizingModule F₁) := inferInstance
  let : Module B₁ (dualizingModule G₁) := inferInstance
  let e := dualizingModuleEquiv F G
  let e₁ := dualizingModuleEquiv F₁ G₁
  have h0 (m : dualizingModule F) :
      e₁ (baseChangeLinearMap F A₁ (1 ⊗ₜ[B] m)) =
        baseChangeLinearMap G A₁ (1 ⊗ₜ[B] e m) := by
    rw [baseChangeLinearMap_one_tmul, baseChangeLinearMap_one_tmul]
    exact dualizingModule.baseChange_congr F G A₁ m
  let l := e₁.toLinearMap.comp (baseChangeLinearMap F A₁)
  let r := (baseChangeLinearMap G A₁).comp (e.toLinearMap.baseChange B₁)
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' =>
      calc
        l (z + z') = l z + l z' := map_add l _ _
        _ = r z + r z' := congrArg₂ (· + ·) hz hz'
        _ = r (z + z') := (map_add r _ _).symm
  | tmul s m =>
      show e₁ (baseChangeLinearMap F A₁ (s ⊗ₜ[B] m)) =
        baseChangeLinearMap G A₁ ((e.toLinearMap.baseChange B₁) (s ⊗ₜ[B] m))
      calc
        _ = e₁ (s • baseChangeLinearMap F A₁ (1 ⊗ₜ[B] m)) := by
          rw [TensorProduct.tmul_eq_smul_one_tmul]
          simp only [map_smul]
        _ = s • e₁ (baseChangeLinearMap F A₁ (1 ⊗ₜ[B] m)) := map_smul e₁.toLinearMap _ _
        _ = s • baseChangeLinearMap G A₁ (1 ⊗ₜ[B] e m) := congrArg (fun y => s • y) (h0 m)
        _ = baseChangeLinearMap G A₁ (s • (1 ⊗ₜ[B] e m)) :=
          (map_smul (baseChangeLinearMap G A₁) _ _).symm
        _ = _ := by
          rw [← TensorProduct.tmul_eq_smul_one_tmul s (e m)]
          simp [LinearMap.baseChange_tmul]

private theorem bijective_of_faithfullyFlat_lTensor
    {R T M N : Type*} [CommRing R] [CommRing T]
    [Algebra R T] [Module.FaithfullyFlat R T]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N)
    (h : Function.Bijective (LinearMap.lTensor T f)) : Function.Bijective f := by
  exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective
    (R := R) (M := T) (f := f)).mp h

theorem linearMap_bijective_of_localizations
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N)
    (h : ∀ p : PrimeSpectrum R,
      Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl f)) :
    Function.Bijective f := by
  constructor
  · intro x y hxy
    by_contra hne
    have hx : x - y ≠ 0 := sub_ne_zero.mpr hne
    have hmem : x - y ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker]
      rw [map_sub, hxy]
      simp
    let K := LinearMap.ker f
    let : AddCommGroup K := K.addCommGroup
    let : Module R K := K.module
    let z : K := ⟨x - y, hmem⟩
    have hz : z ≠ 0 := by
      intro hz
      apply hx
      exact congrArg Subtype.val hz
    have hkn : Nontrivial K := ⟨z, 0, by
      intro hz0
      exact hz (by simpa using congrArg Subtype.val hz0)⟩
    obtain ⟨p, hp⟩ := Module.nonempty_support_of_nontrivial (R := R) (M := K)
    let k : K →ₗ[R] LinearMap.ker (LocalizedModule.map p.asIdeal.primeCompl f) :=
      LinearMap.toKerIsLocalized p.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N) f
    let : IsLocalizedModule p.asIdeal.primeCompl k :=
      LinearMap.toKerLocalized_isLocalizedModule
        (Localization p.asIdeal.primeCompl) p.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N) f
    let e := IsLocalizedModule.iso p.asIdeal.primeCompl k
    have htarget : Nontrivial (LinearMap.ker
        (LocalizedModule.map p.asIdeal.primeCompl f)) := by
      let : Nontrivial (LocalizedModule p.asIdeal.primeCompl K) := hp
      obtain ⟨a, b, hab⟩ := exists_pair_ne (LocalizedModule p.asIdeal.primeCompl K)
      refine ⟨e a, e b, ?_⟩
      intro he
      exact hab (e.injective he)
    have hbot : LinearMap.ker (LocalizedModule.map p.asIdeal.primeCompl f) = ⊥ :=
      LinearMap.ker_eq_bot.mpr (h p).1
    have hsub : Subsingleton (LinearMap.ker
        (LocalizedModule.map p.asIdeal.primeCompl f)) := by
      rw [hbot]
      infer_instance
    exact (not_nontrivial_iff_subsingleton.mpr hsub) htarget
  · intro y
    let C := N ⧸ LinearMap.range f
    let : AddCommGroup C := inferInstance
    let : Module R C := inferInstance
    have hsurj : Function.Surjective f := by
      by_contra hsurj
      have hC : Nontrivial C := by
        rw [Submodule.Quotient.nontrivial_iff]
        intro htop
        exact hsurj (LinearMap.range_eq_top.mp htop)
      obtain ⟨p, hp⟩ := Module.nonempty_support_of_nontrivial (R := R) (M := C)
      have hloc := (h p).2
      have hCsub : Subsingleton (LocalizedModule p.asIdeal.primeCompl C) :=
        (LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker
          p.asIdeal.primeCompl f).mp hloc
      exact (not_nontrivial_iff_subsingleton.mpr hCsub) hp
    exact hsurj y

theorem localizedMap_bijective_of_lTensor
    {R M N T : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [CommRing T] [Algebra R T]
    (p : PrimeSpectrum R)
    [Algebra (Localization p.asIdeal.primeCompl) T]
    [IsScalarTower R (Localization p.asIdeal.primeCompl) T]
    [Module.FaithfullyFlat (Localization p.asIdeal.primeCompl) T]
    (f : M →ₗ[R] N)
    (h : Function.Bijective (LinearMap.lTensor T f)) :
    Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl f) := by
  let S := p.asIdeal.primeCompl
  let : Module T (T ⊗[Localization S] LocalizedModule S M) := TensorProduct.leftModule
  let : Module T (T ⊗[Localization S] LocalizedModule S N) := TensorProduct.leftModule
  let : Module T (T ⊗[R] M) := TensorProduct.leftModule
  let : Module T (T ⊗[R] N) := TensorProduct.leftModule
  let eM₁ : T ⊗[Localization S] LocalizedModule S M ≃ₗ[T]
      T ⊗[Localization S] (Localization S ⊗[R] M) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl T T)
      (LocalizedModule.equivTensorProduct S M)
  let eN₁ : T ⊗[Localization S] LocalizedModule S N ≃ₗ[T]
      T ⊗[Localization S] (Localization S ⊗[R] N) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl T T)
      (LocalizedModule.equivTensorProduct S N)
  let eM₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange R
    (Localization S) T T M
  let eN₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange R
    (Localization S) T T N
  let eM : T ⊗[Localization S] LocalizedModule S M ≃ₗ[T] T ⊗[R] M :=
    eM₁.trans eM₂
  let eN : T ⊗[Localization S] LocalizedModule S N ≃ₗ[T] T ⊗[R] N :=
    eN₁.trans eN₂
  let fT := TensorProduct.AlgebraTensorModule.lTensor T T f
  let fLocT := TensorProduct.AlgebraTensorModule.lTensor T T
    (LocalizedModule.map S f)
  have hcomm : eN.toLinearMap.comp fLocT = fT.comp eM.toLinearMap := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' =>
      simp only [LinearMap.comp_apply, map_add, hz, hz', fT.map_add, fLocT.map_add]
    | tmul t x =>
      induction x using LocalizedModule.induction_on with
      | h m s =>
        simp [eM, eN, eM₁, eN₁, eM₂, eN₂, fLocT, fT,
          TensorProduct.AlgebraTensorModule.lTensor,
          LocalizedModule.equivTensorProduct_apply_mk, LocalizedModule.map_mk,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
  have hright : Function.Bijective
      (eN.toLinearMap.comp fLocT) := by
    rw [hcomm]
    have hfT : Function.Bijective fT := by
      show Function.Bijective (LinearMap.lTensor T f)
      exact h
    exact hfT.comp eM.bijective
  have hlocalTensor : Function.Bijective
      fLocT :=
    ⟨fun x y hxy => by
      exact hright.1 (congrArg eN hxy),
      fun y => by
        obtain ⟨x, hx⟩ := hright.2 (eN y)
        refine ⟨x, ?_⟩
        apply eN.injective
        exact hx⟩
  exact bijective_of_faithfullyFlat_lTensor (LocalizedModule.map S f) (by
    show Function.Bijective (LinearMap.lTensor T (LocalizedModule.map S f))
    exact hlocalTensor)

theorem atPrime_localRingHom_faithfullyFlat
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (I : Ideal R) (J : Ideal S) [I.IsPrime] [J.IsPrime]
    (hIJ : I = J.comap f) (hf : f.Flat) :
    letI : Algebra (Localization.AtPrime I) (Localization.AtPrime J) :=
      (Localization.localRingHom I J f hIJ).toAlgebra
    Module.FaithfullyFlat (Localization.AtPrime I) (Localization.AtPrime J) := by
  let g := Localization.localRingHom I J f hIJ
  let : Algebra (Localization.AtPrime I) (Localization.AtPrime J) := g.toAlgebra
  have hg : g.Flat := RingHom.Flat.localRingHom hf J I hIJ
  have hglocal : IsLocalHom g := Localization.isLocalHom_localRingHom I J f hIJ
  have : Module.Flat (Localization.AtPrime I) (Localization.AtPrime J) :=
    (RingHom.flat_algebraMap_iff (R := Localization.AtPrime I)
      (S := Localization.AtPrime J)).mp (by
        show RingHom.Flat g
        exact hg)
  have : IsLocalHom (algebraMap (Localization.AtPrime I) (Localization.AtPrime J)) := by
    show IsLocalHom g
    exact hglocal
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

noncomputable def awayMapToAtPrime
    {R S : Type*} [CommRing R] [CommRing S] (x : R)
    (f : R →+* S) (P : Ideal S) [P.IsPrime] (hx : f x ∉ P) :
    Localization.Away x →+* Localization.AtPrime P := by
  let g : R →+* Localization.AtPrime P := (algebraMap S (Localization.AtPrime P)).comp f
  exact IsLocalization.Away.lift x (g := g)
    (IsLocalization.map_units (Localization.AtPrime P) (⟨f x, hx⟩ : P.primeCompl))

theorem awayMapToAtPrime_algebraMap
    {R S : Type*} [CommRing R] [CommRing S] (x : R)
    (f : R →+* S) (P : Ideal S) [P.IsPrime] (hx : f x ∉ P) (r : R) :
    awayMapToAtPrime x f P hx (algebraMap R (Localization.Away x) r) =
      algebraMap S (Localization.AtPrime P) (f r) := by
  simp [awayMapToAtPrime, RingHom.comp_apply]

private lemma finite_projective_of_finite_away_localization
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Module.Flat R S] [IsNoetherianRing R]
    (e : S) [IsLocalization.Away e T] [Module.Finite R T] :
    Module.Projective R T := by
  let : Module.Flat S T :=
    IsLocalization.flat T (.powers e)
  let : Module.Flat R T := Module.Flat.trans R S T
  let : Module.FinitePresentation R T := Module.finitePresentation_of_finite R T
  exact Module.Flat.projective_of_finitePresentation

private lemma finite_projective_away_after_baseChange
    {R S R₁ : Type*} [CommRing R] [CommRing S] [CommRing R₁]
    [Algebra R S] [Algebra R R₁]
    (e : S) [Module.Finite R (Localization.Away e)]
    [Module.Projective R (Localization.Away e)] :
  Module.Finite R₁ (Localization.Away ((1 : R₁) ⊗ₜ[R] e)) ∧
      Module.Projective R₁ (Localization.Away ((1 : R₁) ⊗ₜ[R] e)) := by
  let E := IsLocalization.Away.tensorProductEquivTMulRight
    R R₁ e (Localization.Away e)
  have hfinite : Module.Finite R₁ (R₁ ⊗[R] Localization.Away e) := inferInstance
  have hprojective : Module.Projective R₁ (R₁ ⊗[R] Localization.Away e) := inferInstance
  have hfinite' : Module.Finite R₁ (Localization.Away ((1 : R₁) ⊗ₜ[R] e)) :=
    Module.Finite.of_surjective E.toLinearMap E.surjective
  have hprojective' :
      Module.Projective R₁ (Localization.Away ((1 : R₁) ⊗ₜ[R] e)) :=
    Module.Projective.of_equiv' E.toLinearEquiv
  exact ⟨hfinite', hprojective'⟩

private noncomputable def idempotentLocalizationProdEquiv
    {R : Type*} [CommRing R] (e : R) (he : IsIdempotentElem e) :
    R ≃ₐ[R] Localization.Away e × Localization.Away (1 - e) := by
  let C := Localization.Away e
  let D := Localization.Away (1 - e)
  let f : R →ₐ[R] C × D :=
    { toRingHom := (algebraMap R C).prod (algebraMap R D)
      commutes' := fun r => by ext <;> simp }
  have heC : algebraMap R C e = 1 := by
    have hu := IsLocalization.Away.algebraMap_isUnit (R := R) (S := C) e
    apply hu.mul_right_injective
    change algebraMap R C e * algebraMap R C e = algebraMap R C e * 1
    rw [← map_mul, he.eq]
    simp
  have heSubC : algebraMap R C (1 - e) = 0 := by
    rw [map_sub, map_one, heC]
    simp
  have he'D : algebraMap R D (1 - e) = 1 := by
    have hu := IsLocalization.Away.algebraMap_isUnit
      (R := R) (S := D) (1 - e)
    apply hu.mul_right_injective
    change algebraMap R D (1 - e) * algebraMap R D (1 - e) =
      algebraMap R D (1 - e) * 1
    rw [← map_mul, he.one_sub.eq]
    simp
  have heD : algebraMap R D e = 0 := by
    have h := congrArg (fun z : D => z - 1) he'D
    simpa using h
  refine AlgEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply sub_eq_zero.mp
    have h : f (x - y) = 0 := by
      rw [map_sub, hxy]
      simp
    have hC : algebraMap R C (x - y) = 0 := by
      simpa [f] using congrArg Prod.fst h
    have hD : algebraMap R D (x - y) = 0 := by
      simpa [f] using congrArg Prod.snd h
    have hC' : ∃ n : ℕ, e ^ n * (x - y) = 0 := by
      rw [IsLocalization.map_eq_zero_iff (Submonoid.powers e)] at hC
      obtain ⟨⟨m, n, rfl⟩, hm⟩ := hC
      exact ⟨n, hm⟩
    have hD' : ∃ n : ℕ, (1 - e) ^ n * (x - y) = 0 := by
      rw [IsLocalization.map_eq_zero_iff (Submonoid.powers (1 - e))] at hD
      obtain ⟨⟨m, n, rfl⟩, hm⟩ := hD
      exact ⟨n, hm⟩
    obtain ⟨n, hn⟩ := hC'
    have he_mul : e * (x - y) = 0 := by
      cases n with
      | zero =>
          have hxy : x - y = 0 := by simpa using hn
          simp [hxy]
      | succ n => simpa [he.pow_succ_eq n] using hn
    obtain ⟨n, hn⟩ := hD'
    have hone_sub_mul : (1 - e) * (x - y) = 0 := by
      cases n with
      | zero =>
          have hxy : x - y = 0 := by simpa using hn
          simp [hxy]
      | succ n => simpa [(he.one_sub).pow_succ_eq n] using hn
    calc
      x - y = e * (x - y) + (1 - e) * (x - y) := by ring
      _ = 0 := by rw [he_mul, hone_sub_mul]; simp
  · intro z
    obtain ⟨x, hx⟩ := IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e he z.1
    obtain ⟨y, hy⟩ := IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem
      (1 - e) he.one_sub z.2
    refine ⟨x * e + y * (1 - e), ?_⟩
    apply Prod.ext
    · change algebraMap R C (x * e + y * (1 - e)) = z.1
      rw [map_add, map_mul, map_mul, heC, heSubC, hx]
      simp
    · change algebraMap R D (x * e + y * (1 - e)) = z.2
      rw [map_add, map_mul, map_mul, heD, he'D, hy]
      simp

private lemma etaleAwayComponent_projective
    {A B A' : Type*} [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A'] [IsNoetherianRing A] [Module.Flat A B]
    [Algebra.Etale A A']
    (e : A' ⊗[A] B) (_he : IsIdempotentElem e)
    (hfinite : Module.Finite A' (Localization.Away e)) :
    Module.Projective A' (Localization.Away e) := by
  let : Algebra A' (A' ⊗[A] B) := Algebra.TensorProduct.leftAlgebra
  let : Module.Flat A' (A' ⊗[A] B) := inferInstance
  let : Algebra.FiniteType A A' := inferInstance
  let : IsNoetherianRing A' := Algebra.FiniteType.isNoetherianRing A A'
  let : Module.Finite A' (Localization.Away e) := hfinite
  exact finite_projective_of_finite_away_localization
    (R := A') (S := A' ⊗[A] B) (T := Localization.Away e) e

private lemma exists_etale_projective_components
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Flat A B] [Algebra.FiniteType A B]
    (p : Ideal A) [p.IsPrime] :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Algebra.Etale A A')
      (p' : Ideal A') (_ : p'.IsPrime) (_ : p'.LiesOver p)
      (_ : Function.Bijective
        (Ideal.ResidueField.mapₐ p p' (Algebra.ofId _ _) (p'.over_def p)))
      (n : ℕ) (e : Fin (n + 1) → A' ⊗[A] B)
      (_ : CompleteOrthogonalIdempotents e)
      (_ : ∀ (q : Ideal (A' ⊗[A] B)) [q.IsPrime], q.LiesOver p' →
        e (Fin.last n) ∉ q → ¬ Algebra.QuasiFiniteAt A' q),
      (∀ i : Fin n, Module.Finite A' (Localization.Away (e i.castSucc))) ∧
      (∀ i : Fin n, Module.Projective A' (Localization.Away (e i.castSucc))) := by
  classical
  obtain ⟨A', hA', alg, het, p', hp', hp'p, n, e, he, r, hr, hrp, hres,
      hfinite, havoid, hunique, hlast⟩ :=
    Algebra.exists_etale_completeOrthogonalIdempotents_finite_not_quasiFiniteAt
      (R := A) (S := B) p
  let : CommRing A' := hA'
  let : Algebra A A' := alg
  let : Algebra.Etale A A' := het
  refine ⟨A', hA', alg, het, p', hp', hp'p, hres, n, e, he, hlast, ?_, ?_⟩
  · intro i
    exact hfinite i
  · intro i
    exact etaleAwayComponent_projective (A := A) (B := B) (A' := A')
      (e i.castSucc) (he.idem _) (hfinite i)

private lemma exists_prime_lift_along_residueField_equiv
    {A : Type u} {R : Type v} {A' : Type w}
    [CommRing A] [CommRing R] [CommRing A'] [Algebra A R] [Algebra A A']
    (p : Ideal A) [p.IsPrime]
    (q : Ideal R) [q.IsPrime] [q.LiesOver p]
    (p' : Ideal A') [p'.IsPrime] [p'.LiesOver p]
    (hres : Function.Bijective
      (Ideal.ResidueField.mapₐ p p' (Algebra.ofId A A') (p'.over_def p))) :
    ∃ Q : Ideal (A' ⊗[A] R), Q.IsPrime ∧ Q.LiesOver p' ∧
      Q.comap (Algebra.TensorProduct.includeRight : R →ₐ[A] A' ⊗[A] R).toRingHom = q := by
  let fibers := Ideal.fiberIsoOfBijectiveResidueField (S := R) hres
  let Q : Ideal (A' ⊗[A] R) := (fibers.symm ⟨q, inferInstance, inferInstance⟩).1
  let : Q.IsPrime := (fibers.symm ⟨q, inferInstance, inferInstance⟩).2.1
  let : Q.LiesOver p' := (fibers.symm ⟨q, inferInstance, inferInstance⟩).2.2
  have hQq : Q.comap
      (Algebra.TensorProduct.includeRight : R →ₐ[A] A' ⊗[A] R).toRingHom = q := by
    exact Ideal.comap_fiberIsoOfBijectiveResidueField_symm hres
      ⟨q, inferInstance, inferInstance⟩
  exact ⟨Q, inferInstance, inferInstance, hQq⟩

private lemma exists_prime_lift_avoiding_of_residueField_equiv
    {A : Type u} {R : Type v} {A' : Type w}
    [CommRing A] [CommRing R] [CommRing A'] [Algebra A R] [Algebra A A']
    (p : Ideal A) [p.IsPrime]
    (q : Ideal R) [q.IsPrime] [q.LiesOver p]
    (p' : Ideal A') [p'.IsPrime] [p'.LiesOver p]
    (hres : Function.Bijective
      (Ideal.ResidueField.mapₐ p p' (Algebra.ofId A A') (p'.over_def p)))
    (b : R) (hb : b ∉ q) :
    ∃ Q : Ideal (A' ⊗[A] R), Q.IsPrime ∧ Q.LiesOver p' ∧
      Q.comap (Algebra.TensorProduct.includeRight : R →ₐ[A] A' ⊗[A] R).toRingHom = q ∧
      Algebra.TensorProduct.includeRight b ∉ Q := by
  obtain ⟨Q, hQ, hQp', hQq⟩ :=
    exists_prime_lift_along_residueField_equiv p q p' hres
  refine ⟨Q, hQ, hQp', hQq, ?_⟩
  intro hmem
  apply hb
  have hmem' : b ∈ Q.comap
      (Algebra.TensorProduct.includeRight : R →ₐ[A] A' ⊗[A] R).toRingHom := by
    show Algebra.TensorProduct.includeRight b ∈ Q
    exact hmem
  rw [hQq] at hmem'
  exact hmem'

lemma exists_prime_lift_avoiding_after_baseChange
    {A A' B R : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing R]
    [Algebra A A'] [Algebra A B] [Algebra A R]
    (j : B →ₐ[A] R)
    (p : Ideal A) [p.IsPrime]
    (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (r : Ideal R) [r.IsPrime] [r.LiesOver p]
    (hrq : r.comap j.toRingHom = q)
    (p' : Ideal A') [p'.IsPrime] [p'.LiesOver p]
    (hres : Function.Bijective
      (Ideal.ResidueField.mapₐ p p' (Algebra.ofId _ _) (p'.over_def p)))
    (Q : Ideal (A' ⊗[A] B)) [Q.IsPrime] [Q.LiesOver p']
    (hQq : Q.comap
      (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B).toRingHom = q)
    (e : A' ⊗[A] B) (he : e ∉ Q) :
    ∃ Q' : Ideal (A' ⊗[A] R), Q'.IsPrime ∧ Q'.LiesOver p' ∧
      Q'.comap (Algebra.TensorProduct.includeRight : R →ₐ[A] A' ⊗[A] R).toRingHom = r ∧
      Algebra.TensorProduct.map (AlgHom.id A A') j e ∉ Q' := by
  obtain ⟨Q', hQ', hQ'p', hQ'r⟩ :=
    exists_prime_lift_along_residueField_equiv p r p' hres
  let : Algebra A' (A' ⊗[A] R) := Algebra.TensorProduct.leftAlgebra
  let j' : B →ₐ[A] A' ⊗[A] R :=
    (Algebra.TensorProduct.includeRight : R →ₐ[A] A' ⊗[A] R).comp j
  let φ : A' ⊗[A] B →ₐ[A'] A' ⊗[A] R :=
    Algebra.TensorProduct.lift (Algebra.ofId A' (A' ⊗[A] R)) j'
      (fun _ _ => Commute.all _ _)
  let ψ := Algebra.TensorProduct.map (AlgHom.id A A') j
  have hφψ : φ.toRingHom = ψ.toRingHom := by
    apply Algebra.TensorProduct.ringHom_ext
    · ext a
      simp [φ, ψ, Algebra.TensorProduct.map_tmul]
    · ext b
      simp [φ, ψ, j', Algebra.TensorProduct.map_tmul]
  have hQ'φ : (Q'.comap φ.toRingHom).comap
      (algebraMap A' (A' ⊗[A] B)) = p' := by
    rw [Ideal.comap_comap]
    have hleft : φ.toRingHom.comp (algebraMap A' (A' ⊗[A] B)) =
        algebraMap A' (A' ⊗[A] R) := by
      ext a
      show φ ((Algebra.TensorProduct.includeLeft :
        A' →ₐ[A] A' ⊗[A] B) a) =
        algebraMap A' (A' ⊗[A] R) a
      simp [φ]
    rw [hleft]
    exact (Ideal.LiesOver.over (P := Q') (p := p')).symm
  let : (Q'.comap φ.toRingHom).LiesOver p' := ⟨hQ'φ.symm⟩
  have hQ'Q : Q'.comap φ.toRingHom = Q := by
    apply Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hres
    have hright : φ.toRingHom.comp
        (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B).toRingHom =
        ((Algebra.TensorProduct.includeRight : R →ₐ[A] A' ⊗[A] R).toRingHom.comp
          j.toRingHom) := by
      ext b
      simp [φ, j']
    show Q'.comap (φ.toRingHom.comp
        (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B).toRingHom) =
      Q.comap (Algebra.TensorProduct.includeRight.toRingHom)
    rw [hright]
    show (Q'.comap (Algebra.TensorProduct.includeRight.toRingHom)).comap j.toRingHom =
      Q.comap (Algebra.TensorProduct.includeRight.toRingHom)
    rw [hQ'r, hrq, hQq]
  refine ⟨Q', hQ', hQ'p', hQ'r, ?_⟩
  show ψ e ∉ Q'
  intro he'
  apply he
  rw [← hQ'Q]
  have heφ : φ e ∈ Q' := by
    have h : ψ.toRingHom e ∈ Q' := he'
    rw [← hφψ] at h
    exact h
  exact heφ

lemma exists_etale_projective_component_at
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Flat A B] [Algebra.FiniteType A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (hqf : Algebra.QuasiFiniteAt A q) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Algebra.Etale A A')
      (p' : Ideal A') (_ : p'.IsPrime) (_ : p'.LiesOver p)
      (_ : Function.Bijective
        (Ideal.ResidueField.mapₐ p p' (Algebra.ofId _ _) (p'.over_def p)))
      (Q : Ideal (A' ⊗[A] B)) (_ : Q.IsPrime) (_ : Q.LiesOver p')
      (e : A' ⊗[A] B), IsIdempotentElem e ∧ Module.Finite A' (Localization.Away e) ∧ Q.comap
        (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B).toRingHom = q ∧
        e ∉ Q ∧ Module.Projective A' (Localization.Away e) := by
  classical
  obtain ⟨A', hA', alg, het, p', hp', hp'p, hres, n, e, he, hlast, hfinite, hproj⟩ :=
    exists_etale_projective_components (A := A) (B := B) p
  let : CommRing A' := hA'
  let : Algebra A A' := alg
  let : Algebra.Etale A A' := het
  obtain ⟨Q, hQ, hQp', hQq⟩ := exists_prime_lift_along_residueField_equiv p q p' hres
  have := hQ
  have hqf' : Algebra.QuasiFiniteAt A' Q := by
    exact (Algebra.quasiFiniteAt_baseChange_iff A' q Q hQq.symm).mpr hqf
  have hlast : e (Fin.last n) ∈ Q := by
    by_contra hnot
    exact hlast Q hQp' hnot hqf'
  have hsome : ∃ i : Fin n, e i.castSucc ∉ Q := by
    by_contra h
    push Not at h
    have hone : (1 : A' ⊗[A] B) ∈ Q := by
      rw [← he.complete]
      apply Ideal.sum_mem Q
      intro i hi
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact h j
      · exact hlast
    exact Ideal.IsPrime.ne_top' (Q.eq_top_iff_one.mpr hone)
  obtain ⟨i, hi⟩ := hsome
  exact ⟨A', hA', alg, het, p', hp', hp'p, hres, Q, hQ, hQp',
    e i.castSucc, he.idem _, hfinite i, hQq, hi, hproj i⟩

end dualizingModule
end Stacks.Discriminant
