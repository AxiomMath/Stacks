module

public import StacksFrontier.RingTheory.Smooth.NilpotentLiftTensor
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Smooth.Flat

/-!
# A smooth chart over a principal open, for Stacks 0CJV

From the smoothness at one point of the base change `S₁ ⊗_{B'} C` through the second structure
map `t`, this file produces a principal open `D(h')` of `Spec S₁` around the point and a ring
`Pr`, a localization of `S₁ ⊗_{B'} C`, which is smooth over `S₁[1/h']` with surjective map on
spectra and smooth over `B'` through `t`.

## Main results

* `Algebra.exists_smooth_chart_of_isSmoothAt`: given a smooth `B'`-algebra `C`, smooth also
  through a second ring map `t : B' →+* C`, a finitely presented `B'`-algebra `S₁` and a prime
  `𝔷` of `S₁ ⊗_{B'} C` over a prime `𝔵` of `S₁` at which `S₁ ⊗_{B'} C` is smooth over `B'`
  through `t`, there are `h' ∉ 𝔵` and a ring `Pr`, smooth over `S₁[1/h']` with surjective map
  on spectra and smooth over `B'` through `t`.
-/

@[expose] public section

open TensorProduct

namespace Algebra

universe u

variable {B' : Type u} [CommRing B'] (J : Ideal B')

/-- Let `C` be a smooth `B'`-algebra which is also smooth through a second ring map
`t : B' →+* C`, let `S₁` be a finitely presented `B'`-algebra, and let `𝔷` be a prime of
`S₁ ⊗_{B'} C` lying over the prime `𝔵` of `S₁` such that `S₁ ⊗_{B'} C` is smooth at `𝔷` over `B'`
through `t`. Then there are `h' ∉ 𝔵`, a ring `Pr` and ring maps `α : S₁[1/h'] →+* Pr` and
`β : C →+* Pr` agreeing on `B'`, such that `Pr` is smooth over `S₁[1/h']` via `α`, the map
`Spec Pr → Spec S₁[1/h']` is surjective, and `Pr` is smooth over `B'` via `β ∘ t`. -/
theorem exists_smooth_chart_of_isSmoothAt
    {C : Type u} [CommRing C] [Algebra B' C] [Algebra.Smooth B' C] (t : B' →+* C)
    (ht : @Algebra.Smooth B' _ C _ t.toAlgebra)
    {S₁ : Type u} [CommRing S₁] [Algebra B' S₁] [Algebra.FinitePresentation B' S₁]
    (𝔵 : Ideal S₁) [𝔵.IsPrime] (𝔷 : Ideal (S₁ ⊗[B'] C)) [𝔷.IsPrime]
    (h𝔷 : 𝔷.comap Algebra.TensorProduct.includeLeftRingHom = 𝔵)
    (hsm : @IsSmoothAt B' (S₁ ⊗[B'] C) _ _
      ((Algebra.TensorProduct.includeRight.toRingHom).comp t).toAlgebra 𝔷 _) :
    ∃ (h' : S₁) (_ : h' ∉ 𝔵) (Pr : Type u) (_ : CommRing Pr)
      (α : Localization.Away h' →+* Pr) (β : C →+* Pr),
      α.comp (algebraMap B' (Localization.Away h')) = β.comp (algebraMap B' C) ∧
      @Algebra.Smooth (Localization.Away h') _ Pr _ α.toAlgebra ∧
      Function.Surjective (PrimeSpectrum.comap α) ∧
      @Algebra.Smooth B' _ Pr _ (β.comp t).toAlgebra := by
  classical
  let T := S₁ ⊗[B'] C
  let tSm : B' →+* T := (Algebra.TensorProduct.includeRight.toRingHom).comp t
  have hfpT : @FinitePresentation B' T _ _ tSm.toAlgebra := by
    let algCT : Algebra C T := Algebra.TensorProduct.rightAlgebra
    have hfpCT : FinitePresentation C T :=
      FinitePresentation.equiv
        { (Algebra.TensorProduct.comm B' C S₁) with commutes' := fun c => rfl }
    have htower : @IsScalarTower B' C T t.toAlgebra.toSMul algCT.toSMul tSm.toAlgebra.toSMul :=
      @IsScalarTower.of_algebraMap_eq B' C T _ _ _ t.toAlgebra algCT tSm.toAlgebra fun _ => rfl
    exact @FinitePresentation.trans B' C T _ _ t.toAlgebra _ tSm.toAlgebra algCT htower
      ht.finitePresentation hfpCT
  -- a basic open around `𝔷` on which `T` is smooth through `t`
  obtain ⟨σ, hσ, hσsm⟩ :
      ∃ σ ∉ 𝔷, let := tSm.toAlgebra; Algebra.Smooth B' (Localization.Away σ) := by
    let := tSm.toAlgebra
    have := hfpT
    have := hsm
    exact IsSmoothAt.exists_notMem_smooth B' 𝔷
  -- the image of `D(σ)` in `Spec S₁` is open and contains `𝔵`
  have : Algebra.HasGoingDown S₁ T := Algebra.HasGoingDown.of_flat
  have hopen : IsOpenMap (PrimeSpectrum.comap (algebraMap S₁ T)) :=
    PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
  have hOopen := hopen _ (PrimeSpectrum.basicOpen σ).2
  have h𝔵O : (⟨𝔵, inferInstance⟩ : PrimeSpectrum S₁) ∈
      PrimeSpectrum.comap (algebraMap S₁ T) '' (PrimeSpectrum.basicOpen σ : Set _) :=
    ⟨⟨𝔷, inferInstance⟩, hσ, PrimeSpectrum.ext h𝔷⟩
  obtain ⟨_, ⟨_, ⟨h', rfl⟩, rfl⟩, hxh', hh'O⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open h𝔵O hOopen
  let Pr := Localization.Away (σ * algebraMap S₁ T h')
  let β : C →+* Pr := (algebraMap T Pr).comp Algebra.TensorProduct.includeRight.toRingHom
  have hunit : IsUnit (algebraMap S₁ Pr h') := by
    have := IsLocalization.Away.algebraMap_isUnit (S := Pr) (σ * algebraMap S₁ T h')
    rw [map_mul] at this
    rw [IsScalarTower.algebraMap_apply S₁ T Pr]
    exact isUnit_of_mul_isUnit_right this
  let α : Localization.Away h' →+* Pr := IsLocalization.Away.lift h' hunit
  have hα : α.comp (algebraMap S₁ (Localization.Away h')) = algebraMap S₁ Pr :=
    IsLocalization.Away.lift_comp h' hunit
  refine ⟨h', hxh', Pr, inferInstance, α, β, ?_, ?_, ?_, ?_⟩
  · ext b
    have h1 := congrArg (fun φ => φ (algebraMap B' S₁ b)) hα
    simp only [RingHom.comp_apply] at h1
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply B' S₁ (Localization.Away h'), h1,
      IsScalarTower.algebraMap_apply S₁ T Pr]
    simp only [β, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply]
    congr 1
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_one_eq_one_tmul]
  · let : Algebra (Localization.Away h') Pr := α.toAlgebra
    have : IsScalarTower S₁ (Localization.Away h') Pr :=
      IsScalarTower.of_algebraMap_eq fun x => (congrArg (fun φ => φ x) hα).symm
    have : Algebra.Smooth T Pr := Algebra.Smooth.of_isLocalization_Away (σ * algebraMap S₁ T h')
    have : Algebra.Smooth S₁ Pr := Algebra.Smooth.comp S₁ T Pr
    have : FormallySmooth (Localization.Away h') Pr :=
      FormallySmooth.of_restrictScalars S₁ (Localization.Away h') Pr
    have : FinitePresentation (Localization.Away h') Pr :=
      FinitePresentation.of_restrict_scalars_finitePresentation S₁ _ _
    exact ⟨inferInstance, inferInstance⟩
  · intro 𝔭'
    set 𝔭 := PrimeSpectrum.comap (algebraMap S₁ (Localization.Away h')) 𝔭'
    have h𝔭 : 𝔭 ∈ (PrimeSpectrum.basicOpen h' : Set (PrimeSpectrum S₁)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away h') h']
      exact ⟨𝔭', rfl⟩
    obtain ⟨𝔮, h𝔮σ, h𝔮⟩ := hh'O h𝔭
    have h𝔮h : algebraMap S₁ T h' ∉ 𝔮.asIdeal := by
      intro hm
      apply h𝔭
      rw [← h𝔮]
      exact hm
    have h𝔮mem :
        𝔮 ∈ (PrimeSpectrum.basicOpen (σ * algebraMap S₁ T h') : Set (PrimeSpectrum T)) := by
      rw [PrimeSpectrum.basicOpen_mul]
      exact ⟨h𝔮σ, h𝔮h⟩
    rw [← PrimeSpectrum.localization_away_comap_range Pr] at h𝔮mem
    obtain ⟨𝔮', h𝔮'⟩ := h𝔮mem
    refine ⟨𝔮', PrimeSpectrum.localization_comap_injective (Localization.Away h')
      (Submonoid.powers h') ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply, hα, IsScalarTower.algebraMap_eq S₁ T Pr,
      PrimeSpectrum.comap_comp_apply, h𝔮', h𝔮]
  · let := tSm.toAlgebra
    have := hfpT
    have hsub : (PrimeSpectrum.basicOpen σ : Set (PrimeSpectrum T)) ⊆ smoothLocus B' T :=
      (basicOpen_subset_smoothLocus_iff_smooth).2 hσsm
    have hsm' : Algebra.Smooth B' Pr := by
      refine (basicOpen_subset_smoothLocus_iff_smooth).1 (subset_trans ?_ hsub)
      rw [PrimeSpectrum.basicOpen_mul]
      exact Set.inter_subset_left
    convert hsm'
    exact Algebra.algebra_ext _ _ fun x => by rw [IsScalarTower.algebraMap_apply B' T Pr]; rfl

end Algebra
