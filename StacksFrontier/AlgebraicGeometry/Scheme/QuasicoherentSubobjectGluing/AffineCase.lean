module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Scheme.Affine.Functoriality
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasicoherentSubobjectGluing.FiniteTypeLocal
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasicoherentSubobjectGluing.LocalizedNumerators
import all StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness

/-!
# The affine case of the finite type extension lemma

This file develops the affine case of [Stacks, Tag 01PF]: on `Spec R`, a quasi-coherent module
whose restriction to a quasi-compact open `U` is of finite type contains a quasi-coherent
submodule of finite type agreeing with it over `U`.

## Main results

* `AlgebraicGeometry.exists_generatingSections_of_isFiniteType_restrict` — finite type of `M|_U`
  is witnessed by finitely many generating sections over opens of the ambient scheme inside `U`.
* `AlgebraicGeometry.exists_basicOpen_module_finite_localization` — every point of `U` has a
  standard open `D(f) ⊆ U` with `N_f` a finite `R_f`-module.
* `AlgebraicGeometry.exists_fg_submodule_localized_eq_top_of_isFiniteType_restrict` — the
  finitely generated submodule `N' ⊆ N` and the finite standard cover of `U` on which it is
  everything.
* `AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_isIso_restrict` — **the affine case
  of [Stacks, Tag 01PF]**: the quasi-coherent submodule of finite type agreeing with the module
  over `U`.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits SheafOfModules TopologicalSpace
open Stacks.AlgebraicGeometry

namespace AlgebraicGeometry

universe u

/-! ### Generating sections on opens of the ambient scheme -/

/-- **Finite type of a restriction is witnessed inside the open.** If `M|_U` is of finite type
then every point of `U` lies in an open `W ≤ U` of the ambient scheme over which `M` has finitely
many generating sections. -/
theorem exists_generatingSections_of_isFiniteType_restrict {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (h : (M.restrict U.ι).IsFiniteType) (x : X) (hx : x ∈ U) :
    ∃ (W : X.Opens) (σ : (M.over W).GeneratingSections), W ≤ U ∧ x ∈ W ∧ σ.IsFiniteType := by
  obtain ⟨V₀, hxV, σ, hσ⟩ := Stacks.SheafOfModules.isFiniteTypeAt_of_isFiniteType
    (M.restrict U.ι) h (⟨x, hx⟩ : U.toScheme)
  let V : U.toScheme.Opens := V₀
  let W : X.Opens := U.ι ''ᵁ V
  let φ : V.toScheme ≅ W.toScheme := U.ι.isoImage V
  have hcomp : V.ι ≫ U.ι = φ.hom ≫ W.ι := (Scheme.Hom.isoImage_hom_ι _ _).symm
  have heq : φ.inv ≫ (φ.hom ≫ W.ι) = W.ι := by rw [Iso.inv_hom_id_assoc]
  let τ₀ : ((M.restrict U.ι).restrict V.ι).GeneratingSections :=
    Stacks.AlgebraicGeometry.CoherentFinite.generatingSectionsOfOver V (M.restrict U.ι) σ
  let τ₁ : (M.restrict (V.ι ≫ U.ι)).GeneratingSections :=
    (GeneratingSections.equivOfIso
      ((Scheme.Modules.restrictFunctorComp V.ι U.ι).app M)).symm τ₀
  let τ₂ : (M.restrict (φ.hom ≫ W.ι)).GeneratingSections :=
    GeneratingSections.equivOfIso ((Scheme.Modules.restrictFunctorCongr hcomp).app M) τ₁
  let τ₃ : ((M.restrict (φ.hom ≫ W.ι)).restrict φ.inv).GeneratingSections :=
    CoherentTFAE.generatingSectionsRestrict φ.inv τ₂
  let τ₄ : (M.restrict W.ι).GeneratingSections :=
    (GeneratingSections.equivOfIso
      (((Scheme.Modules.restrictFunctorCongr heq).app M).symm ≪≫
        (Scheme.Modules.restrictFunctorComp φ.inv (φ.hom ≫ W.ι)).app M)).symm τ₃
  exact ⟨W, CoherentTFAE.generatingSectionsOver W M τ₄, U.ι_image_le V,
    ⟨⟨x, hx⟩, hxV, rfl⟩, ⟨hσ.finite⟩⟩

/-! ### The standard opens on which the module is finite -/

/-- **Finite type of `Ñ|_U` is witnessed by standard opens.** If `Ñ|_U` is of finite type then
every point of `U` lies in a standard open `D(f) ⊆ U` for which `N_f` is a finite `R_f`-module. -/
theorem exists_basicOpen_module_finite_localization {R : CommRingCat.{u}} (N : ModuleCat.{u} R)
    (U : (Spec R).Opens) (h : ((tilde N).restrict U.ι).IsFiniteType) (x : Spec R) (hx : x ∈ U) :
    ∃ f : R, x ∈ PrimeSpectrum.basicOpen f ∧ PrimeSpectrum.basicOpen f ≤ U ∧
      Module.Finite (Localization.Away f) (LocalizedModule (Submonoid.powers f) N) := by
  obtain ⟨W, σ, hWU, hxW, hσ⟩ :=
    exists_generatingSections_of_isFiniteType_restrict (tilde N) U h x hx
  obtain ⟨-, ⟨f, rfl⟩, hxf, hfW⟩ :=
    Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens hxW
  exact ⟨f, hxf, hfW.trans hWU,
    module_finite_localization_of_localGenerators N f W σ hσ hfW⟩

/-! ### The finitely generated submodule agreeing with `N` over `U` -/

/-- **A finitely generated submodule agreeing with `N` over `U`.** If `Ñ|_U` is of finite type on a
quasi-compact open `U` of `Spec R`, then `U` is covered by finitely many standard opens `D(g i)`
and some finitely generated submodule `N' ⊆ N` has `N'_{g i} = N_{g i}` for every `i`. -/
theorem exists_fg_submodule_localized_eq_top_of_isFiniteType_restrict {R : CommRingCat.{u}}
    (N : ModuleCat.{u} R) (U : (Spec R).Opens) (hU : IsCompact U.1)
    (h : ((tilde N).restrict U.ι).IsFiniteType) :
    ∃ (ι : Type u) (_ : Finite ι) (g : ι → R) (N' : Submodule R N), N'.FG ∧
      (⨆ i, PrimeSpectrum.basicOpen (g i)) = U ∧
      ∀ i, N'.localized (Submonoid.powers (g i)) = ⊤ := by
  classical
  let S : Set R := {f | PrimeSpectrum.basicOpen f ≤ U ∧
    Module.Finite (Localization.Away f) (LocalizedModule (Submonoid.powers f) N)}
  have hcov : U.1 ⊆ ⋃ f : S, (PrimeSpectrum.basicOpen f.1).1 := fun x hx => by
    obtain ⟨f, hxf, hfU, hfin⟩ := exists_basicOpen_module_finite_localization N U h x hx
    exact Set.mem_iUnion.mpr ⟨⟨f, hfU, hfin⟩, hxf⟩
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover
    (fun f : S => (PrimeSpectrum.basicOpen f.1).1)
    (fun f => (PrimeSpectrum.basicOpen f.1).isOpen) hcov
  obtain ⟨N', hfg, hloc⟩ := Submodule.exists_fg_localized_eq_top
    (R := R) (M := N) (ι := {f : S // f ∈ t}) (fun i => i.1.1) fun i => i.1.2.2
  refine ⟨{f : S // f ∈ t}, inferInstance, fun i => i.1.1, N', hfg, le_antisymm ?_ ?_, hloc⟩
  · exact iSup_le fun i => i.1.2.1
  · intro x hx
    obtain ⟨f, hft, hxf⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Opens.mem_iSup.mpr ⟨⟨f, hft⟩, hxf⟩

/-! ### The inclusion of the submodule is an isomorphism over `U` -/

/-- **On the stalk at a point of `D(f)`, the inclusion `Ñ' ⟶ Ñ` is an isomorphism**, provided
`N'` already localizes to the whole of `N_f`. -/
private theorem isIso_stalkFunctor_map_tilde_map {R : CommRingCat.{u}} {N₀ N : ModuleCat.{u} R}
    (φ : N₀ ⟶ N) (hφ : Function.Injective φ.hom) (f : R)
    (hran : (LinearMap.range φ.hom).localized₀ (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) N) = ⊤)
    (x : PrimeSpectrum.Top R) (hx : x ∈ PrimeSpectrum.basicOpen f) :
    IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
      (Scheme.Modules.Hom.mapPresheaf (tilde.map φ))) := by
  have hle : Submonoid.powers f ≤ x.asIdeal.primeCompl :=
    Submonoid.powers_le.mpr ((PrimeSpectrum.mem_basicOpen f x).mp hx)
  have hinj : Function.Injective (IsLocalizedModule.map x.asIdeal.primeCompl
      (tilde.toStalk N₀ x).hom (tilde.toStalk N x).hom φ.hom) :=
    IsLocalizedModule.map_injective _ _ _ φ.hom hφ
  have hsurj : Function.Surjective (IsLocalizedModule.map x.asIdeal.primeCompl
      (tilde.toStalk N₀ x).hom (tilde.toStalk N x).hom φ.hom) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_localizedMap_eq_localized₀_range]
    exact Submodule.localized₀_eq_top_of_le _ hle _ _ hran
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun a b hab => hinj ?_, fun z => ?_⟩
  · exact (tilde.toStalk_map φ x a).symm.trans (hab.trans (tilde.toStalk_map φ x b))
  · obtain ⟨m, hm⟩ := hsurj z
    exact ⟨m, (tilde.toStalk_map φ x m).trans hm⟩

/-- **Over a quasi-compact open covered by standard opens on which the image of `φ` is
everything, `Ñ₀ ⟶ Ñ` restricts to an isomorphism.** -/
private theorem isIso_restrict_tilde_map {R : CommRingCat.{u}} {N₀ N : ModuleCat.{u} R}
    (φ : N₀ ⟶ N) (hφ : Function.Injective φ.hom) {ι : Type u} (g : ι → R) (U : (Spec R).Opens)
    (hcover : (⨆ i, PrimeSpectrum.basicOpen (g i)) = U)
    (hran : ∀ i, (LinearMap.range φ.hom).localized₀ (Submonoid.powers (g i))
      (LocalizedModule.mkLinearMap (Submonoid.powers (g i)) N) = ⊤) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (tilde.map φ)) := by
  refine ExtensionByZeroModules.isIso_of_stalk_isIso U.toScheme.ringCatSheaf _ fun y => ?_
  have hyU : U.ι.base y ∈ ⨆ i, PrimeSpectrum.basicOpen (g i) := by rw [hcover]; exact y.2
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hyU
  have hdirect : IsIso ((Scheme.Modules.toPresheaf (Spec R) ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} (U.ι.base y)).map (tilde.map φ)) :=
    isIso_stalkFunctor_map_tilde_map φ hφ (g i) (hran i) _ hi
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso U.ι y) (tilde.map φ)).mpr
    hdirect

/-! ### The affine case of the extension lemma -/

/-- **The affine case of [Stacks, Tag 01PF].** On the spectrum of a ring, a quasi-coherent module
`H` whose restriction to a quasi-compact open `U` is of finite type has a quasi-coherent submodule
`K` of finite type whose inclusion restricts to an isomorphism over `U` — that is, `K|_U = H|_U`.
-/
theorem exists_finiteTypeQuasicoherentSubobject_isIso_restrict {R : CommRingCat.{u}}
    (H : (Spec R).Modules) [H.IsQuasicoherent] (U : (Spec R).Opens) (hU : IsCompact U.1)
    (h : (H.restrict U.ι).IsFiniteType) :
    ∃ K : Subobject H, (K : (Spec R).Modules).IsQuasicoherent ∧
      (K : (Spec R).Modules).IsFiniteType ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map K.arrow) := by
  classical
  obtain ⟨N, ⟨e⟩⟩ : ∃ N : ModuleCat.{u} R, Nonempty (tilde N ≅ H) := by
    obtain ⟨N, ⟨i⟩⟩ : (tilde.functor R).essImage H := by
      rw [essImage_tilde]; exact ‹H.IsQuasicoherent›
    exact ⟨N, ⟨i⟩⟩
  have : (H.restrict U.ι).IsFiniteType := h
  have h' : ((tilde N).restrict U.ι).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      ((Scheme.Modules.restrictFunctor U.ι).mapIso e).symm
  obtain ⟨ι₀, hfinι, g, N', hfg, hcover, hlocT⟩ :=
    exists_fg_submodule_localized_eq_top_of_isFiniteType_restrict N U hU h'
  obtain ⟨N₀, φ, hφ, hfin₀, hran⟩ :
      ∃ (N₀ : ModuleCat.{u} R) (φ : N₀ ⟶ N), Function.Injective φ.hom ∧
        Module.Finite R N₀ ∧
        ∀ i, (LinearMap.range φ.hom).localized₀ (Submonoid.powers (g i))
          (LocalizedModule.mkLinearMap (Submonoid.powers (g i)) N) = ⊤ := by
    refine ⟨ModuleCat.of R (N' : Type u), ModuleCat.ofHom N'.subtype, ?_, ?_, fun i => ?_⟩
    · simp
    · exact Module.Finite.iff_fg.mpr hfg
    · rw [show LinearMap.range (ModuleCat.ofHom N'.subtype).hom = N' by simp]
      exact Submodule.localized₀_eq_top_of_localized_eq_top N' _ (hlocT i)
  have hrestrict : IsIso ((Scheme.Modules.restrictFunctor U.ι).map (tilde.map φ)) :=
    isIso_restrict_tilde_map φ hφ g U hcover hran
  have hmonoφ : Mono φ := ConcreteCategory.mono_of_injective φ hφ
  have hmonoTilde : Mono (tilde.map φ) := (inferInstance : Mono ((tilde.functor R).map φ))
  have hmonoe : Mono e.hom :=
    ⟨fun a b hab => by simpa using congrArg (fun k => k ≫ e.inv) hab⟩
  obtain ⟨A, ψ, hψmono, hψqc, hψft, hψiso⟩ :
      ∃ (A : (Spec R).Modules) (ψ : A ⟶ H), Mono ψ ∧ A.IsQuasicoherent ∧ A.IsFiniteType ∧
        IsIso ((Scheme.Modules.restrictFunctor U.ι).map ψ) := by
    refine ⟨tilde N₀, tilde.map φ ≫ e.hom, mono_comp _ _, inferInstance,
      (tilde_isFiniteType_iff _).mpr hfin₀, ?_⟩
    rw [Functor.map_comp]
    infer_instance
  have : Mono ψ := hψmono
  have : A.IsFiniteType := hψft
  refine ⟨Subobject.mk ψ, ?_, ?_, ?_⟩
  · exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
      (Subobject.underlyingIso ψ).symm hψqc
  · exact Stacks.SheafOfModules.isFiniteType_of_iso.{u} (Subobject.underlyingIso ψ).symm
  · rw [← Subobject.underlyingIso_hom_comp_eq_mk ψ, Functor.map_comp]
    infer_instance

end AlgebraicGeometry

end
