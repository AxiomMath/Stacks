module

public import Mathlib.RingTheory.PicardGroup
public import StacksFrontier.AlgebraicGeometry.ChartModuleSystem.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Local

/-!
# Invertibility of the glued sheaf

If every point lies in a chart whose module is free of rank one, or if every chart module is an
invertible module, the glued sheaf is an invertible `𝒪_Y`-module.

## Main definitions

* `AlgebraicGeometry.ChartModuleSystem.restrictFromSpecTopEquiv`: the global sections of the
  restriction of the glued sheaf to `Spec Γ(Y, V c)` are the module on the chart `c`.
* `AlgebraicGeometry.ChartModuleSystem.restrictFromSpecIsoUnit`: the trivialization on a chart
  whose module is free of rank one.

## Main results

* `AlgebraicGeometry.ChartModuleSystem.isInvertibleModule_sheaf`: the glued sheaf is invertible
  when the chart modules are locally free of rank one.
* `AlgebraicGeometry.ChartModuleSystem.isInvertibleModule_sheaf_of_invertible`: the glued sheaf is
  invertible when every chart module is an invertible module.
* `LinearMap.IsBaseChangeAlong.nonempty_linearEquiv_of_free_away`: a base change of an invertible
  module free after inverting `r` is free of rank one where `r` is a unit.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open Stacks.AlgebraicGeometry.TwistMapsInvertible
open scoped TensorProduct

namespace LinearMap.IsBaseChangeAlong

variable {R S M N : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module S N] {σ : R →+* S}

/-- If `f : M → N` exhibits `N` as the base change of an invertible `R`-module `M` along
`σ : R → S`, `σ r` is a unit and `M_r` is free over `R_r`, then `N ≃ S`. -/
theorem nonempty_linearEquiv_of_free_away {f : M →ₛₗ[σ] N} (hf : f.IsBaseChangeAlong)
    [Module.Invertible R M] (r : R) (hr : IsUnit (σ r))
    (hfree : Module.Free (Localization.Away r) (LocalizedModule.Away r M)) :
    Nonempty (N ≃ₗ[S] S) := by
  let := σ.toAlgebra
  let : Module R N := Module.compHom N σ
  have : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hbc : IsBaseChange S f.restrictScalarsAlong := hf
  have : Module.Invertible S N := Module.Invertible.congr hbc.equiv
  refine Module.Invertible.free_iff_linearEquiv.mp ?_
  let : Algebra (Localization.Away r) S := (IsLocalization.Away.lift r hr).toAlgebra
  have : IsScalarTower R (Localization.Away r) S :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.Away.lift_comp r hr).symm
  have : Module.Free (Localization.Away r) (Localization.Away r ⊗[R] M) :=
    .of_equiv (IsLocalizedModule.isBaseChange (Submonoid.powers r) (Localization.Away r)
      (LocalizedModule.mkLinearMap (Submonoid.powers r) M)).equiv.symm
  exact .of_equiv ((TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization.Away r)
    S S M) ≪≫ₗ hbc.equiv)

end LinearMap.IsBaseChangeAlong

namespace AlgebraicGeometry.ChartModuleSystem

variable {Y : Scheme.{u}} {I : Y.AffineChartIndex} (S : ChartModuleSystem I)

/-- The global sections of the restriction of the glued sheaf to `Spec Γ(Y, V c)` are the module
on the chart `c`, linearly over `Γ(Y, V c)`. -/
noncomputable def restrictFromSpecTopEquiv (c : I.ι) :
    (modulesSpecToSheaf.obj (S.sheaf.restrict (I.isAffineOpen c).fromSpec)).presheaf.obj (op ⊤)
      ≃ₗ[Γ(Y, (I.V c).1)] S.M c :=
  ((restrictSectionsEquiv S.sheaf (I.isAffineOpen c) ⊤).trans
    (sectionsCongrSelf S.sheaf ((Scheme.Hom.image_top_eq_opensRange _).trans
      (I.isAffineOpen c).opensRange_fromSpec) (fromSpec_image_le (I.isAffineOpen c) ⊤))).trans
    (S.sectionsEquiv c)

/-- On a chart `c` whose module is free of rank one, the restriction of the glued sheaf to
`Spec Γ(Y, V c)` is isomorphic to the structure sheaf. -/
noncomputable def restrictFromSpecIsoUnit (c : I.ι)
    (e : S.M c ≃ₗ[Γ(Y, (I.V c).1)] Γ(Y, (I.V c).1)) :
    S.sheaf.restrict (I.isAffineOpen c).fromSpec ≅
      SheafOfModules.unit (Spec Γ(Y, (I.V c).1)).ringCatSheaf :=
  (asIso (S.sheaf.restrict (I.isAffineOpen c).fromSpec).fromTildeΓ).symm ≪≫
    (tilde.functor Γ(Y, (I.V c).1)).mapIso
      ((S.restrictFromSpecTopEquiv c).trans e).toModuleIso ≪≫ tildeSelf

/-- If every point lies in a chart whose module is free of rank one, the glued sheaf is an
invertible `𝒪_Y`-module. -/
theorem isInvertibleModule_sheaf
    (h : ∀ y : Y, ∃ c, y ∈ (I.V c).1 ∧ Nonempty (S.M c ≃ₗ[Γ(Y, (I.V c).1)] Γ(Y, (I.V c).1))) :
    Stacks.Ample.IsInvertibleModule Y S.sheaf := by
  refine isInvertibleModule_of_forall_exists_isoUnit_openImmersion S.sheaf fun y => ?_
  obtain ⟨c, hyc, ⟨e⟩⟩ := h y
  refine ⟨_, (I.isAffineOpen c).fromSpec, inferInstance, ?_, ⟨S.restrictFromSpecIsoUnit c e⟩⟩
  rwa [(I.isAffineOpen c).range_fromSpec]

/-- If every chart module is an invertible `Γ(Y, V c)`-module, the glued sheaf is an invertible
`𝒪_Y`-module. -/
theorem isInvertibleModule_sheaf_of_invertible
    [∀ c, Module.Invertible Γ(Y, (I.V c).1) (S.M c)] :
    Stacks.Ample.IsInvertibleModule Y S.sheaf := by
  refine S.isInvertibleModule_sheaf fun y => ?_
  obtain ⟨c, hc⟩ := I.exists_mem y
  obtain ⟨s, hs, hfree⟩ :=
    Module.Invertible.exists_finset_free_localization Γ(Y, (I.V c).1) (S.M c)
  have hcov : (I.V c).1 ≤ ⨆ r : (s : Set Γ(Y, (I.V c).1)), Y.basicOpen r.1 :=
    (I.isAffineOpen c).self_le_iSup_basicOpen_iff.mpr hs
  obtain ⟨⟨r, hrs⟩, hyr⟩ := Opens.mem_iSup.mp (hcov hc)
  obtain ⟨e, he, hye, heW⟩ := I.exists_refines_le hc hyr
  have hunit : IsUnit (I.res he r) := by
    have h₁ : IsUnit (Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op r) :=
      Y.toRingedSpace.isUnit_res_basicOpen r
    have h₂ := (Y.presheaf.map (homOfLE heW).op).hom.isUnit_map h₁
    rwa [← CommRingCat.comp_apply, ← Functor.map_comp] at h₂
  exact ⟨e, hye, (S.isBaseChangeAlong_ρ he).nonempty_linearEquiv_of_free_away r hunit
    (hfree r hrs)⟩

end AlgebraicGeometry.ChartModuleSystem
