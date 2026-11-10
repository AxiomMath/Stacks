module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.SchemeArtinRees
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.ReducedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerAffineChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleChartGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsOfPullback

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

open Stacks.Cohomology.FormalFunctions

/-- Restriction to an open subscheme, read through the inclusion of the open subscheme, lands in a
power of the extension of a base ideal exactly when the restriction to the open does. -/
theorem restrict_mem_pow_map_of_ι_appTop_mem (A : Type u) [CommRing A] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of A)) (I : Ideal A) (n : ℕ) (U : Y.Opens) (y : Γ(Y, ⊤))
    (h : U.ι.appTop y ∈ Ideal.map ((U.ι.appTop).hom.comp (baseRingHom A g)) I ^ n) :
    Y.presheaf.map (homOfLE le_top : U ⟶ ⊤).op y ∈
      Ideal.map ((Y.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom.comp
        (baseRingHom A g)) I ^ n := by
  have key : ∀ W W' : Y.Opens, W = W' →
      Y.presheaf.map (homOfLE le_top : W ⟶ ⊤).op y ∈
        Ideal.map ((Y.presheaf.map (homOfLE le_top : W ⟶ ⊤).op).hom.comp
          (baseRingHom A g)) I ^ n →
      Y.presheaf.map (homOfLE le_top : W' ⟶ ⊤).op y ∈
        Ideal.map ((Y.presheaf.map (homOfLE le_top : W' ⟶ ⊤).op).hom.comp
          (baseRingHom A g)) I ^ n := by
    rintro W _ rfl h
    exact h
  exact key _ _ U.ι_image_top h

end AlgebraicGeometry

/-- An element of `J • R` lies in `J`. -/
theorem Ideal.mem_of_mem_smul_top {R : Type*} [CommRing R] (J : Ideal R) (x : R)
    (h : x ∈ J • (⊤ : Submodule R R)) : x ∈ J :=
  Submodule.smul_le.2 (fun _r hr y _ => J.mul_mem_right y hr) h

namespace AlgebraicGeometry.Space

open Stacks.SheafOfModules.Tensor (ringSheaf)

variable (A : Type u) [CommRing A] {B : BigFppfSite.{u}} {hA : B.Contains (Spec (.of A))}

/-- Global functions of a represented algebraic space are the global functions of the representing
scheme, as `A`-algebras. -/
def globalFunctionsYonedaAlgEquiv (V : BigFppfOver B (Spec (.of A)) hA) :
    letI := siteObjSectionsAlgebra A V
    globalFunctions B (Spec (.of A)) hA (yoneda.obj V) ≃ₐ[A]
      Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj V, ⊤) :=
  letI := siteObjSectionsAlgebra A V
  AlgEquiv.ofRingEquiv (f := globalFunctionsYonedaRingEquiv B (Spec (.of A)) hA V) fun _ => rfl

/-- Global sections of the structure module of a represented algebraic space, evaluated at the
identity chart: the global functions of the representing scheme. -/
def unitSectionsYonedaLinearEquiv (V : BigFppfOver B (Spec (.of A)) hA) :
    letI := siteObjSectionsAlgebra A V
    (sectionsOverBase A B hA (yonedaSpace B (Spec (.of A)) hA V).1
      (yonedaSpace B (Spec (.of A)) hA V).2).obj (SheafOfModules.unit _) ≃ₗ[A]
      Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj V, ⊤) :=
  letI := siteObjSectionsAlgebra A V
  (unitSectionsLinearEquivGlobalFunctions A (yonedaSpace B (Spec (.of A)) hA V)).trans
    (globalFunctionsYonedaAlgEquiv A V).toLinearEquiv

/-- `unitSectionsYonedaLinearEquiv` sends a global section to its value at the identity chart. -/
theorem unitSectionsYonedaLinearEquiv_apply (V : BigFppfOver B (Spec (.of A)) hA)
    (s : (sectionsOverBase A B hA (yonedaSpace B (Spec (.of A)) hA V).1
      (yonedaSpace B (Spec (.of A)) hA V).2).obj (SheafOfModules.unit _)) :
    letI := siteObjSectionsAlgebra A V
    unitSectionsYonedaLinearEquiv A V s = s.1 (op (idEtaleChart B (Spec (.of A)) hA V)) := rfl

/-- **Artin-Rees for the structure module of a scheme proper over a Noetherian ring**, read on
the small étale site of the algebraic space it represents. -/
theorem hasSectionsArtinRees_unit_yoneda [IsNoetherianRing A] (V : BigFppfOver B (Spec (.of A)) hA)
    (hV : _root_.AlgebraicGeometry.IsProper (B.inclusion.map V.hom)) (I : Ideal A) :
    HasSectionsArtinRees A (yonedaSpace B (Spec (.of A)) hA V)
      (baseIdealSheaf A (yonedaSpace B (Spec (.of A)) hA V) I) I (SheafOfModules.unit _) := by
  let := siteObjSectionsAlgebra A V
  let Y := (BigFppfOver.toScheme B (Spec (.of A)) hA).obj V
  let g : Y ⟶ Spec (.of A) := B.inclusion.map V.hom
  have : _root_.AlgebraicGeometry.IsProper g := hV
  obtain ⟨c, hc⟩ := exists_mem_pow_smul_top_of_forall_affineOpens A g I
  intro m
  refine ⟨m + c, fun s hs => ?_⟩
  let e := unitSectionsYonedaLinearEquiv A V
  have hy : ∀ U : Y.affineOpens, Y.presheaf.map (homOfLE le_top : U.1 ⟶ ⊤).op (e s) ∈
      (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I g).ideal U ^ (m + c) := by
    intro U
    let idC := idEtaleChart B (Spec (.of A)) hA V
    let O := openChart B (Spec (.of A)) hA (yoneda.obj V) idC U.1
    have hOaff : IsAffine ((SmallEtale.toOver B (Spec (.of A)) hA (yoneda.obj V) ⋙
        BigFppfOver.toScheme B (Spec (.of A)) hA).obj O) := U.2
    have hsO := (mem_sectionsKer_iff A (yonedaSpace B (Spec (.of A)) hA V) _ s).1 hs (op O)
    rw [idealPowerMultiple_eq_idealPowSubmodule] at hsO
    have hsO' := (chartSubmodule_idealPowSubmodule_eq_of_isQuasicoherentOnSite B (Spec (.of A)) hA
      (yoneda.obj V) (yonedaSpace B (Spec (.of A)) hA V).2
      (baseIdealSheaf A (yonedaSpace B (Spec (.of A)) hA V) I) (m + c)
      (SheafOfModules.unit _) inferInstance (isQuasicoherentOnSite_baseIdealSheaf A _ I) O hOaff).le
      hsO
    have hJ : chartSectionIdeal B (Spec (.of A)) hA (yoneda.obj V)
        (yonedaSpace B (Spec (.of A)) hA V).2
        (baseIdealSheaf A (yonedaSpace B (Spec (.of A)) hA V) I) O =
          Ideal.map (chartBaseRingHom A (yonedaSpace B (Spec (.of A)) hA V) O) I :=
      baseIdealSheaf_obj_of_isAffine A (yonedaSpace B (Spec (.of A)) hA V) I O hOaff
    rw [hJ] at hsO'
    let x : chartSectionsRing B (Spec (.of A)) hA (yonedaSpace B (Spec (.of A)) hA V) O :=
      s.1 (op O)
    have hsO4 : x ∈
        Ideal.map (chartBaseRingHom A (yonedaSpace B (Spec (.of A)) hA V) O) I ^ (m + c) :=
      @Ideal.mem_of_mem_smul_top _
        (chartSectionsRing_commRing B (Spec (.of A)) hA (yonedaSpace B (Spec (.of A)) hA V) O)
        _ x hsO'
    have hincl :=
      toScheme_map_toOver_map_openChartInclusion B (Spec (.of A)) hA (yoneda.obj V) idC U.1
    have hx : x = U.1.ι.appTop (e s) := by
      have h := (s.2 (openChartInclusion B (Spec (.of A)) hA (yoneda.obj V) idC U.1).op).symm
      refine h.trans ?_
      change (Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of A)) hA).map
        ((SmallEtale.toOver B (Spec (.of A)) hA (yoneda.obj V)).map
          (openChartInclusion B (Spec (.of A)) hA (yoneda.obj V) idC U.1))).op).hom (e s) = _
      rw [hincl]
      rfl
    have hφ : chartBaseRingHom A (yonedaSpace B (Spec (.of A)) hA V) O =
        (U.1.ι.appTop).hom.comp (Stacks.Cohomology.FormalFunctions.baseRingHom A g) := by
      ext a
      have h := Γ_map_algebraMap_siteObj A
        ((SmallEtale.toOver B (Spec (.of A)) hA (yoneda.obj V)).map
          (openChartInclusion B (Spec (.of A)) hA (yoneda.obj V) idC U.1)) a
      rw [hincl] at h
      exact h.symm
    rw [hx, hφ] at hsO4
    have := restrict_mem_pow_map_of_ι_appTop_mem A g I (m + c) U.1 (e s) hsO4
    rwa [Stacks.Cohomology.FormalFunctions.baseIdealSheaf_ideal,
      Stacks.Cohomology.FormalFunctions.baseIdeal, Ideal.map_map]
  have h1 := hc (m + c) (by omega) (e s) hy
  rw [Nat.add_sub_cancel] at h1
  have h1' : e s ∈ I ^ m • (⊤ : Submodule A Γ(Y, ⊤)) := h1
  have h2 := Submodule.mem_map_of_mem (f := e.symm.toLinearMap) h1'
  rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range] at h2
  have h3 : e.symm.toLinearMap (e s) = s := e.symm_apply_apply s
  rwa [h3] at h2

end AlgebraicGeometry.Space
