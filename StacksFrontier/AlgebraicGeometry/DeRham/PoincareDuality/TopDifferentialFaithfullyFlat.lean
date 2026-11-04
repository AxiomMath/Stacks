module

public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.TopDifferentialSpreadOut
public import StacksFrontier.Homology.ExtendScalars.IndependentUniverses
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose

/-!
# Vanishing of the de Rham differential on cohomology descends along faithfully flat maps

Let `A ⟶ A'` be a faithfully flat ring map, `X` a quasi-compact separated scheme over `A` and
`X' = X ×_A A'`. If the de Rham differential `Ω^e_{X'/A'} ⟶ Ω^{e+1}_{X'/A'}` induces zero on
`H^{q+1}(X', -)`, then so does `Ω^e_{X/A} ⟶ Ω^{e+1}_{X/A}` on `H^{q+1}(X, -)`. On the
alternating Čech complexes of a finite affine covering the second is the base change of the first,
flat base change commutes with cohomology, and a faithfully flat base change reflects vanishing
of morphisms of modules.

## Main results

* `ModuleCat.eq_zero_of_extendScalars_map_eq_zero`: a faithfully flat extension of scalars
  reflects vanishing of morphisms.
* `AlgebraicGeometry.TopDegreeDifferential.rightDerived_map_deRham_d_eq_zero_of_faithfullyFlat`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.Leray (sectionsFunctor)

universe u

namespace ModuleCat

/-- **A faithfully flat extension of scalars reflects vanishing of morphisms**: if `g ⊗ A'` is
zero then the image of `g`, whose base change is the image of `g ⊗ A'`, is zero. -/
theorem eq_zero_of_extendScalars_map_eq_zero {A A' : Type u} [CommRing A] [CommRing A']
    (φ : A →+* A') (hφ : φ.FaithfullyFlat) {M N : ModuleCat.{u} A} (g : M ⟶ N)
    (h : (extendScalars.{u, u, u} φ).map g = 0) : g = 0 := by
  let M' := ModuleCat.of A (LinearMap.range g.hom)
  let π : M ⟶ M' := ModuleCat.ofHom g.hom.rangeRestrict
  let ι : M' ⟶ N := ModuleCat.ofHom (LinearMap.range g.hom).subtype
  have hfac : π ≫ ι = g := by ext; rfl
  have : Epi π := (ModuleCat.epi_iff_surjective _).2 (LinearMap.surjective_rangeRestrict _)
  have : Mono ι := (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
  let F := extendScalars.{u, u, u} φ
  have : PreservesFiniteLimits F := extendScalars_preservesFiniteLimits_of_flat φ hφ.flat
  have : PreservesFiniteColimits F := extendScalars_preservesFiniteColimits φ
  have h2 : F.map ι = 0 := (cancel_epi (F.map π)).1 (by rwa [comp_zero, ← F.map_comp, hfac])
  have h3 : IsZero (F.obj M') := by
    have : Mono (0 : F.obj M' ⟶ F.obj N) := h2 ▸ (inferInstance : Mono (F.map ι))
    exact IsZero.of_mono_zero (F.obj M') (F.obj N)
  rw [← hfac, (isZero_of_isZero_extendScalars φ hφ M' h3).eq_of_tgt π 0, zero_comp]

end ModuleCat

namespace AlgebraicGeometry.TopDegreeDifferential

open Stacks.Cech

/-- **Vanishing of the de Rham differential on cohomology descends along faithfully flat base
change.** For `A ⟶ A'` faithfully flat, `X` quasi-compact and separated over `A` and
`X' = X ×_A A'`, if `d : Ω^e_{X'/A'} ⟶ Ω^{e+1}_{X'/A'}` induces zero on `H^{q+1}(X', -)` then
`d : Ω^e_{X/A} ⟶ Ω^{e+1}_{X/A}` induces zero on `H^{q+1}(X, -)`. -/
theorem rightDerived_map_deRham_d_eq_zero_of_faithfullyFlat {A A' : Type u} [CommRing A]
    [CommRing A'] (φ : A →+* A') (hφ : φ.FaithfullyFlat) {X X' : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of A')) (g : X' ⟶ X)
    (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) [IsSeparated f] [CompactSpace X]
    (e q : ℕ)
    (h : ((sectionsFunctor X'.carrier ⊤).rightDerived (q + 1)).map
        ((SheafOfModules.toSheaf _).map (f'.deRhamComplex.d e (e + 1))) = 0) :
    ((sectionsFunctor X.carrier ⊤).rightDerived (q + 1)).map
        ((SheafOfModules.toSheaf _).map (f.deRhamComplex.d e (e + 1))) = 0 := by
  classical
  obtain ⟨s, hs⟩ :=
    Stacks.AlgebraicGeometry.Tag01PFAffineExtend.exists_finset_affineOpens_iSup_eq_top (X := X)
  let : LinearOrder s := linearOrderOfSTO WellOrderingRel
  let U : s → X.Opens := fun i => i.1.1
  have hU : (⊤ : X.Opens) = ⨆ i, U i := hs.symm.trans iSup_subtype'
  have hUaff : ∀ i, IsAffineOpen (U i) := fun i => i.1.2
  have : IsSeparated f' := MorphismProperty.of_isPullback hsq inferInstance
  have : IsAffineHom g := MorphismProperty.of_isPullback hsq.flip inferInstance
  have hU' : (⊤ : X'.Opens) = ⨆ i, g ⁻¹ᵁ U i := by
    rw [← Scheme.Hom.preimage_iSup, ← hU, Scheme.Hom.preimage_top]
  rw [rightDerived_map_deRham_d_eq_zero_iff_homologyMap f U hU hUaff e q]
  rw [rightDerived_map_deRham_d_eq_zero_iff_homologyMap f' (fun i => g ⁻¹ᵁ U i) hU'
    (fun i => (hUaff i).preimage g) e q] at h
  have h2 := (homologyMap_extendScalars_deRham_eq_zero_iff φ f f' g hsq U hUaff e (q + 1)).2 h
  let F := ModuleCat.extendScalars.{u, u, u} φ
  have : F.PreservesHomology := extendScalars_preservesHomology_of_flat.{u, u} φ hφ.flat
  let c := alternatingCechModulePush f U (Scheme.Hom.deRhamPresheafD f e)
    (Scheme.Hom.deRhamPresheafD_app_smul f e)
  let E := Functor.mapHomologicalComplexHomologyIso F (ComplexShape.up ℕ) (q + 1)
  have h3 : E.hom.app _ ≫ F.map (HomologicalComplex.homologyMap c (q + 1)) = 0 :=
    (E.hom.naturality c).symm.trans ((congrArg (· ≫ E.hom.app _) h2).trans zero_comp)
  exact ModuleCat.eq_zero_of_extendScalars_map_eq_zero φ hφ _
    ((Iso.cancel_iso_hom_left (E.app _) _ _).1 (h3.trans comp_zero.symm))

end AlgebraicGeometry.TopDegreeDifferential
