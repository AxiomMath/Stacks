module

public import StacksFrontier.AlgebraicGeometry.Quot.ContractionClosedFibreFieldDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.FieldFibreRelativeDimensionOneVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatDerivedPushforwardFibreSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineTorAmplitude
public import StacksFrontier.Homology.Perfect.LocalSplittingDegreeZero

/-!
# The derived fibres of `RΓ(U, Rf_*𝒪_X)` vanish outside `[0, 1]` in relative dimension one

Let `U` be an affine object of the big fppf site over an arbitrary base scheme `S`, with ring of
functions `A`, and let `f : X ⟶ U` be a proper, flat morphism of finite presentation of algebraic
spaces with relative dimension at most one. Put `K = RΓ(U, Rf_*𝒪_X) ∈ D(A)`. For every prime
`𝔭 ⊂ A` and every `n ∉ [0, 1]`,

`Hⁿ(K ⊗^L_A κ(𝔭)) = 0`.

Indeed, with `X' = X ×_U Spec κ(𝔭)` and `f' : X' ⟶ Spec κ(𝔭)`, cohomology and base change
(Stacks 0CTM, part (1)) and the affine base change `Lg^*Φ ≅ Φ'(- ⊗^L_A κ(𝔭))` identify
`Φ'(K ⊗^L_A κ(𝔭))` with `Rf'_*𝒪_{X'}`, which lies in `D^{[0, 1]}`: in `D^{≥ 0}` because `Rf'_*` is
left t-exact, and in `D^{≤ 1}` because `X'` is a proper scheme of dimension at most one over a
field (`AlgebraicGeometry.Space.isLE_one_derivedModulePushforward_structureModule_of_subsingleton`,
with the relative dimension of `f'` read off that of `f` by Stacks 04NS). The associated-module
functor `Φ'` is exact and faithful.

This is the fibrewise input of Stacks 068V in the proof of the vanishing of the obstruction groups
of the Picard stack, Stacks 0DPJ.

## Main results

* `StacksDraft.Perfect.isZero_homologyFunctor_obj_totalDerivedExtensionScalars_comp_ringEquiv`:
  vanishing of `Hⁿ(K ⊗^L_A A')` is kept by a further base change along a ring isomorphism.
* `Space.isZero_homology_residueField_derivedSections_of_hasRelativeDimensionLE_one`: the derived
  fibres of `RΓ(U, Rf_*𝒪_X)` vanish outside `[0, 1]` in relative dimension one.

## Implementation notes

No declaration here carries a `stacks` attribute: these are steps of the proof of Stacks 0DPJ.
The derived categories are those of the standard model, fixed by `letI` inside the statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

namespace StacksDraft.Perfect

/-- **Vanishing of `Hⁿ` of a derived base change `- ⊗^L_A A'` is kept by a further base change
along a ring isomorphism `A' ≅ L`.** -/
theorem isZero_homologyFunctor_obj_totalDerivedExtensionScalars_comp_ringEquiv
    {A A' L : Type u} [CommRing A] [CommRing A'] [CommRing L] (φ : A →+* A') (e : A' ≃+* L)
    (K : letI := HasDerivedCategory.standard (ModuleCat.{u} A)
      DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    (h : letI := HasDerivedCategory.standard (ModuleCat.{u} A)
      letI := HasDerivedCategory.standard (ModuleCat.{u} A')
      IsZero ((DerivedCategory.homologyFunctor _ n).obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          φ).functor.obj K))) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} A)
    letI := HasDerivedCategory.standard (ModuleCat.{u} L)
    IsZero ((DerivedCategory.homologyFunctor _ n).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        ((e : A' →+* L).comp φ)).functor.obj K)) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := HasDerivedCategory.standard (ModuleCat.{u} A')
  let := HasDerivedCategory.standard (ModuleCat.{u} L)
  let ψ : A' →+* L := e
  let G := ModuleCat.extendScalars.{u, u, u} ψ
  have : PreservesFiniteLimits G :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _ (RingHom.Flat.of_bijective e.bijective)
  let Dφ :=
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} φ).functor
  refine IsZero.of_iso (G.map_isZero h) ?_
  exact (DerivedCategory.homologyFunctor _ n).mapIso
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp φ ψ).app K).symm ≪≫
    (DerivedCategory.homologyFunctor _ n).mapIso
      ((Dualizing.totalDerivedExtensionScalarsIsoExtendScalars ψ).app (Dφ.obj K)) ≪≫
    (G.mapDerivedCategoryHomologyIso n).app (Dφ.obj K)

end StacksDraft.Perfect

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The derived fibres of `RΓ(U, Rf_*𝒪_X)` vanish outside `[0, 1]`.** Let `U` be an affine
object of the big fppf site with ring of functions `A`, and `f : X ⟶ U` proper, flat, of finite
presentation and of relative dimension at most one. Then for every prime `𝔭` of `A` and every
`n ∉ [0, 1]`, `Hⁿ(RΓ(U, Rf_*𝒪_X) ⊗^L_A κ(𝔭)) = 0`. -/
theorem isZero_homology_residueField_derivedSections_of_hasRelativeDimensionLE_one
    (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    {X : AlgebraicSpaces B S hS} (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (hd : HasRelativeDimensionLE 1 B S hS f.hom)
    (p : Ideal Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) [p.IsPrime] (n : ℤ)
    (hn : n < 0 ∨ 1 < n) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    letI := HasDerivedCategory.standard (ModuleCat.{u} p.ResidueField)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} p.ResidueField) n).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap _ p.ResidueField)).functor.obj
        ((representedAffineDerivedSections B S hS U).obj ((derivedModulePushforward B S hS f).obj
          ((DerivedCategory.singleFunctor _ 0).obj (structureModule X)))))) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
  let := HasDerivedCategory.standard (ModuleCat.{u} p.ResidueField)
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS U))
  let g := residueFieldSiteMapOfIsAffine B S hS U p
  let U' := residueFieldSiteObject B hS (specGlobalSectionsPoint B S hS U p)
    (contains_spec_residueField_specGlobalSectionsPoint B S hS U p)
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS (yoneda.obj U')
    (isAlgebraicSpace_yoneda B S hS U'))
  let gY := representedSpaceMap B S hS g
  let X' := pullback f gY
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X'.1 X'.2)
  let := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
    ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
    ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩))
  let f' : X' ⟶ _ := pullback.snd f gY
  let i : X' ⟶ X := pullback.fst f gY
  have sq : IsPullback i f' f gY := IsPullback.of_hasPullback f gY
  obtain ⟨-, hf', -, hd'⟩ := curveFamilyConditions_of_isPullback B S hS (m := g)
    (AlgebraicSpaces.isPullback_hom B S hS sq) X.2 X'.2 hfl hf hfp hd
  have : Subsingleton ((BigFppfOver.toScheme B S hS).obj U') :=
    inferInstanceAs (Subsingleton (Spec ((specGlobalSectionsOver B S hS U).left.residueField
      (specGlobalSectionsPoint B S hS U p))))
  have : _root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U') :=
    inferInstanceAs (_root_.AlgebraicGeometry.IsLocallyNoetherian
      (Spec ((specGlobalSectionsOver B S hS U).left.residueField
        (specGlobalSectionsPoint B S hS U p))))
  -- `Rf'_*𝒪_{X'}` lies in `D^{[0, 1]}`
  let F' := (derivedModulePushforward B S hS f').obj
    ((DerivedCategory.singleFunctor _ 0).obj (structureModule X'))
  have hLE : F'.IsLE 1 :=
    isLE_one_derivedModulePushforward_structureModule_of_subsingleton f' hf' hd'
  have hGE : F'.IsGE 0 := isGE_derivedModulePushforward_obj_of_isGE B S hS f' _ 0 inferInstance
  have hZ : IsZero ((DerivedCategory.homologyFunctor _ n).obj F') := by
    rcases hn with hn | hn
    · exact DerivedCategory.isZero_of_isGE F' 0 n hn
    · exact DerivedCategory.isZero_of_isLE F' 1 n hn
  -- `Φ'(K ⊗^L_A A') ≅ Rf'_*𝒪_{X'}`
  let E := (derivedModulePushforward B S hS f).obj
    ((DerivedCategory.singleFunctor _ 0).obj (structureModule X))
  let K := (representedAffineDerivedSections B S hS U).obj E
  let adjU := representedAffineDerivedAdjunction B S hS U
  have hqcE := qcohDerived_derivedModulePushforward_structureModule B S hS U f hfp.2.1 hfp.2.2
  have hcounit : IsIso (adjU.counit.app E) :=
    isIso_representedAffineDerivedAdjunction_counit_app B S hS U E hqcE
  let β := representedAffineDerivedBaseChangeIso B S hS g
  let Lg := smallEtaleDerivedModulePullback B S hS gY
  have hbc := (isPerfect_derivedModulePushforward_and_isIso_baseChange_of_isFlat f hf hfl hfp _
    (isPerfect_unit X)).2 gY f' i sq
  let bc := smallEtaleDerivedModuleBaseChangeMap B S hS f gY f' i sq.w
    ((DerivedCategory.singleFunctor _ 0).obj (structureModule X))
  let D := representedAffineDerivedExtension B S hS g
  let chain : (representedAffineDerivedAssociated B S hS U').obj (D.functor.obj K) ≅ F' :=
    (β.app K).symm ≪≫ Lg.mapIso (@asIso _ _ _ _ _ hcounit) ≪≫ @asIso _ _ _ _ bc hbc ≪≫
      (derivedModulePushforward B S hS f').mapIso
        (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) i)
  have hZΦ : IsZero ((DerivedCategory.homologyFunctor _ n).obj
      ((representedAffineDerivedAssociated B S hS U').obj (D.functor.obj K))) :=
    hZ.of_iso ((DerivedCategory.homologyFunctor _ n).mapIso chain)
  have hZa : IsZero ((representedAffineAssociated B S hS U').obj
      ((DerivedCategory.homologyFunctor _ n).obj (D.functor.obj K))) :=
    hZΦ.of_iso ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (representedAffineAssociated B S hS U') n).app _).symm
  have hD : IsZero ((DerivedCategory.homologyFunctor _ n).obj (D.functor.obj K)) :=
    (isZero_representedAffineAssociated_obj_iff B S hS U' _).mp hZa
  have h :=
    StacksDraft.Perfect.isZero_homologyFunctor_obj_totalDerivedExtensionScalars_comp_ringEquiv
      _ (residueFieldSiteObjectRingEquivOfIsAffine B S hS U p) K n hD
  rwa [residueFieldSiteObjectRingEquivOfIsAffine_comp] at h

end AlgebraicGeometry.Space

end
