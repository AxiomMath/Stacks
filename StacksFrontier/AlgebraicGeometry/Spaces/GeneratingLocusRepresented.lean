module

public import StacksFrontier.AlgebraicGeometry.Ample.DescentStep
public import StacksFrontier.AlgebraicGeometry.NonvanishingOpen.CokernelSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeIdEtaleChartTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedInvertibleTrivial
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionGeneratingLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportGeometricStalkCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedInjective

/-!
# The generating locus of a section on a representable algebraic space

Let `U` be an object of the big fppf site over `S`, with underlying scheme `T`, and let `𝓜` be a
quasi-coherent module on the small étale site of the algebraic space `yoneda.obj U`, with a
global section `s`.  Restricting to the Zariski site of `T` along the identity chart
(`AlgebraicGeometry.Space.idChartRestriction`) gives a quasi-coherent `𝒪_T`-module `𝓜_T` with a
global section `s_T`.  When `𝓜_T` is invertible, the generating locus of `s`
(`AlgebraicGeometry.Space.sectionGeneratingLocus`) is, under the identification of the points of
`yoneda.obj U` with those of `T` (Stacks 03BX), the nonvanishing locus `T_{s_T}` of
Stacks 01CY.

The generating locus is the complement of the support of the cokernel `𝓒` of `s : 𝒪 ⟶ 𝓜`.  By
Descent, Proposition 03DX (2), the associated-module functor and the restriction to the Zariski
site are inverse on quasi-coherent modules, so `𝓒` is the associated module of the cokernel `𝓒_T`
of `s_T : 𝒪_T ⟶ 𝓜_T`, the associated-module functor being a left adjoint.  The support of `𝓒` is
the support of `𝓒_T` by Stacks 07TY, and that is the complement of `T_{s_T}`
(`Stacks.SheafOfModules.supp_cokernel_unitHomEquiv_symm`).

## Main definitions

* `AlgebraicGeometry.Space.idChartRestrictionFunctor`: the restriction to the Zariski site along
  the identity chart, as a functor.
* `AlgebraicGeometry.Space.idChartSection`: the section `s_T` of `𝓜_T`.

## Main results

* `AlgebraicGeometry.Space.mem_sectionGeneratingLocus_iff_mem_nonvanishingLocus`: the generating
  locus is the nonvanishing locus of the restricted section.

## References

* [Stacks Project, Tag 0D2W](https://stacks.math.columbia.edu/tag/0D2W)
* [Stacks Project, Tag 07TY](https://stacks.math.columbia.edu/tag/07TY)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (U : BigFppfOver B S hS)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
/-- The abelian structure of the modules on `yoneda.obj U`, supplied directly rather than by
instance search; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedInjective`. -/
noncomputable local instance (priority := 10000) representedModulesAbelian :
    Abelian (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) :=
  smallEtaleModulesAbelian (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)


/-- The restriction of modules on the small étale site of `yoneda.obj U` to the Zariski site of
the scheme underlying `U` along the identity chart, as a functor; its value at `𝓜` is
`AlgebraicGeometry.Space.idChartRestriction`. -/
noncomputable def idChartRestrictionFunctor :
    Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) ⥤
      ((BigFppfOver.toScheme B S hS).obj U).Modules :=
  (representedSmallEtaleModuleEquivalence B S hS U).inverse ⋙
    _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property

/-- The value of `AlgebraicGeometry.Space.idChartRestrictionFunctor` at `𝓜` is
`AlgebraicGeometry.Space.idChartRestriction` of `𝓜`. -/
theorem idChartRestrictionFunctor_obj
    (M : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) :
    (idChartRestrictionFunctor B S hS U).obj M = idChartRestriction B S hS U M := rfl

/-- The section `s_T` of the restriction `𝓜_T` of `𝓜` to the Zariski site along the identity
chart induced by a global section `s` of `𝓜`. -/
noncomputable def idChartSection
    (M : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (s : M.sections) : (idChartRestriction B S hS U M).sections :=
  (idChartRestriction B S hS U M).unitHomEquiv
    ((idChartRestrictionUnitIso B S hS U (isAlgebraicSpace_yoneda B S hS U)).inv ≫
      (idChartRestrictionFunctor B S hS U).map (M.unitHomEquiv.symm s))

/-- **The support of the cokernel of a section on a representable algebraic space is the support
of the cokernel of the restricted section**, under the identification of points of Stacks 03BX. -/
theorem mem_supportOfSheaf_cokernel_iff
    (M : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hM : M.IsQuasicoherentOnSite) (s : M.sections) (t : (BigFppfOver.toScheme B S hS).obj U) :
    (pointsEquivScheme B S hS U).symm t ∈ supportOfSheaf B S hS (yoneda.obj U)
        ((SheafOfModules.toSheaf _).obj (cokernel (C := Modules.{u, u} B S hS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B S hS U)) (M.unitHomEquiv.symm s))) ↔
      t ∈ SheafOfModules.supp (cokernel
        ((idChartRestriction B S hS U M).unitHomEquiv.symm (idChartSection B S hS U M s))) := by
  let T := (BigFppfOver.toScheme B S hS).obj U
  let E := representedSmallEtaleModuleEquivalence B S hS U
  let A := _root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B) T
    U.left.property
  let Rm := _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B) T
    U.left.property
  let adj := _root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction
    (associatedBigEtaleSite B) T U.left.property
  let G : T.Modules ⥤ Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) :=
    A ⋙ E.functor
  let R := idChartRestrictionFunctor B S hS U
  have hqcE : ∀ X : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U),
      X.IsQuasicoherentOnSite → (E.inverse.obj X).IsQuasicoherentOnSite := fun X hX =>
    (isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS U (E.inverse.obj X)).1
      (SheafOfModules.IsQuasicoherentOnSite.of_iso (E.counitIso.app X).symm hX)
  have hqcR : ∀ X : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U),
      X.IsQuasicoherentOnSite → SheafOfModules.IsQuasicoherent (R.obj X) := fun X hX =>
    _root_.AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule (associatedBigEtaleSite B)
      T U.left.property _ (hqcE X hX)
  have hc : ∀ X : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U),
      X.IsQuasicoherentOnSite → IsIso (adj.counit.app (E.inverse.obj X)) := fun X hX =>
    _root_.AlgebraicGeometry.SmallEtale.isIso_counit (associatedBigEtaleSite B) T U.left.property
      _ (hqcE X hX) (hqcR X hX)
  let c : ∀ X : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U),
      X.IsQuasicoherentOnSite → (G.obj (R.obj X) ≅ X) := fun X hX =>
    E.functor.mapIso (@asIso _ _ _ _ _ (hc X hX)) ≪≫ E.counitIso.app X
  have hcnat : ∀ {X Y : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)}
      (hX : X.IsQuasicoherentOnSite) (hY : Y.IsQuasicoherentOnSite) (f : X ⟶ Y),
      G.map (R.map f) ≫ (c Y hY).hom = (c X hX).hom ≫ f := by
    intro X Y hX hY f
    have h1 : A.map (Rm.map (E.inverse.map f)) ≫ adj.counit.app (E.inverse.obj Y) =
        adj.counit.app (E.inverse.obj X) ≫ E.inverse.map f :=
      adj.counit.naturality (E.inverse.map f)
    have h2 : E.functor.map (E.inverse.map f) ≫ E.counitIso.hom.app Y =
        E.counitIso.hom.app X ≫ f :=
      E.counitIso.hom.naturality f
    show E.functor.map (A.map (Rm.map (E.inverse.map f))) ≫
        (E.functor.map (adj.counit.app (E.inverse.obj Y)) ≫ E.counitIso.hom.app Y) =
      (E.functor.map (adj.counit.app (E.inverse.obj X)) ≫ E.counitIso.hom.app X) ≫ f
    rw [← Category.assoc, ← E.functor.map_comp, h1, E.functor.map_comp, Category.assoc, h2]
    exact (Category.assoc _ _ _).symm
  have hO : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)).O)).IsQuasicoherentOnSite :=
    SheafOfModules.isQuasicoherentOnSite_unit _
  set φ := M.unitHomEquiv.symm s with hφ
  let ε := idChartRestrictionUnitIso B S hS U (isAlgebraicSpace_yoneda B S hS U)
  let φσ := (idChartRestriction B S hS U M).unitHomEquiv.symm (idChartSection B S hS U M s)
  have hφσ' : φσ = ε.inv ≫ R.map φ := Equiv.symm_apply_apply _ _
  have hRφ : R.map φ = ε.hom ≫ φσ := by
    rw [hφσ']
    exact (Iso.hom_inv_id_assoc ε _).symm
  have : SheafOfModules.IsQuasicoherent (idChartRestriction B S hS U M) := hqcR M hM
  have h𝓒 : SheafOfModules.IsQuasicoherent (cokernel φσ) :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel φσ
  have : G.IsLeftAdjoint := inferInstanceAs (A ⋙ E.functor).IsLeftAdjoint
  have : PreservesColimitsOfSize.{0, 0} G :=
    (Adjunction.ofIsLeftAdjoint G).leftAdjoint_preservesColimits
  have : G.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint G
  let I0 : cokernel (C := Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) (G.map (R.map φ)) ≅ cokernel φ :=
    cokernel.mapIso (C := Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) (G.map (R.map φ)) φ (c _ hO) (c M hM)
      (hcnat hO hM φ)
  have hGφ : G.map (R.map φ) = G.map ε.hom ≫ G.map φσ :=
    (congrArg (fun f => G.map f) hRφ).trans (G.map_comp _ _)
  have hepi : Epi (G.map ε.hom) :=
    @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom (G.mapIso ε))
  let I2 : cokernel (C := Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) (G.map (R.map φ)) ≅
      cokernel (C := Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) (G.map φσ) :=
    cokernelIsoOfEq (C := Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) hGφ ≪≫
    @cokernelEpiComp (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) _ _ _ _ _ (G.map ε.hom) (G.map φσ) hepi _
  let I3 : cokernel (C := Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) (G.map φσ) ≅ G.obj (cokernel φσ) :=
    (PreservesCokernel.iso G φσ).symm
  let I : cokernel (C := Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) φ ≅ G.obj (cokernel φσ) := I0.symm ≪≫ I2 ≪≫ I3
  have hsupp : supportOfSheaf B S hS (yoneda.obj U) ((SheafOfModules.toSheaf _).obj
        (cokernel (C := Modules.{u, u} B S hS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B S hS U)) φ)) =
      supportOfSheaf B S hS (yoneda.obj U) ((SheafOfModules.toSheaf _).obj
        (G.obj (cokernel φσ))) :=
    supportOfSheaf_eq_of_iso B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ I
  rw [hsupp]
  have hGq : (G.obj (cokernel φσ)).IsQuasicoherentOnSite :=
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj ⟨cokernel φσ, h𝓒⟩).property
  have h07 := supp_restrictToChart_eq_preimage_supportOfSheaf_of_isQuasicoherent B S hS
    ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ (idEtaleChart B S hS U)
    (G.obj (cokernel φσ))
  let I4 : restrictToChart B S hS (isAlgebraicSpace_yoneda B S hS U) (G.obj (cokernel φσ))
      (idEtaleChart B S hS U) ≅ cokernel φσ :=
    restrictToChartIsoIdChartRestriction B S hS U (G.obj (cokernel φσ)) ≪≫
      Rm.mapIso (E.unitIso.app (A.obj (cokernel φσ))).symm ≪≫
      (@asIso _ _ _ _ _ (_root_.AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent
        (associatedBigEtaleSite B) T U.left.property ⟨cokernel φσ, h𝓒⟩)).symm
  have h4 := SheafOfModules.supp_eq_of_iso I4
  have key : t ∈ SheafOfModules.supp (cokernel φσ) ↔
      (pointsEquivScheme B S hS U).symm t ∈ supportOfSheaf B S hS (yoneda.obj U)
        ((SheafOfModules.toSheaf _).obj (G.obj (cokernel φσ))) :=
    (Iff.of_eq (congrArg (t ∈ ·) h4.symm)).trans ((Iff.of_eq (congrArg (t ∈ ·) h07)).trans
      (Set.mem_preimage.trans (Iff.of_eq (congrArg (fun x => x ∈ supportOfSheaf B S hS
        (yoneda.obj U) ((SheafOfModules.toSheaf _).obj (G.obj (cokernel φσ))))
        (congrFun (pointsMap_id B S hS (yoneda.obj U)) ((pointsEquivScheme B S hS U).symm t))))))
  exact key.symm

attribute [local instance] modulesMonoidalCategory in
/-- **The restriction of an invertible module to the identity chart is invertible.**  If
`𝓜 ⊗ 𝓝 ≅ 𝒪` on `yoneda.obj U` then `𝓜_T ⊗ 𝓝_T ≅ (𝓜 ⊗ 𝓝)_T ≅ 𝒪_T`, the restriction being
compatible with tensor products of quasi-coherent modules
(`AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartTensorIso`) and `𝓝` being
quasi-coherent as an invertible module. -/
theorem isInvertible_idChartRestriction
    (M : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hM : IsInvertibleModule ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ M) :
    Stacks.SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace.presheaf
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace).property
      (idChartRestriction B S hS U M) := by
  obtain ⟨N, ⟨ψ⟩⟩ := (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit M).mp hM
  have hN : IsInvertibleModule ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ N :=
    Stacks.SheafOfModules.Invertible.isInvertible_of_tensor_iso_unit _ _
      ((Stacks.SheafOfModules.Invertible.tensorProductBraiding _ _ N M) ≪≫ ψ)
  have hMq := isQuasicoherentOnSite_of_isInvertibleModule
    ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ M hM
  have hNq := isQuasicoherentOnSite_of_isInvertibleModule
    ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ N hN
  let e1 : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O)).obj
        (idChartRestriction B S hS U M, idChartRestriction B S hS U N) ≅
      SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf :=
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O)).mapIso
        (Iso.prod (restrictToChartSchemeIdEtaleChartIso B S hS U M).symm
          (restrictToChartSchemeIdEtaleChartIso B S hS U N).symm)) ≪≫
    (restrictToChartSchemeIdEtaleChartTensorIso B S hS U M N hMq hNq).symm ≪≫
    (restrictToChartSchemeIdEtaleChartIso B S hS U (M ⊗ N)) ≪≫
    (idChartRestrictionFunctor B S hS U).mapIso
      (modulesTensorObjIso B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) M N ≪≫ ψ) ≪≫
    idChartRestrictionUnitIso B S hS U (isAlgebraicSpace_yoneda B S hS U)
  exact Stacks.SheafOfModules.Invertible.isInvertible_of_tensor_iso_unit _ _ e1

/-- **The generating locus of a section on a representable algebraic space is the nonvanishing
locus of the restricted section.**  For an invertible module `𝓜` on `yoneda.obj U` and a global
section `s`, a point of the scheme `T` underlying `U` lies in the generating locus of `s`, read
through Stacks 03BX, exactly when it lies in the nonvanishing locus `T_{s_T}` of Stacks 01CY. -/
theorem mem_sectionGeneratingLocus_iff_mem_nonvanishingLocus
    (M : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hM : IsInvertibleModule ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ M)
    (s : M.sections) (t : (BigFppfOver.toScheme B S hS).obj U) :
    (pointsEquivScheme B S hS U).symm t ∈ sectionGeneratingLocus B S hS M s ↔
      t ∈ Stacks.SheafOfModules.nonvanishingLocus
        (X := ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace)
        (idChartRestriction B S hS U M) (idChartSection B S hS U M s) := by
  have := isInvertible_idChartRestriction B S hS U M hM
  have h1 := mem_supportOfSheaf_cokernel_iff B S hS U M
    (isQuasicoherentOnSite_of_isInvertibleModule ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
      M hM) s t
  have h2 := Stacks.SheafOfModules.supp_cokernel_unitHomEquiv_symm
    (X := ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace)
    (idChartRestriction B S hS U M) (idChartSection B S hS U M s)
  rw [mem_sectionGeneratingLocus_iff]
  refine (not_congr h1).trans ?_
  exact (not_congr (Iff.of_eq (congrArg (t ∈ ·) h2))).trans not_not

end AlgebraicGeometry.Space

end
