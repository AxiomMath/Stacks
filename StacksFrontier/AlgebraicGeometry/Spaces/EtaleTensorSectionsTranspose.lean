module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleTensorSingleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedPushforwardPullbackTensorIso

/-!
# The transpose of `c_U` and the identification `ψ_U`

In the setting of `AlgebraicGeometry.Space.etaleTensorSectionsBaseChangeMap`, the base change map
`c_U : RΓ_R(U, Lj^*K) ⊗^𝐋_R R₀ ⟶ RΓ_{R₀}(U₀, Lj₀^*(F[0]))` is the adjoint of `RΓ_R(U, Lj^*φ)`
followed by the identification

`ψ_U : RΓ_R(U, Lj^*((i_*F)[0])) ⟶ RΓ_{R₀}(U₀, Lj₀^*(F[0]))|_R`.

This file names `ψ_U`, records the transposition identity
`RΓ_R(U, Lj^*φ) ≫ ψ_U = η ≫ c_U|_R` (`η` the unit of derived extension and restriction of scalars),
and proves that its factors are isomorphisms: the inverse of the projection formula at the unit
([Stacks, Tag 08IN]), the identification `ψ_i` at a quasi-coherent object such as `Rj_*𝒪_U` (the
projection formula of the affine `i`), and `π'_F` (`isIso_etaleTensorSectionsProjection`).

## Main definitions

* `AlgebraicGeometry.Space.etaleTensorSectionsIdentification`: `ψ_U`.

## Main results

* `CategoryTheory.transposeUnitMap_transpose`: the abstract transposition identity.
* `AlgebraicGeometry.Space.etaleTensorSectionsBaseChangeMap_transpose`.
* `AlgebraicGeometry.Space.isIso_tensorSingleSectionsNatTrans_app`: `ψ_i` is invertible at a
  quasi-coherent object.
* `CategoryTheory.isIso_transposeUnitIdentification`: the identification is invertible when its
  middle factor and `π'` are.
* `AlgebraicGeometry.Space.isIso_etaleTensorSectionsIdentification`: `ψ_U` is invertible.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {𝒳 𝒰 𝒜 𝒜₀ : Type*} [Category 𝒳] [Category 𝒰] [Category 𝒜] [Category 𝒜₀]
  (TX : 𝒳 ⥤ 𝒳 ⥤ 𝒳) (GA : 𝒳 ⥤ 𝒜) (Lj : 𝒳 ⥤ 𝒰) (GU : 𝒰 ⥤ 𝒜) {ext : 𝒜 ⥤ 𝒜₀} {res : 𝒜₀ ⥤ 𝒜}
  (adj : ext ⊣ res) (Q : 𝒳 ⥤ 𝒜₀) {G K P : 𝒳} (φ : K ⟶ G) (ψ : TX.flip.obj G ⋙ GA ⟶ Q ⋙ res)
  (π : TX.obj P ⋙ GA ⟶ Lj ⋙ GU) (hπ : IsIso (π.app G)) {Y : 𝒜₀} (π' : Q.obj P ⟶ Y)

/-- The map `GU(Lj G) ⟶ res Y` whose composite with `GU(Lj φ)` is adjoint to `transposeUnitMap`:
the inverse of `π` at `G`, then `ψ` at `P` and `π'`. -/
def transposeUnitIdentification : GU.obj (Lj.obj G) ⟶ res.obj Y :=
  @inv _ _ _ _ _ hπ ≫ ψ.app P ≫ res.map π'

/-- **The transposition identity**: the map whose adjoint is `transposeUnitMap` is the unit of
the adjunction followed by the restriction of `transposeUnitMap`. -/
theorem transposeUnitMap_transpose :
    GU.map (Lj.map φ) ≫ transposeUnitIdentification TX GA Lj GU Q ψ π hπ π' =
      adj.unit.app _ ≫ res.map (transposeUnitMap TX GA Lj GU adj Q φ ψ π hπ π') :=
  ((adj.homEquiv _ _).apply_symm_apply _).symm.trans
    (Adjunction.homEquiv_unit _ _ _ (transposeUnitMap TX GA Lj GU adj Q φ ψ π hπ π'))

/-- `transposeUnitIdentification` is invertible when `ψ` at `P` and `π'` are. -/
theorem isIso_transposeUnitIdentification (hψ : IsIso (ψ.app P)) (hπ' : IsIso π') :
    IsIso (transposeUnitIdentification TX GA Lj GU Q ψ π hπ π') :=
  IsIso.comp_isIso' (@IsIso.inv_isIso _ _ _ _ _ hπ) (IsIso.comp_isIso' hψ (Functor.map_isIso _ _))

end CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {T T₀ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)]
  {X X₀ U U₀ : AlgebraicSpaces B S hS}
  (h : X ⟶ ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
  (h₀ : X₀ ⟶ ⟨yoneda.obj T₀, isAlgebraicSpace_yoneda B S hS T₀⟩)
  (g₀ : T₀ ⟶ T) (i₀ : X₀ ⟶ X) (w₀ : i₀ ≫ h = h₀ ≫ representedSpaceMap B S hS g₀)
  (hi₀ : IsAffineHom B S hS i₀.hom)
  (F : Modules.{u, u} B S hS X₀.1 X₀.2) (hF : F.IsQuasicoherentOnSite)
  (j : U ⟶ X) (j₀ : U₀ ⟶ X₀) (i' : U₀ ⟶ U) (wU : i' ≫ j = j₀ ≫ i₀)
  (hjqc : IsQuasiCompact B S hS j.hom) (hjqs : IsQuasiSeparated B S hS j.hom)
  (hG : QcohDerived B S hS X
    ((DerivedCategory.singleFunctor _ 0).obj ((modulePushforward B S hS i₀).obj F)))
  {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
  (φ : K ⟶ (DerivedCategory.singleFunctor _ 0).obj ((modulePushforward B S hS i₀).obj F))

/-- **The identification `ψ_U : RΓ_R(U, Lj^*((i_*F)[0])) ⟶ RΓ_{R₀}(U₀, Lj₀^*(F[0]))|_R`** whose
composite with `RΓ_R(U, Lj^*φ)` is adjoint to `c_U`: the inverse of the projection formula at the
unit ([Stacks, Tag 08IN]), `ψ_i` at `Rj_*𝒪_U` and `π'_F`. -/
def etaleTensorSectionsIdentification :=
  transposeUnitIdentification (smallEtaleDerivedTensor B S hS X)
    (derivedModulePushforward B S hS h ⋙ representedAffineDerivedSections B S hS T)
    (smallEtaleDerivedModulePullback B S hS j)
    (derivedModulePushforward B S hS (j ≫ h) ⋙ representedAffineDerivedSections B S hS T)
    (res := (ModuleCat.restrictScalars
      (representedAffineCommRingCatHom B S hS g₀).hom).mapDerivedCategory)
    (P := (derivedModulePushforward B S hS j).obj (structureDerived U))
    (smallEtaleDerivedModulePullback B S hS i₀ ⋙
      (smallEtaleDerivedTensor B S hS X₀).flip.obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X₀)) 0).obj F) ⋙
      (derivedModulePushforward B S hS h₀ ⋙ representedAffineDerivedSections B S hS T₀))
    (tensorSingleSectionsNatTrans B S hS h h₀ g₀ i₀ w₀ hi₀ F hF)
    (sectionsProjectionUnitNatTrans T j h)
    (isIso_sectionsProjectionUnitNatTrans_app T j h hjqc hjqs _ hG)
    (etaleTensorSectionsProjection B S hS h₀ i₀ F j j₀ i' wU)

/-- **`RΓ_R(U, Lj^*φ) ≫ ψ_U = η ≫ c_U|_R`**: `c_U` is the adjoint of `RΓ_R(U, Lj^*φ) ≫ ψ_U`. -/
theorem etaleTensorSectionsBaseChangeMap_transpose :
    (derivedModulePushforward B S hS (j ≫ h) ⋙ representedAffineDerivedSections B S hS T).map
        ((smallEtaleDerivedModulePullback B S hS j).map φ) ≫
      etaleTensorSectionsIdentification B S hS h h₀ g₀ i₀ w₀ hi₀ F hF j j₀ i' wU hjqc hjqs hG =
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
        (representedAffineCommRingCatHom B S hS g₀).hom).unit.app _ ≫
      (ModuleCat.restrictScalars
          (representedAffineCommRingCatHom B S hS g₀).hom).mapDerivedCategory.map
        (etaleTensorSectionsBaseChangeMap B S hS h h₀ g₀ i₀ w₀ hi₀ F hF j j₀ i' wU hjqc hjqs hG
          φ) :=
  transposeUnitMap_transpose (smallEtaleDerivedTensor B S hS X)
    (derivedModulePushforward B S hS h ⋙ representedAffineDerivedSections B S hS T)
    (smallEtaleDerivedModulePullback B S hS j)
    (derivedModulePushforward B S hS (j ≫ h) ⋙ representedAffineDerivedSections B S hS T)
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
      (representedAffineCommRingCatHom B S hS g₀).hom)
    (smallEtaleDerivedModulePullback B S hS i₀ ⋙
      (smallEtaleDerivedTensor B S hS X₀).flip.obj ((DerivedCategory.singleFunctor _ 0).obj F) ⋙
      (derivedModulePushforward B S hS h₀ ⋙ representedAffineDerivedSections B S hS T₀))
    φ (tensorSingleSectionsNatTrans B S hS h h₀ g₀ i₀ w₀ hi₀ F hF)
    (sectionsProjectionUnitNatTrans T j h)
    (isIso_sectionsProjectionUnitNatTrans_app T j h hjqc hjqs _ hG)
    (etaleTensorSectionsProjection B S hS h₀ i₀ F j j₀ i' wU)

include hF in
/-- `ψ_i` is invertible at a quasi-coherent `E`: it is the projection formula of the affine `i`,
between the identifications `(i_*F)[0] ≅ Ri_*(F[0])` and `RΓ_R(X, Ri_* -) ≅ RΓ_{R₀}(X₀, -)`. -/
theorem isIso_tensorSingleSectionsNatTrans_app
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : QcohDerived B S hS X E) :
    IsIso ((tensorSingleSectionsNatTrans B S hS h h₀ g₀ i₀ w₀ hi₀ F hF).app E) := by
  have := isIso_smallEtaleProjectionFormulaMapSnd B S hS i₀
    (isQuasiCompact_of_isAffineHom_hom i₀ hi₀)
    (isQuasiSeparated_of_isAffineHom_hom i₀ hi₀) E hE
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X₀)) 0).obj F)
    (qcohDerived_singleFunctor_of_isQuasicoherentOnSite B S hS F hF)
  exact IsIso.comp_isIso' (Iso.isIso_hom ((derivedModulePushforward B S hS h ⋙
      representedAffineDerivedSections B S hS T).mapIso
        (((smallEtaleDerivedTensor B S hS X).flip.mapIso
          (derivedModulePushforwardSingleIsoOfIsAffineHom B S hS i₀ hi₀ F hF).symm).app E)))
    (IsIso.comp_isIso' (Iso.isIso_hom ((derivedModulePushforward B S hS h ⋙
        representedAffineDerivedSections B S hS T).mapIso (@asIso _ _ _ _
        ((smallEtaleProjectionFormulaSndNatTrans i₀ ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X₀)) 0).obj F)).app E) this)))
      (Iso.isIso_hom ((affineBaseDerivedSectionsPushforwardIso B S hS g₀ h h₀ i₀ w₀).app _)))

include hF hi₀ in
/-- **`ψ_U` is an isomorphism** for `U₀ = U ×_X X₀` cartesian, `j` and `j₀` quasi-compact and
quasi-separated, and `U`, `X₀` Tor independent over `X`: its three factors are, by
`isIso_sectionsProjectionUnitNatTrans_app`, `isIso_tensorSingleSectionsNatTrans_app` at
`Rj_*𝒪_U` and `isIso_etaleTensorSectionsProjection`.

The abstract lemma is applied with every argument given, as in the definition of
`AlgebraicGeometry.Space.etaleTensorSectionsIdentification`: inferring them from the hypothesis on
`ψ_i` splits its codomain differently, and the kernel cannot then reconcile the two terms. -/
theorem isIso_etaleTensorSectionsIdentification (sq : IsPullback i' j₀ j i₀)
    (hj₀qc : IsQuasiCompact B S hS j₀.hom) (hj₀qs : IsQuasiSeparated B S hS j₀.hom)
    (hTor : TorIndependent U.2 X₀.2 X.2 j.hom i₀.hom) :
    IsIso (etaleTensorSectionsIdentification B S hS h h₀ g₀ i₀ w₀ hi₀ F hF j j₀ i' sq.w hjqc hjqs
      hG) := by
  have hO : QcohDerived B S hS U (structureDerived U) :=
    qcohDerived_singleFunctor_structureModule (X := U.1) (hX := U.2)
  exact isIso_transposeUnitIdentification (smallEtaleDerivedTensor B S hS X)
    (derivedModulePushforward B S hS h ⋙ representedAffineDerivedSections B S hS T)
    (smallEtaleDerivedModulePullback B S hS j)
    (derivedModulePushforward B S hS (j ≫ h) ⋙ representedAffineDerivedSections B S hS T)
    (res := (ModuleCat.restrictScalars
      (representedAffineCommRingCatHom B S hS g₀).hom).mapDerivedCategory)
    (P := (derivedModulePushforward B S hS j).obj (structureDerived U))
    (smallEtaleDerivedModulePullback B S hS i₀ ⋙
      (smallEtaleDerivedTensor B S hS X₀).flip.obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X₀)) 0).obj F) ⋙
      (derivedModulePushforward B S hS h₀ ⋙ representedAffineDerivedSections B S hS T₀))
    (tensorSingleSectionsNatTrans B S hS h h₀ g₀ i₀ w₀ hi₀ F hF)
    (sectionsProjectionUnitNatTrans T j h)
    (isIso_sectionsProjectionUnitNatTrans_app T j h hjqc hjqs _ hG)
    (etaleTensorSectionsProjection B S hS h₀ i₀ F j j₀ i' sq.w)
    (isIso_tensorSingleSectionsNatTrans_app B S hS h h₀ g₀ i₀ w₀ hi₀ F hF
      ((derivedModulePushforward B S hS j).obj (structureDerived U))
      (qcohDerived_derivedModulePushforward_obj B S hS j hjqc hjqs (structureDerived U) hO))
    (isIso_etaleTensorSectionsProjection B S hS h₀ i₀ F hF j j₀ i' hjqc hjqs sq hj₀qc hj₀qs hTor)

end AlgebraicGeometry.Space

end
