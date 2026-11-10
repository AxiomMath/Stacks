module

public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModulePullbackSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRepresentability
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicRepresentableComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QcqsOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedIsoLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTransposeBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceComp
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceSchemeConverse
public import StacksFrontier.Homology.Tor.DerivedTensorFlatBaseChange
public import StacksFrontier.Homology.Tor.IndependenceBaseChange
import all StacksFrontier.Homology.Tor.IndependenceBaseChange

/-!
# The derived pullback of `g_*𝒪_{Y'}` under Tor independence

Let `f : X ⟶ Y` and `g : Y' ⟶ Y` be morphisms of algebraic spaces with `Y` and `Y'` affine, and
suppose `X` and `Y'` are Tor independent over `Y`.  Then the comparison
`Lf^*(g_*𝒪_{Y'}) ⟶ f^*(g_*𝒪_{Y'})` is an isomorphism.  This is the step of the proof of
Stacks 08IR in which Tor independence enters.

On an affine étale chart `Z` of `X`, with `V` an affine chart of `Y` and `W = V ×_Y Y'`, the
module `g_*𝒪_{Y'}` restricted to `V` is the module associated with the `𝒪(V)`-module `𝒪(W)`;
its derived pullback to `Z` is the module associated with `𝒪(W) ⊗^L_{𝒪(V)} 𝒪(Z)`, which is
`𝒪(W) ⊗_{𝒪(V)} 𝒪(Z)` because the two rings are Tor independent over `𝒪(V)`.

## Main results

* `RingTheory.TorIndependence.isIso_comparison_app_restrictScalars_single_of_torIndependent`
* In the namespace `AlgebraicGeometry.Space`:
  * `isIso_smallEtaleDerivedModulePullbackComparison_app_representedAffineAssociated`
  * `isIso_smallEtaleDerivedModulePullbackComparison_app_pushforwardStructure`

## References

* [Stacks Project, Tag 08IR](https://stacks.math.columbia.edu/tag/08IR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward (derivedPushforward pushforwardOnHomotopy
  sourceQuasiIso)

universe u

namespace RingTheory.TorIndependence

/-- **Tor independent extension of scalars of an algebra.**  If `A` and `B` are Tor independent
over `R`, the derived extension of scalars `A ⊗^L_R B` is computed by `A ⊗_R B`: the comparison
of any total left derived extension of scalars along `R → B` is invertible at `A[0]`. -/
theorem isIso_comparison_app_restrictScalars_single_of_torIndependent
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} B)]
    (ψ : R →+* A) (φ : R →+* B)
    (hTor : letI := ψ.toAlgebra; letI := φ.toAlgebra; TorIndependent R A B)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, u, u} φ) :
    IsIso (D.comparison.app ((CochainComplex.restrictScalarsLarge.{u, u, u} ψ).obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)))) := by
  let := ψ.toAlgebra
  let := φ.toAlgebra
  exact @isIso_extendScalarsCounit_app_restrict_of_torIndependent.{u, u, u, u} _ _ _ _ _ _ _ _ _ _
    hTor D.functor D.comparison D.isLeftDerived _
    (CochainComplex.DerivedTensor.kFlat_single_of_flat _)

end RingTheory.TorIndependence

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Represented

variable {U' U : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  (g : U' ⟶ U)

/-- **The comparison of Stacks 06YY on associated modules.**  For `g : U' ⟶ U` with affine
underlying schemes and a complex `K` of `R = Γ(U, 𝒪)`-modules, the comparison
`Lg^*(K^~) ⟶ g^*(K^~)` is invertible as soon as `K ⊗^L_R R' ⟶ K ⊗_R R'` is. -/
theorem isIso_smallEtaleDerivedModulePullbackComparison_app_representedAffineAssociated
    (K : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ)
    (hK : IsIso ((representedAffineDerivedExtension B S hS g).comparison.app K)) :
    IsIso ((smallEtaleDerivedModulePullbackComparison B S hS (representedSpaceMap B S hS g)).app
      ((HomotopyCategory.quotient _ _).obj
        (((representedAffineAssociated B S hS U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K))) := by
  have hfac := Functor.leftDerived_fac_app _ ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (representedAffineDerivedExtension B S hS g).comparison
        (representedAffineDerivedAssociated B S hS U'))
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _
    (representedAffineBaseChangeComparison B S hS g) K
  have h₁ : IsIso (((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (representedAffineDerivedExtension B S hS g).comparison
        (representedAffineDerivedAssociated B S hS U')).app K) := by
    have := hK
    dsimp
    infer_instance
  have h₂ : IsIso ((representedAffineDerivedBaseChangeHom B S hS g).app
      (DerivedCategory.Q.obj K)) := inferInstance
  have h₃ : IsIso ((representedAffineBaseChangeComparison B S hS g).app K) := by
    rw [← hfac]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₂ h₁
  rw [representedAffineBaseChangeComparison_app] at h₃
  have i₁ : IsIso ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).map
      ((representedAffineDerivedAssociatedFactors B S hS U).hom.app K)) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _
      (Iso.isIso_hom ((representedAffineDerivedAssociatedFactors B S hS U).app K))
  have i₂ : IsIso (DerivedCategory.Qh.map
      ((representedAffineHomotopyPullbackIso B S hS g).hom.app K) ≫
      (representedAffineDerivedAssociatedFactors B S hS U').inv.app
        (((ModuleCat.extendScalars.{u, u, u}
          (representedAffineCommRingCatHom B S hS g).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) := by
    have : IsIso (DerivedCategory.Qh.map
      ((representedAffineHomotopyPullbackIso B S hS g).hom.app K)) :=
      @Functor.map_isIso _ _ _ _ _ _ _ _
        (Iso.isIso_hom ((representedAffineHomotopyPullbackIso B S hS g).app K))
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ this
      (Iso.isIso_inv ((representedAffineDerivedAssociatedFactors B S hS U').app _))
  have h₄ := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ i₁ h₃
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ i₂ h₄

end Represented

section Charts

variable {X Y Y' : AlgebraicSpaces B S hS}

/-- **Tor independence on rings of global sections of affine charts.**  If `X` and `Y'` are Tor
independent over `Y`, and `Z`, `W`, `V` are affine étale charts of `X`, `Y'`, `Y` with
morphisms `b : Z ⟶ V` over `f` and `c : W ⟶ V` over `g`, then `𝒪(W)` and `𝒪(Z)` are Tor
independent over `𝒪(V)`. -/
theorem torIndependent_appTop_of_torIndependent (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hTor : TorIndependent X.2 Y'.2 Y.2 f.hom g.hom)
    (Z : SmallEtale B S hS X.1) (W : SmallEtale B S hS Y'.1) (V : SmallEtale B S hS Y.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj Z))]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y'.1).obj W))]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V))]
    (b : (SmallEtale.toOver B S hS X.1).obj Z ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (c : (SmallEtale.toOver B S hS Y'.1).obj W ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (hb : Z.1.hom ≫ f.hom = yoneda.map b ≫ V.1.hom)
    (hc : W.1.hom ≫ g.hom = yoneda.map c ≫ V.1.hom) :
    letI := (representedAffineCommRingCatHom B S hS c).hom.toAlgebra
    letI := (representedAffineCommRingCatHom B S hS b).hom.toAlgebra
    RingTheory.TorIndependence.TorIndependent
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y'.1).obj W), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj Z), ⊤) := by
  have h₁ := torIndependent_comp_of_isEtale_source B S hS f.hom g.hom
    (isEtale_chartToSpace B S hS X Z) (isEtale_chartToSpace B S hS Y' W) hTor
  have e₁ : (chartToSpace B S hS X Z).hom ≫ f.hom =
      (chartSpaceMapOver B S hS b).hom ≫ (chartToSpace B S hS Y V).hom := hb
  have e₂ : (chartToSpace B S hS Y' W).hom ≫ g.hom =
      (chartSpaceMapOver B S hS c).hom ≫ (chartToSpace B S hS Y V).hom := hc
  have h₂ := (congrArg₂ (TorIndependent (chartSpace B S hS X Z).2 (chartSpace B S hS Y' W).2 Y.2)
    e₁ e₂).mp h₁
  have h₃ := (torIndependent_of_comp_isEtale_base B S hS (isEtale_chartToSpace B S hS Y V)
    (chartSpaceMapOver B S hS b) (chartSpaceMapOver B S hS c) h₂).symm
  have h₄ : AlgebraicGeometry.TorIndependent ((BigFppfOver.toScheme B S hS).map c)
      ((BigFppfOver.toScheme B S hS).map b) :=
    torIndependent_scheme_of_torIndependent_yoneda B S hS c b h₃
  have hW : (⊤ : ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Y'.1).obj W)).Opens) ≤
      ((BigFppfOver.toScheme B S hS).map c) ⁻¹ᵁ ⊤ := by simp
  have hZ : (⊤ : ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X.1).obj Z)).Opens) ≤
      ((BigFppfOver.toScheme B S hS).map b) ⁻¹ᵁ ⊤ := by simp
  have hcrit := ((torIndependent_tfae ((BigFppfOver.toScheme B S hS).map c)
    ((BigFppfOver.toScheme B S hS).map b)).out 1 2).mp h₄
  have h₅ := hcrit ⊤ (isAffineOpen_top _) ⊤ (isAffineOpen_top _) ⊤ (isAffineOpen_top _) hW hZ
  have key : ∀ (α : Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V), ⊤) ⟶
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y'.1).obj W), ⊤))
      (β : Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V), ⊤) ⟶
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj Z), ⊤)),
      α = representedAffineCommRingCatHom B S hS c → β = representedAffineCommRingCatHom B S hS b →
      (letI := α.hom.toAlgebra
       letI := β.hom.toAlgebra
       Algebra.TorIndependent
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y'.1).obj W), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj Z), ⊤)) →
      letI := (representedAffineCommRingCatHom B S hS c).hom.toAlgebra
      letI := (representedAffineCommRingCatHom B S hS b).hom.toAlgebra
      RingTheory.TorIndependence.TorIndependent
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y'.1).obj W), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj Z), ⊤) := by
    rintro α β rfl rfl h
    let := (representedAffineCommRingCatHom B S hS c).hom.toAlgebra
    let := (representedAffineCommRingCatHom B S hS b).hom.toAlgebra
    exact (RingTheory.TorIndependence.torIndependent_iff_isZero_tor _ _ _).2 h
  exact key _ _ (Scheme.Hom.appLE_eq_app _) (Scheme.Hom.appLE_eq_app _) h₅

/-- The homotopy-category pullback of `g_*𝒪_{Y'}` along `v` is `v^*g_*𝒪_{Y'}` in degree `0`. -/
private def pullbackPushforwardUnitHomotopyIso (g : Y' ⟶ Y) {T : BigFppfOver B S hS}
    (v : representedAlgebraicSpace B S hS T ⟶ Y) :
    (smallEtalePullbackMapHomotopy B S hS v).obj
        ((smallEtalePushforwardMapHomotopy B S hS g).obj (structureHomotopy B S hS Y')) ≅
      (HomotopyCategory.singleFunctor _ 0).obj
        ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          (X := smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS T))
          (Y := smallEtaleRingedTopos B S hS Y)
          (smallEtaleRingedToposHom B S hS v).toModulesHom).obj
        ((RingedToposHom.pushforwardModules (X := smallEtaleRingedTopos B S hS Y')
          (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS g)).obj
          (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y')))) :=
  haveI : (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
      (X := smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS T))
      (Y := smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposHom B S hS v).toModulesHom).Additive :=
    pullbackModules_smallEtale_additive _
  (HomotopyCategory.quotient _ _).mapIso
    ((_ : _ ⥤ _).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex _ (ComplexShape.up ℤ) 0).app _) ≪≫
      (HomologicalComplex.singleMapHomologicalComplex _ (ComplexShape.up ℤ) 0).app _)

/-- **The module `g_*𝒪_{Y'}` on an affine chart.**  Let `g : Y' ⟶ Y` be affine and let
`v : V ⟶ Y` be étale and representable with `V` affine, with base change `c : W ⟶ V` a morphism
of affine representables.  The restriction of `g_*𝒪_{Y'}` to `V` is the module associated with
the `𝒪(V)`-module `𝒪(W)`. -/
theorem nonempty_pullbackModules_pushforwardModules_unit_iso (g : Y' ⟶ Y)
    (hg : IsAffineHom B S hS g.hom) {T T' : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
    (v : representedAlgebraicSpace B S hS T ⟶ Y) (hv : IsEtale B S hS v.hom)
    (hvr : yoneda.relativelyRepresentable v.hom) (c : T' ⟶ T)
    (v' : representedAlgebraicSpace B S hS T' ⟶ Y')
    (sq : IsPullback v' (representedSpaceMap B S hS c) g v) :
    Nonempty ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS T))
        (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS v).toModulesHom).obj
        ((RingedToposHom.pushforwardModules (X := smallEtaleRingedTopos B S hS Y')
          (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS g)).obj
          (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y'))) ≅
      (representedAffineAssociated B S hS T).obj
        ((ModuleCat.restrictScalars.{u} (representedAffineCommRingCatHom B S hS c).hom).obj
          (ModuleCat.of _ Γ((BigFppfOver.toScheme B S hS).obj T', ⊤)))) := by
  let p := representedSpaceMap B S hS c
  have hp : IsAffineHom B S hS p.hom :=
    isAffineHom_of_isAffineSpace B S hS _ (isAffineSpace_yoneda B S hS _ inferInstance)
      (isAffineSpace_yoneda B S hS _ inferInstance)
  let A := Γ((BigFppfOver.toScheme B S hS).obj T', ⊤)
  let ψ := (representedAffineCommRingCatHom B S hS c).hom
  let MA := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  let O' := SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y')
  let N := (smallEtalePushforwardMapHomotopy B S hS g).obj (structureHomotopy B S hS Y')
  let Pv := Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS T))
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS v).toModulesHom
  let Pg := RingedToposHom.pushforwardModules (X := smallEtaleRingedTopos B S hS Y')
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS g)
  let Lv := smallEtaleDerivedModulePullback B S hS v
  let Rg := derivedModulePushforward B S hS g
  let Rp := derivedModulePushforward B S hS p
  let uf := (pushforwardOnHomotopy (X := smallEtaleRingedTopos B S hS Y')
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS g)).totalRightDerivedUnit
      DerivedCategory.Qh (sourceQuasiIso (smallEtaleRingedTopos B S hS Y'))
  have : Pv.Additive := pullbackModules_smallEtale_additive _
  have := isIso_smallEtaleDerivedModulePullbackComparison_app_of_isEtale B S hS v hv N
  have := isIso_totalRightDerivedUnit_app_structureHomotopy B S hS g hg
  have := isIso_smallEtaleDerivedBaseChangeMap_of_isEtale B S hS g v p v' sq hv hvr
    (structureDerived Y')
  have := isIso_representedAffineTransportUnit B S hS c hp MA
  let eK := pullbackPushforwardUnitHomotopyIso B S hS g v
  let D₁ : (DerivedCategory.singleFunctor _ 0).obj (Pv.obj (Pg.obj O')) ≅
      Lv.obj (DerivedCategory.Qh.obj N) :=
    (DerivedCategory.singleFunctorIsoCompQh _ 0).app (Pv.obj (Pg.obj O')) ≪≫
      DerivedCategory.Qh.mapIso eK.symm ≪≫
      (asIso ((smallEtaleDerivedModulePullbackComparison B S hS v).app N)).symm
  let D₂ : Lv.obj (DerivedCategory.Qh.obj N) ≅ Lv.obj (Rg.obj (structureDerived Y')) :=
    Lv.mapIso (asIso (uf.app (structureHomotopy B S hS Y')) ≪≫
      Rg.mapIso ((DerivedCategory.singleFunctorIsoCompQh _ 0).app O').symm)
  let D₃ : Lv.obj (Rg.obj (structureDerived Y')) ≅
      Rp.obj ((DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS
          (representedAlgebraicSpace B S hS T')))) :=
    asIso (smallEtaleDerivedModuleBaseChangeMap B S hS g v p v' sq.w (structureDerived Y')) ≪≫
      Rp.mapIso (smallEtaleDerivedModulePullbackUnitIso v')
  let D₄ : Rp.obj ((DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS
          (representedAlgebraicSpace B S hS T')))) ≅
      (representedAffineDerivedAssociated B S hS T).obj
        ((ModuleCat.restrictScalars.{u} ψ).mapDerivedCategory.obj MA) :=
    Rp.mapIso (representedAffineDerivedAssociatedSingleUnitIso B S hS T' 0).symm ≪≫
      (asIso (representedAffineTransportUnit B S hS c MA)).symm
  let D₅ : (representedAffineDerivedAssociated B S hS T).obj
        ((ModuleCat.restrictScalars.{u} ψ).mapDerivedCategory.obj MA) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((representedAffineAssociated B S hS T).obj
          ((ModuleCat.restrictScalars.{u} ψ).obj (ModuleCat.of A A))) :=
    (representedAffineDerivedAssociated B S hS T).mapIso
        (((ModuleCat.restrictScalars.{u} ψ).mapDerivedCategorySingleFunctor 0).app
          (ModuleCat.of A A)) ≪≫
      ((representedAffineAssociated B S hS T).mapDerivedCategorySingleFunctor 0).app _
  exact ⟨(DerivedCategory.singleFunctor _ 0).preimageIso (D₁ ≪≫ D₂ ≪≫ D₃ ≪≫ D₄ ≪≫ D₅)⟩

/-- **The comparison of Stacks 06YY at `g_*𝒪_{Y'}` on an affine chart.**  In the situation of
`AlgebraicGeometry.Space.nonempty_pullbackModules_pushforwardModules_unit_iso`, let
`b : Z ⟶ V` be a morphism of affine representables with `𝒪(W)` and `𝒪(Z)` Tor independent over
`𝒪(V)`.  Then `Lb^*(v^*g_*𝒪_{Y'}) ⟶ b^*(v^*g_*𝒪_{Y'})` is an isomorphism. -/
theorem isIso_smallEtaleDerivedModulePullbackComparison_app_pullback_pushforwardStructure
    (g : Y' ⟶ Y) (hg : IsAffineHom B S hS g.hom) {T T' Z : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)]
    (v : representedAlgebraicSpace B S hS T ⟶ Y) (hv : IsEtale B S hS v.hom)
    (hvr : yoneda.relativelyRepresentable v.hom) (c : T' ⟶ T)
    (v' : representedAlgebraicSpace B S hS T' ⟶ Y')
    (sq : IsPullback v' (representedSpaceMap B S hS c) g v) (b : Z ⟶ T)
    (hTor : letI := (representedAffineCommRingCatHom B S hS c).hom.toAlgebra
      letI := (representedAffineCommRingCatHom B S hS b).hom.toAlgebra
      RingTheory.TorIndependence.TorIndependent Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj T', ⊤) Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)) :
    IsIso ((smallEtaleDerivedModulePullbackComparison B S hS (representedSpaceMap B S hS b)).app
      ((smallEtalePullbackMapHomotopy B S hS v).obj
        ((smallEtalePushforwardMapHomotopy B S hS g).obj (structureHomotopy B S hS Y')))) := by
  obtain ⟨eM⟩ := nonempty_pullbackModules_pushforwardModules_unit_iso B S hS g hg v hv hvr c v' sq
  let ψ := (representedAffineCommRingCatHom B S hS c).hom
  let A := Γ((BigFppfOver.toScheme B S hS).obj T', ⊤)
  let K := (CochainComplex.restrictScalarsLarge.{u, u, u} ψ).obj
    ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))
  have hK :=
    RingTheory.TorIndependence.isIso_comparison_app_restrictScalars_single_of_torIndependent
      ψ (representedAffineCommRingCatHom B S hS b).hom hTor
      (representedAffineDerivedExtension B S hS b)
  have h := isIso_smallEtaleDerivedModulePullbackComparison_app_representedAffineAssociated
    B S hS b K hK
  let assoc := representedAffineAssociated B S hS T
  let res := ModuleCat.restrictScalars.{u} ψ
  let eH : (smallEtalePullbackMapHomotopy B S hS v).obj
      ((smallEtalePushforwardMapHomotopy B S hS g).obj (structureHomotopy B S hS Y')) ≅
      (HomotopyCategory.quotient _ _).obj
        ((assoc.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    pullbackPushforwardUnitHomotopyIso B S hS g v ≪≫ (HomotopyCategory.quotient _ _).mapIso
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso eM ≪≫
        ((HomologicalComplex.singleMapHomologicalComplex assoc (ComplexShape.up ℤ) 0).app
          (res.obj (ModuleCat.of A A))).symm ≪≫
        (assoc.mapHomologicalComplex _).mapIso
          ((HomologicalComplex.singleMapHomologicalComplex res (ComplexShape.up ℤ) 0).app
            (ModuleCat.of A A)).symm)
  exact @isIso_app_of_iso_of_isIso_app _ _ _ _ _ _ _ _ _ eH h

/-- **The derived pullback of `g_*𝒪_{Y'}` under Tor independence.**  Let `f : X ⟶ Y` and
`g : Y' ⟶ Y` be morphisms of algebraic spaces with `Y` and `Y'` affine and `X`, `Y'` Tor
independent over `Y`.  Then the comparison `Lf^*(g_*𝒪_{Y'}) ⟶ f^*(g_*𝒪_{Y'})` is an
isomorphism. -/
theorem isIso_smallEtaleDerivedModulePullbackComparison_app_pushforwardStructure (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hY : IsAffineSpace B S hS Y.1) (hY' : IsAffineSpace B S hS Y'.1)
    (hTor : TorIndependent X.2 Y'.2 Y.2 f.hom g.hom) :
    IsIso ((smallEtaleDerivedModulePullbackComparison B S hS f).app
      ((smallEtalePushforwardMapHomotopy B S hS g).obj (structureHomotopy B S hS Y'))) := by
  have hg : IsAffineHom B S hS g.hom := isAffineHom_of_isAffineSpace B S hS g.hom hY' hY
  let hrg := relativelyRepresentable_of_isAffineHom B S hS g hg
  let N := (smallEtalePushforwardMapHomotopy B S hS g).obj (structureHomotopy B S hS Y')
  obtain ⟨T, hT, ⟨e⟩⟩ := hY
  let V : SmallEtale B S hS Y.1 :=
    ⟨CostructuredArrow.mk e.inv, isEtaleChart_of_isIso B S hS T e.inv⟩
  have hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)) :=
    hT
  let W := (smallBaseChange B S hS g hrg).obj V
  have hW' : IsAffine ((SmallEtale.toOver B S hS Y'.1 ⋙ BigFppfOver.toScheme B S hS).obj W) :=
    isAffine_smallBaseChange_obj B S hS g hrg hg V hV
  have hW : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y'.1).obj W)) :=
    hW'
  let c : (SmallEtale.toOver B S hS Y'.1).obj W ⟶ (SmallEtale.toOver B S hS Y.1).obj V :=
    hrg.snd V.1.hom
  have hc : W.1.hom ≫ g.hom = yoneda.map c ≫ V.1.hom := hrg.w V.1.hom
  let v : representedAlgebraicSpace B S hS ((SmallEtale.toOver B S hS Y.1).obj V) ⟶ Y :=
    ObjectProperty.homMk V.1.hom
  let v' : representedAlgebraicSpace B S hS ((SmallEtale.toOver B S hS Y'.1).obj W) ⟶ Y' :=
    ObjectProperty.homMk W.1.hom
  have sq : IsPullback v' (representedSpaceMap B S hS c) g v :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) (hrg.isPullback V.1.hom)
  have hv : IsEtale B S hS v.hom := isEtale_chartToSpace B S hS Y V
  have hvr : yoneda.relativelyRepresentable v.hom := relativelyRepresentable_chartToSpace B S hS Y V
  refine isIso_of_isIso_smallEtaleDerivedModulePullback_chartToSpace B S hS
    (SmallEtale.coversTop_affineCharts B S hS X.1) _ fun ⟨Z, hZ⟩ => ?_
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj Z)) := hZ
  let u : representedAlgebraicSpace B S hS ((SmallEtale.toOver B S hS X.1).obj Z) ⟶ X :=
    ObjectProperty.homMk Z.1.hom
  have hu : IsEtale B S hS u.hom := isEtale_chartToSpace B S hS X Z
  let b : (SmallEtale.toOver B S hS X.1).obj Z ⟶ (SmallEtale.toOver B S hS Y.1).obj V :=
    yoneda.preimage (Z.1.hom ≫ f.hom ≫ e.hom)
  have hb : Z.1.hom ≫ f.hom = yoneda.map b ≫ V.1.hom := by
    change _ = yoneda.map (yoneda.preimage _) ≫ e.inv
    rw [Functor.map_preimage, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hR := torIndependent_appTop_of_torIndependent B S hS f g hTor Z W V b c hb hc
  have hchart := isIso_smallEtaleDerivedModulePullbackComparison_app_pullback_pushforwardStructure
    B S hS g hg v hv hvr c v' sq b hR
  have hw : u ≫ f = representedSpaceMap B S hS b ≫ v := ObjectProperty.hom_ext _ hb
  -- the comparison along `b ≫ v`
  have hbv : IsIso ((smallEtaleDerivedModulePullbackComparison B S hS
      (representedSpaceMap B S hS b ≫ v)).app N) := by
    have e₁ := smallEtaleDerivedModulePullbackCompIso_hom_app_comparison B S hS
      (representedSpaceMap B S hS b) v N
    have := isIso_smallEtaleDerivedModulePullbackComparison_app_of_isEtale B S hS v hv N
    have := hchart
    exact IsIso.of_isIso_fac_left e₁
  -- the comparison along `u ≫ f`
  have huf : IsIso ((smallEtaleDerivedModulePullbackComparison B S hS (u ≫ f)).app N) :=
    hw ▸ hbv
  have e₃ := smallEtaleDerivedModulePullbackCompIso_hom_app_comparison B S hS u f N
  have := isIso_smallEtaleDerivedModulePullbackComparison_app_of_isEtale B S hS u hu
    ((smallEtalePullbackMapHomotopy B S hS f).obj N)
  have := huf
  have key : IsIso ((smallEtaleDerivedModulePullback B S hS u).map
      ((smallEtaleDerivedModulePullbackComparison B S hS f).app N)) :=
    IsIso.of_isIso_fac_right e₃.symm
  exact key

end Charts

end AlgebraicGeometry.Space

end
