module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.ChartSlice
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.BaseChart
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent

/-!
# The model of a represented algebraic space is the model of its scheme

Let `U` be an object of the big fppf site over `S`, with scheme `T`. The equi-universe model of
the small étale ringed site of the algebraic space `h_U`
(`AlgebraicGeometry.Space.smallEtaleModelRingedSite`) and the equi-universe model of the small
étale ringed site of the scheme `T` (`AlgebraicGeometry.SmallEtale.modelSite`) are equivalent
ringed sites: both are models of the small étale site of `T` (Stacks 04M0 for a representable
algebraic space), and the equivalence carries one structure sheaf to the other.

## Main definitions

* `AlgebraicGeometry.Space.reprModelEquiv`: the equivalence of sites.
* `AlgebraicGeometry.Space.reprModelRingMap`: its invertible structure map.

## References

* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- The model of the small étale ringed site of the represented algebraic space `h_U`. -/
abbrev reprSite : RingedSite.{u, u, u} :=
  smallEtaleModelRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)

/-- The scheme of `U`. -/
abbrev reprScheme : Scheme.{u} := (BigFppfOver.toScheme B S hS).obj U

/-- The model of the small étale ringed site of the scheme of `U`. -/
abbrev reprBaseSite : RingedSite.{u, u, u} :=
  SmallEtale.modelSite (associatedBigEtaleSite B) (reprScheme B S hS U) U.left.property

/-- **The model of `h_U` is the model of the scheme of `U`.** -/
def reprModelEquiv : (reprSite B S hS U).C ≌ (reprBaseSite B S hS U).C :=
  (smallEtaleModelEquivalence B S hS (yoneda.obj U)).trans
    ((representedSmallEtaleEquivalence B S hS U).trans
      (SmallEtale.smallModelEquiv (associatedBigEtaleSite B) (reprScheme B S hS U)
        U.left.property))

/-- The functor of `reprModelEquiv` is a dense subsite inclusion. -/
instance reprModelEquiv_functor_isDenseSubsite :
    (reprModelEquiv B S hS U).functor.IsDenseSubsite (reprSite B S hS U).J
      (reprBaseSite B S hS U).J := by
  have h₁ : (smallEtaleModelEquivalence B S hS (yoneda.obj U)).functor.IsDenseSubsite
      (smallEtaleModelTopology B S hS (yoneda.obj U))
      (SmallEtale.topology B S hS (yoneda.obj U)) := inferInstance
  have h₂ : (representedSmallEtaleEquivalence B S hS U).functor.IsDenseSubsite
      (SmallEtale.topology B S hS (yoneda.obj U))
      (representedSchemeSmallEtaleTopology B S hS U) := inferInstance
  have h₃ : (SmallEtale.smallModelEquiv (associatedBigEtaleSite B) (reprScheme B S hS U)
      U.left.property).functor.IsDenseSubsite (representedSchemeSmallEtaleTopology B S hS U)
      (SmallEtale.smallModelTopology (associatedBigEtaleSite B) (reprScheme B S hS U)
        U.left.property) :=
    SmallEtale.smallModelEquiv_functor_isDenseSubsite _ _ _
  have h₂₃ := Equivalence.isDenseSubsite_trans_functor
    (representedSmallEtaleEquivalence B S hS U)
    (SmallEtale.smallModelEquiv (associatedBigEtaleSite B) (reprScheme B S hS U) U.left.property)
    (JA := SmallEtale.topology B S hS (yoneda.obj U))
    (JB := representedSchemeSmallEtaleTopology B S hS U)
    (JC := SmallEtale.smallModelTopology (associatedBigEtaleSite B) (reprScheme B S hS U)
      U.left.property)
  exact @Equivalence.isDenseSubsite_trans_functor _ _ _ _ _ _
    (smallEtaleModelTopology B S hS (yoneda.obj U)) (SmallEtale.topology B S hS (yoneda.obj U))
    (SmallEtale.smallModelTopology (associatedBigEtaleSite B) (reprScheme B S hS U)
      U.left.property) _ _ h₁ h₂₃

/-- The inverse of the represented comparison is a dense subsite inclusion. -/
instance representedSmallEtaleEquivalence_inverse_isDenseSubsite :
    (representedSmallEtaleEquivalence B S hS U).inverse.IsDenseSubsite
      (representedSchemeSmallEtaleTopology B S hS U)
      (SmallEtale.topology B S hS (yoneda.obj U)) := by
  rw [← representedSmallEtaleEquivalence_topology B S hS U]
  exact inferInstanceAs ((representedSmallEtaleEquivalence B S hS U).symm.functor.IsDenseSubsite
    (representedSchemeSmallEtaleTopology B S hS U)
    ((representedSmallEtaleEquivalence B S hS U).symm.inverse.inducedTopology
      (representedSchemeSmallEtaleTopology B S hS U)))

/-- The inverse of `reprModelEquiv` is a dense subsite inclusion. -/
instance reprModelEquiv_inverse_isDenseSubsite :
    (reprModelEquiv B S hS U).inverse.IsDenseSubsite (reprBaseSite B S hS U).J
      (reprSite B S hS U).J := by
  have h₃ : (SmallEtale.smallModelEquiv (associatedBigEtaleSite B) (reprScheme B S hS U)
      U.left.property).symm.functor.IsDenseSubsite
      (SmallEtale.smallModelTopology (associatedBigEtaleSite B) (reprScheme B S hS U)
        U.left.property) (representedSchemeSmallEtaleTopology B S hS U) :=
    SmallEtale.smallModelEquiv_symm_functor_isDenseSubsite' _ _ _
  have h₂ : (representedSmallEtaleEquivalence B S hS U).symm.functor.IsDenseSubsite
      (representedSchemeSmallEtaleTopology B S hS U)
      (SmallEtale.topology B S hS (yoneda.obj U)) :=
    representedSmallEtaleEquivalence_inverse_isDenseSubsite B S hS U
  have h₁ : (smallEtaleModelEquivalence B S hS (yoneda.obj U)).symm.functor.IsDenseSubsite
      (SmallEtale.topology B S hS (yoneda.obj U))
      (smallEtaleModelTopology B S hS (yoneda.obj U)) :=
    smallEtaleModelEquivalence_inverse_isDenseSubsite B S hS _
  have h₃₂ := Equivalence.isDenseSubsite_trans_functor
    (SmallEtale.smallModelEquiv (associatedBigEtaleSite B) (reprScheme B S hS U)
      U.left.property).symm
    (representedSmallEtaleEquivalence B S hS U).symm
    (JA := SmallEtale.smallModelTopology (associatedBigEtaleSite B) (reprScheme B S hS U)
      U.left.property)
    (JB := representedSchemeSmallEtaleTopology B S hS U)
    (JC := SmallEtale.topology B S hS (yoneda.obj U))
  exact @Equivalence.isDenseSubsite_trans_functor _ _ _ _ _ _
    (SmallEtale.smallModelTopology (associatedBigEtaleSite B) (reprScheme B S hS U)
      U.left.property) (SmallEtale.topology B S hS (yoneda.obj U))
    (smallEtaleModelTopology B S hS (yoneda.obj U)) _
    (smallEtaleModelEquivalence B S hS (yoneda.obj U)).symm h₃₂ h₁

/-- The functor of `reprModelEquiv` is continuous. -/
instance reprModelEquiv_functor_isContinuous :
    (reprModelEquiv B S hS U).functor.IsContinuous (reprSite B S hS U).J
      (reprBaseSite B S hS U).J :=
  @Functor.IsDenseSubsite.instIsContinuous _ _ _ _ _ _ _
    (reprModelEquiv_functor_isDenseSubsite B S hS U)

/-- The inverse of `reprModelEquiv` is continuous. -/
instance reprModelEquiv_inverse_isContinuous :
    (reprModelEquiv B S hS U).inverse.IsContinuous (reprBaseSite B S hS U).J
      (reprSite B S hS U).J :=
  @Functor.IsDenseSubsite.instIsContinuous _ _ _ _ _ _ _
    (reprModelEquiv_inverse_isDenseSubsite B S hS U)

/-- **The structure map of `reprModelEquiv`**: the structure sheaf of the model of `h_U` is
carried to the structure sheaf of the model of the scheme of `U`, through the identification of
the structure sheaves of `h_U` and of the scheme (`representedStructureMap`) and the structure
map of the comparison of the small étale site of the scheme with its model. -/
def reprModelRingMap :
    Stacks.SheafOfModules.Tensor.ringSheaf (reprSite B S hS U).O ⟶
      ((reprModelEquiv B S hS U).functor.sheafPushforwardContinuous RingCat.{u}
        (reprSite B S hS U).J (reprBaseSite B S hS U).J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (reprBaseSite B S hS U).O) :=
  (𝟙 _ : Stacks.SheafOfModules.Tensor.ringSheaf (reprSite B S hS U).O ⟶
      ((smallEtaleModelEquivalence B S hS (yoneda.obj U)).functor.sheafPushforwardContinuous
        RingCat.{u} (smallEtaleModelTopology B S hS (yoneda.obj U))
        (SmallEtale.topology B S hS (yoneda.obj U))).obj
          (ringStructureSheaf B S hS (yoneda.obj U))) ≫
    ((smallEtaleModelEquivalence B S hS (yoneda.obj U)).functor.sheafPushforwardContinuous
        RingCat.{u} (smallEtaleModelTopology B S hS (yoneda.obj U))
        (SmallEtale.topology B S hS (yoneda.obj U))).map
      (representedStructureMap B S hS U ≫
        ((representedSmallEtaleEquivalence B S hS U).functor.sheafPushforwardContinuous
          RingCat.{u} (SmallEtale.topology B S hS (yoneda.obj U))
          (representedSchemeSmallEtaleTopology B S hS U)).map
          (SmallEtale.toEtaleHom (associatedBigEtaleSite B) (reprScheme B S hS U)
            U.left.property).fSharpRing)

/-- The identification of the structure sheaves of `h_U` and of its scheme is invertible. -/
instance isIso_representedStructureMap : IsIso (representedStructureMap B S hS U) := by
  have h : (sheafToPresheaf _ RingCat.{u}).map (representedStructureMap B S hS U) = 𝟙 _ := rfl
  have : IsIso ((sheafToPresheaf _ RingCat.{u}).map (representedStructureMap B S hS U)) := by
    rw [h]; exact IsIso.id _
  exact isIso_of_fully_faithful (sheafToPresheaf _ RingCat.{u}) _

/-- The structure map `reprModelRingMap` is an isomorphism. -/
instance isIso_reprModelRingMap : IsIso (reprModelRingMap B S hS U) := by
  have h₁ : IsIso (SmallEtale.toEtaleHom (associatedBigEtaleSite B) (reprScheme B S hS U)
      U.left.property).fSharpRing := SmallEtale.isIso_toEtaleHom_fSharpRing _ _ _
  exact (Iso.refl (Stacks.SheafOfModules.Tensor.ringSheaf (reprSite B S hS U).O) ≪≫
    ((smallEtaleModelEquivalence B S hS (yoneda.obj U)).functor.sheafPushforwardContinuous
        RingCat.{u} (smallEtaleModelTopology B S hS (yoneda.obj U))
        (SmallEtale.topology B S hS (yoneda.obj U))).mapIso
      (@asIso _ _ _ _ (representedStructureMap B S hS U) (isIso_representedStructureMap B S hS U) ≪≫
        ((representedSmallEtaleEquivalence B S hS U).functor.sheafPushforwardContinuous
          RingCat.{u} (SmallEtale.topology B S hS (yoneda.obj U))
          (representedSchemeSmallEtaleTopology B S hS U)).mapIso (@asIso _ _ _ _ _ h₁))).isIso_hom

/-! ### The two transports of modules agree -/

/-- The projection of the model of `h_U` to the small étale site of the scheme of `U`. -/
abbrev reprProj : (reprSite B S hS U).C ⥤
    _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B) (reprScheme B S hS U)
      U.left.property :=
  (smallEtaleModelEquivalence B S hS (yoneda.obj U)).functor ⋙
    (representedSmallEtaleEquivalence B S hS U).functor

/-- `reprModelEquiv` followed by the comparison of the model of the scheme with its small étale
site. -/
abbrev reprProjBack : (reprSite B S hS U).C ⥤
    _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B) (reprScheme B S hS U)
      U.left.property :=
  (reprModelEquiv B S hS U).functor ⋙
    (SmallEtale.smallModelEquiv (associatedBigEtaleSite B) (reprScheme B S hS U)
      U.left.property).inverse

/-- The projection `reprProj` is continuous. -/
instance reprProj_isContinuous :
    (reprProj B S hS U).IsContinuous (reprSite B S hS U).J
      (representedSchemeSmallEtaleTopology B S hS U) :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _ _ (SmallEtale.topology B S hS (yoneda.obj U)) _
    (smallEtaleModelEquivalence_functor_isContinuous B S hS (yoneda.obj U))
    (isContinuous_representedSmallEtaleEquivalence_functor B S hS U)

/-- The functor `reprProjBack` is continuous. -/
instance reprProjBack_isContinuous :
    (reprProjBack B S hS U).IsContinuous (reprSite B S hS U).J
      (representedSchemeSmallEtaleTopology B S hS U) :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _ _ (reprBaseSite B S hS U).J _
    inferInstance (inferInstanceAs ((SmallEtale.smallModelEquiv (associatedBigEtaleSite B)
      (reprScheme B S hS U) U.left.property).inverse.IsContinuous
        (SmallEtale.smallModelTopology (associatedBigEtaleSite B) (reprScheme B S hS U)
          U.left.property) (representedSchemeSmallEtaleTopology B S hS U)))

/-- The two projections agree, through the unit of the comparison of the small étale site of
the scheme with its model. -/
def reprProjIso : reprProjBack B S hS U ≅ reprProj B S hS U :=
  NatIso.ofComponents
    (fun X => ((SmallEtale.smallModelEquiv (associatedBigEtaleSite B) (reprScheme B S hS U)
      U.left.property).unitIso.app ((reprProj B S hS U).obj X)).symm)
    (fun f => ((SmallEtale.smallModelEquiv (associatedBigEtaleSite B) (reprScheme B S hS U)
      U.left.property).unitIso.inv.naturality ((reprProj B S hS U).map f)))

/-- Transport to the model of the scheme followed by the pushforward along `reprModelEquiv` is
the pushforward along `reprProjBack`. -/
def reprModelModulesIso₁ :
    (SmallEtale.modelModulesEquiv (associatedBigEtaleSite B) (reprScheme B S hS U)
        U.left.property).functor ⋙ SheafOfModules.pushforward.{u} (reprModelRingMap B S hS U) ≅
      @SheafOfModules.pushforward.{u} _ _ _ _ (reprSite B S hS U).J
        (representedSchemeSmallEtaleTopology B S hS U) (reprProjBack B S hS U) _
        (SmallEtale.structureSheaf (associatedBigEtaleSite B) (reprScheme B S hS U)
          U.left.property) (reprProjBack_isContinuous B S hS U)
        (reprModelRingMap B S hS U ≫
          ((reprModelEquiv B S hS U).functor.sheafPushforwardContinuous RingCat.{u}
            (reprSite B S hS U).J (reprBaseSite B S hS U).J).map
            (SmallEtale.fromEtaleHom (associatedBigEtaleSite B) (reprScheme B S hS U)
              U.left.property).fSharpRing) :=
  @SheafOfModules.pushforwardComp _ _ _ _ _ _ _ _ _ _ _ _ (reprModelRingMap B S hS U) _ _ _
    (inferInstanceAs ((SmallEtale.smallModelEquiv (associatedBigEtaleSite B)
      (reprScheme B S hS U) U.left.property).inverse.IsContinuous
        (SmallEtale.smallModelTopology (associatedBigEtaleSite B) (reprScheme B S hS U)
          U.left.property) (representedSchemeSmallEtaleTopology B S hS U)))
    (SmallEtale.fromEtaleHom (associatedBigEtaleSite B) (reprScheme B S hS U)
      U.left.property).fSharpRing

/-- The represented transport followed by transport to the model of `h_U` is the pushforward
along `reprProj`. -/
def reprModelModulesIso₄ :
    @SheafOfModules.pushforward.{u} _ _ _ _ (reprSite B S hS U).J
        (representedSchemeSmallEtaleTopology B S hS U) (reprProj B S hS U)
        (Stacks.SheafOfModules.Tensor.ringSheaf (reprSite B S hS U).O)
        (SmallEtale.structureSheaf (associatedBigEtaleSite B) (reprScheme B S hS U)
          U.left.property) (reprProj_isContinuous B S hS U)
        ((𝟙 _ : Stacks.SheafOfModules.Tensor.ringSheaf (reprSite B S hS U).O ⟶
          ((smallEtaleModelEquivalence B S hS (yoneda.obj U)).functor.sheafPushforwardContinuous
            RingCat.{u} (smallEtaleModelTopology B S hS (yoneda.obj U))
            (SmallEtale.topology B S hS (yoneda.obj U))).obj
              (ringStructureSheaf B S hS (yoneda.obj U))) ≫
          ((smallEtaleModelEquivalence B S hS (yoneda.obj U)).functor.sheafPushforwardContinuous
          RingCat.{u} (smallEtaleModelTopology B S hS (yoneda.obj U))
          (SmallEtale.topology B S hS (yoneda.obj U))).map (representedStructureMap B S hS U)) ≅
      representedModulePushforward B S hS U ⋙
        (modulesEquivModelModules B S hS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B S hS U)).functor :=
  (@SheafOfModules.pushforwardComp _ _ _ _ _ _ _ _ _ _ _
    (smallEtaleModelEquivalence_functor_isContinuous B S hS (yoneda.obj U)) (𝟙 _) _ _ _
    (isContinuous_representedSmallEtaleEquivalence_functor B S hS U)
    (representedStructureMap B S hS U)).symm

/-- **The two transports of modules from the small étale site of the scheme of `U` to the model
of `h_U` agree.** -/
def reprModelModulesIso :
    (SmallEtale.modelModulesEquiv (associatedBigEtaleSite B) (reprScheme B S hS U)
        U.left.property).functor ⋙ SheafOfModules.pushforward.{u} (reprModelRingMap B S hS U) ≅
      representedModulePushforward B S hS U ⋙
        (modulesEquivModelModules B S hS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B S hS U)).functor :=
  reprModelModulesIso₁ B S hS U ≪≫
    @SheafOfModules.pushforwardCongr _ _ _ _ _ _ _ _ _ (reprProjBack_isContinuous B S hS U) _ _
      (by ext : 2; rfl) ≪≫
    (@SheafOfModules.pushforwardNatIso _ _ _ _ _ _ _ _ _ _ (reprProjBack_isContinuous B S hS U)
      (reprProj_isContinuous B S hS U) _ (reprProjIso B S hS U)).symm ≪≫
    reprModelModulesIso₄ B S hS U

/-! ### Duality charts on the model of a represented algebraic space -/

/-- The model of `h_U` has fibre products. -/
instance reprSite_hasPullbacks : HasPullbacks (reprSite B S hS U).C :=
  inferInstanceAs (HasPullbacks (SmallEtaleModel B S hS (yoneda.obj U)))

variable [_root_.AlgebraicGeometry.IsAffine (reprScheme B S hS U)]
  [_root_.AlgebraicGeometry.IsNoetherian (reprScheme B S hS U)]

/-- **The bounded duality chart on the model of `h_U`**, transported from the model of the
scheme of `U` along `reprModelEquiv` (Stacks 08JP (1)). -/
def reprBoundedChart (ω : RingedSite.SchemeStdDerived (reprScheme B S hS U))
    (hω : letI : HasDerivedCategory (reprScheme B S hS U).Modules := HasDerivedCategory.standard _
      Stacks.Duality.IsDualizingComplex ω) :
    RingedSite.DualityChart (reprSite B S hS U)
      ((RingedSite.siteEquivDerivedEquivalence (reprModelEquiv B S hS U)
        (reprModelRingMap B S hS U)).functor.obj
          ((SmallEtale.chartFunctor (associatedBigEtaleSite B) (reprScheme B S hS U)
            U.left.property).derived.obj ω))
      RingedSite.ChartClass.bounded :=
  (SmallEtale.boundedBaseDualityChart (associatedBigEtaleSite B) (reprScheme B S hS U)
    U.left.property ω hω).transport

end AlgebraicGeometry.Space
