module

public import StacksFrontier.AlgebraicGeometry.Spaces.SupportGeometricStalkCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChartZariskiEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.RepresentedProperOver
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupport
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.Basic

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# Supports on a represented algebraic space and on the representing scheme

For an object `U` of the big fppf site and a quasi-coherent module `M` on the algebraic space
`h_U`, the support of the Zariski restriction of `M` along the identity chart is the support of
`M` read through the points of the scheme
(`AlgebraicGeometry.Space.C1573.supp_chartZariskiModule_idEtaleChart`), and, for a morphism
`q : U ⟶ V` such that `h_q` is locally of finite type, `M` has support proper over `h_V` exactly
when that restriction has support proper over `V`
(`AlgebraicGeometry.Space.C1573.hasProperSupport_yoneda_map_iff`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The support of the Zariski restriction along the identity chart is the support of the
module.** -/
theorem C1573.supp_chartZariskiModule_idEtaleChart (U : BigFppfOver B S hS)
    (M : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hM : M.IsQuasicoherentOnSite) :
    SheafOfModules.supp ((chartZariskiModule B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
        (idEtaleChart B S hS U)).obj M) =
      (pointsEquivScheme B S hS U).symm ⁻¹'
        supportOfSheaf B S hS (yoneda.obj U) ((SheafOfModules.toSheaf _).obj M) := by
  have := hM
  have e := restrictToChartIsoChartSchemeModule B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ M hM (idEtaleChart B S hS U) ≪≫
    (chartZariskiModuleQcohIso B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
      (idEtaleChart B S hS U)).app ⟨M, hM⟩
  refine (SheafOfModules.supp_eq_of_iso e).symm.trans
    ((supp_restrictToChart_eq_preimage_supportOfSheaf_of_isQuasicoherent B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ (idEtaleChart B S hS U) M).trans ?_)
  refine congrArg (fun k => k ⁻¹' supportOfSheaf B S hS (yoneda.obj U)
    ((SheafOfModules.toSheaf _).obj M)) (funext fun u => ?_)
  exact congrFun (pointsMap_id B S hS (yoneda.obj U)) _

/-- **Proper support on a represented algebraic space is proper support on the representing
scheme.**  A quasi-coherent module on `h_U` has support proper over `h_V` exactly when its
Zariski restriction along the identity chart has support proper over `V`. -/
theorem C1573.hasProperSupport_yoneda_map_iff {U V : BigFppfOver B S hS} (q : U ⟶ V)
    [LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map q)]
    (hq : IsLocallyOfFiniteType B S hS (yoneda.map q))
    (M : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hM : M.IsQuasicoherentOnSite) :
    HasProperSupport B S hS (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V)
        (yoneda.map q) hq ((SheafOfModules.toSheaf _).obj M) ↔
      Stacks.Algebraization.HasProperSupport ((BigFppfOver.toScheme B S hS).map q)
        ((chartZariskiModule B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
          (idEtaleChart B S hS U)).obj M) := by
  have hsupp := supp_chartZariskiModule_idEtaleChart B S hS U M hM
  set e := pointsEquivScheme B S hS U
  have hset : supportOfSheaf B S hS (yoneda.obj U) ((SheafOfModules.toSheaf _).obj M) =
      e ⁻¹' SheafOfModules.supp ((chartZariskiModule B S hS
        ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ (idEtaleChart B S hS U)).obj M) :=
    (e.preimage_symm_preimage _).symm.trans (congrArg (e ⁻¹' ·) hsupp).symm
  have hhom : ∀ Z : Set ((BigFppfOver.toScheme B S hS).obj U),
      IsClosed (e ⁻¹' Z) ↔ IsClosed Z := fun Z =>
    (schemePointsHomeomorph B S hS U).isClosed_preimage (s := Z)
  have key : ∀ (T : Set (points B S hS (yoneda.obj U))) (hT : IsClosed T)
      (Z : Closeds ((BigFppfOver.toScheme B S hS).obj U)), T = e ⁻¹' (Z : Set _) →
      (IsProperOver B S hS (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V)
        (yoneda.map q) hq T hT ↔
        _root_.AlgebraicGeometry.IsProperOver ((BigFppfOver.toScheme B S hS).map q) Z) := by
    rintro _ hT Z rfl
    exact isProperOver_yoneda_map_iff B S hS q hq Z hT
  constructor
  · rintro ⟨hcl, hp⟩
    have hZ : IsClosed (SheafOfModules.supp ((chartZariskiModule B S hS
        ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ (idEtaleChart B S hS U)).obj M)) :=
      (hhom _).1 (hset ▸ hcl)
    exact ⟨⟨_, hZ⟩, rfl, (key _ hcl ⟨_, hZ⟩ hset).1 hp⟩
  · rintro ⟨Z, hZ, hp⟩
    have hT : supportOfSheaf B S hS (yoneda.obj U) ((SheafOfModules.toSheaf _).obj M) =
        e ⁻¹' (Z : Set _) := hset.trans (congrArg (fun W => e ⁻¹' W) hZ.symm)
    have hcl : IsClosed (supportOfSheaf B S hS (yoneda.obj U)
        ((SheafOfModules.toSheaf _).obj M)) := hT ▸ (hhom _).2 Z.isClosed
    exact ⟨hcl, (key _ hcl Z hT).2 hp⟩

end AlgebraicGeometry.Space

end
