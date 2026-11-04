module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapZeroLocusSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictToChartSchemeSectionsTransport

/-!
# Projectivity of the sections along a chart, from the Zariski pullback of a chart restriction

Let `G` be a quasi-coherent module on an algebraic space `X`, let `U` be an étale chart of `X`
and let `r : W ⟶ U` be a morphism of the site. The reading
`AlgebraicGeometry.Space.baseChangeModule` of `G` on the represented algebraic space of `W` along
the composite `h_W ⟶ h_U ⟶ X` is isomorphic to the Zariski pullback `r^*(G|_U)` of the chart
restriction of `G`, by the compatibility of chart restriction with base change for a
quasi-coherent module, `AlgebraicGeometry.Space.restrictToChartBaseChangeIso`. The isomorphism is
linear over the functions on `W`, so projectivity of the global sections over the functions on
any scheme under `W` holds for one module exactly when it holds for the other.

## Main definitions

* `AlgebraicGeometry.Space.baseChangeModuleIsoPullbackRestrictToChart`: the isomorphism between
  `r^*(G|_U)` and the reading of `G` on `W`.

## Main results

* `AlgebraicGeometry.Space.projective_baseChangeModule_of_projective_pullback_restrictToChart`:
  for `p : X' ⟶ X` and `g : h_W ⟶ X'` with `g ≫ p = h_r ≫ U`, projectivity of the sections of
  `r^*(G|_U)` implies projectivity of the sections of the reading of `p^* G` on `W` along `g`.
* `AlgebraicGeometry.Space.ModuleMapSituation.chartSectionsProjective_baseChangeTarget`: the same
  implication, with conclusion
  `AlgebraicGeometry.Space.ModuleMapSituation.ChartSectionsProjective`, for a chart of a base
  change `X ×_Y Y'`.
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The reading of a quasi-coherent module on a scheme through a chart is the Zariski pullback
of its chart restriction.**  For `G` quasi-coherent on `X`, an étale chart `U` of `X` and a
morphism `r : W ⟶ U` of the site, `baseChangeModule G W (h_r ≫ U)` is the pullback along `r` of
`G|_U`. -/
def baseChangeModuleIsoPullbackRestrictToChart {X : AlgebraicSpaces B S hS}
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : G.IsQuasicoherentOnSite)
    (U : SmallEtale B S hS X.1) {W : BigFppfOver B S hS}
    (r : W ⟶ (SmallEtale.toOver B S hS X.1).obj U) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).obj
        (restrictToChart B S hS X.2 G U) ≅
      baseChangeModule B S hS G W (yoneda.map r ≫ U.obj.hom) :=
  restrictToChartBaseChangeIso B S hS (X := schemeSpace W) (Z := X)
      (ObjectProperty.homMk (yoneda.map r ≫ U.obj.hom)) G hG U (idEtaleChart B S hS W) r
      (Category.id_comp _).symm ≪≫
    restrictToChartIsoRestrictToChartScheme B S hS (isAlgebraicSpace_yoneda B S hS W)
      ((modulePullback B S hS (ObjectProperty.homMk (yoneda.map r ≫ U.obj.hom) :
        schemeSpace W ⟶ X)).obj G) (idEtaleChart B S hS W)

/-- **Projectivity of the sections of the reading along a chart.**  Let `G` be quasi-coherent on
`X`, `p : X' ⟶ X`, `U` an étale chart of `X`, `r : W ⟶ U` a morphism of the site and
`g : h_W ⟶ X'` with `g ≫ p = h_r ≫ U`.  If the global sections of `r^*(G|_U)` are projective
over the functions on `V` (acting through `α : W ⟶ V`), so are the global sections of the reading
of `p^* G` on `W` along `g`. -/
theorem projective_baseChangeModule_of_projective_pullback_restrictToChart
    {X X' : AlgebraicSpaces B S hS} (p : X' ⟶ X)
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : G.IsQuasicoherentOnSite)
    (U : SmallEtale B S hS X.1) {V W : BigFppfOver B S hS}
    (r : W ⟶ (SmallEtale.toOver B S hS X.1).obj U) (g : yoneda.obj W ⟶ X'.1)
    (hg : g ≫ p.hom = yoneda.map r ≫ U.obj.hom) (α : W ⟶ V)
    (hproj :
      letI M := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).obj
        (restrictToChart B S hS X.2 G U)
      letI : Module Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) Γ(M, ⊤) :=
        Module.compHom Γ(M, ⊤) ((BigFppfOver.toScheme B S hS).map α).appTop.hom
      Module.Projective Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) Γ(M, ⊤)) :
    letI M := baseChangeModule B S hS ((modulePullback B S hS p).obj G) W g
    letI : Module Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) (Γ(M, ⊤) : Type u) :=
      Module.compHom _ ((BigFppfOver.toScheme B S hS).map α).appTop.hom
    Module.Projective Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) (Γ(M, ⊤) : Type u) := by
  let e : (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).obj
        (restrictToChart B S hS X.2 G U) ≅
      baseChangeModule B S hS ((modulePullback B S hS p).obj G) W g :=
    baseChangeModuleIsoPullbackRestrictToChart B S hS G hG U r ≪≫
      eqToIso (congrArg (baseChangeModule B S hS G W) hg.symm) ≪≫
      baseChangeModuleCompIso B S hS p G W g
  exact Module.Projective.of_compHom_addEquiv ((BigFppfOver.toScheme B S hS).map α).appTop.hom
    (Scheme.Modules.sectionsAddEquiv e ⊤) (Scheme.Modules.sectionsAddEquiv_smul e ⊤) hproj

namespace ModuleMapSituation

/-- **Projectivity of the sections along a chart of a base change.**  For a chart
`g : h_W ⟶ X ×_Y Y'` of a base change whose composite with the projection to `X` factors as
`h_r ≫ U` through an étale chart `U` of `X`, if the sections of `r^*(G|_U)` are projective over
`Γ(V, 𝒪_V)` then `ChartSectionsProjective V W g α` holds for the base change. -/
theorem chartSectionsProjective_baseChangeTarget (D : ModuleMapSituation.{u, u} B S hS)
    {Y' : AlgebraicSpaces B S hS} (b : Y' ⟶ D.Y) {V W : BigFppfOver B S hS}
    (g : schemeSpace W ⟶ (D.baseChangeTarget b).X) (α : W ⟶ V)
    (U : SmallEtale B S hS D.X.1) (r : W ⟶ (SmallEtale.toOver B S hS D.X.1).obj U)
    (hg : g.hom ≫ pullback.fst D.f.hom b.hom = yoneda.map r ≫ U.obj.hom)
    (hproj :
      letI M := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).obj
        (restrictToChart B S hS D.X.2 D.G U)
      letI : Module Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) Γ(M, ⊤) :=
        Module.compHom Γ(M, ⊤) ((BigFppfOver.toScheme B S hS).map α).appTop.hom
      Module.Projective Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) Γ(M, ⊤)) :
    (D.baseChangeTarget b).ChartSectionsProjective V W g α :=
  projective_baseChangeModule_of_projective_pullback_restrictToChart B S hS
    (D.baseChangeTargetProjection b) D.G D.quasicoherent_G U r g.hom hg α hproj

end ModuleMapSituation

end AlgebraicGeometry.Space

end
