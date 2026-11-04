module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCoordinateRatioValue
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsSchemeReadingUnit

/-!
# The coordinates of a chart of an inverse image, with the chart identifications of `𝒪`

`AlgebraicGeometry.Space.modulePullbackChartSection_value_eq_coordVector` takes the unit
compatibility of `AlgebraicGeometry.Space.chartSectionsReadingEquiv` at the two charts as
hypotheses on identifications `UV`, `UA` of the readings of `𝒪` with `𝒪`. For the identification
`schemeReadingChartIso ≪≫ restrictToChartSchemeUnitIso` these hypotheses hold
(`AlgebraicGeometry.Space.chartSectionsReadingEquiv_unit_apply`,
`AlgebraicGeometry.Space.chartSectionsReadingEquiv_unit_one`); this file states the coordinate
identity for identifications equal to that one, with no further hypothesis on them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section ChartUnit

variable {Y : AlgebraicSpaces B S hS} (W : SmallEtale B S hS Y.1)

/-- An identification of the reading of `𝒪_Y` at a chart with `𝒪`, on which θ is the identity on
the functions of the chart, is so on the sections of the unit module. -/
theorem chartUnitReading_hom_app_chartSectionsReadingEquiv_unit
    (UA : schemeReading (T := (SmallEtale.toOver B S hS Y.1).obj W)
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O))) (chartToSpace B S hS Y W) ≅
      Scheme.unitModule (chartScheme W))
    (hb : ∀ r : (structureRingSheaf B S hS Y).obj.obj (op W),
      UA.hom.app ⊤ (chartSectionsReadingEquiv (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
          W r) = r) :
    ∀ r : (SheafOfModules.unit (structureRingSheaf B S hS Y)).val.obj (op W),
      UA.hom.app ⊤
        (chartSectionsReadingEquiv (SheafOfModules.unit (structureRingSheaf B S hS Y)) W r) = r :=
  hb

/-- `θ` is the identity on functions for the identification
`schemeReadingChartIso ≪≫ restrictToChartSchemeUnitIso`, for an identification `UA` equal to it. -/
theorem chartUnitReading_hom_app_chartSectionsReadingEquiv_unit_of_eq
    (UA : schemeReading (T := (SmallEtale.toOver B S hS Y.1).obj W)
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O))) (chartToSpace B S hS Y W) ≅
      Scheme.unitModule (chartScheme W))
    (hUA : UA = (schemeReadingChartIso (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O))) W ≪≫
      restrictToChartSchemeUnitIso B S hS Y.1 Y.2 W)) :
    ∀ r : (SheafOfModules.unit (structureRingSheaf B S hS Y)).val.obj (op W),
      UA.hom.app ⊤
        (chartSectionsReadingEquiv (SheafOfModules.unit (structureRingSheaf B S hS Y)) W r) =
          r := by
  refine chartUnitReading_hom_app_chartSectionsReadingEquiv_unit W UA ?_
  subst hUA
  exact chartSectionsReadingEquiv_unit_apply W

/-- The inverse of an identification of the reading of `𝒪_Y` at a chart with `𝒪` sending the
reading of `1` to `1` sends `1` to the reading of `1`. -/
theorem chartUnitReading_inv_app_one
    (UV : schemeReading (T := (SmallEtale.toOver B S hS Y.1).obj W)
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O))) (chartToSpace B S hS Y W) ≅
      Scheme.unitModule (chartScheme W))
    (h : UV.hom.app ⊤ (chartSectionsReadingEquiv (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) W
          (1 : (structureRingSheaf B S hS Y).obj.obj (op W))) = (1 : Γ(chartScheme W, ⊤))) :
    UV.inv.app ⊤ (1 : Γ(chartScheme W, ⊤)) =
      chartSectionsReadingEquiv (SheafOfModules.unit (structureRingSheaf B S hS Y)) W
        (1 : (structureRingSheaf B S hS Y).obj.obj (op W)) :=
  (congrArg (fun z => UV.inv.app ⊤ z) h).symm.trans (scheme_modules_iso_inv_hom_app UV ⊤ _)

/-- `chartUnitReading_inv_app_one` for an identification `UV` equal to
`schemeReadingChartIso ≪≫ restrictToChartSchemeUnitIso`. -/
theorem chartUnitReading_inv_app_one_of_eq
    (UV : schemeReading (T := (SmallEtale.toOver B S hS Y.1).obj W)
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O))) (chartToSpace B S hS Y W) ≅
      Scheme.unitModule (chartScheme W))
    (hUV : UV = (schemeReadingChartIso (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O))) W ≪≫
      restrictToChartSchemeUnitIso B S hS Y.1 Y.2 W)) :
    UV.inv.app ⊤ (1 : Γ(chartScheme W, ⊤)) =
      chartSectionsReadingEquiv (SheafOfModules.unit (structureRingSheaf B S hS Y)) W
        (1 : (structureRingSheaf B S hS Y).obj.obj (op W)) := by
  refine chartUnitReading_inv_app_one W UV ?_
  subst hUV
  exact chartSectionsReadingEquiv_unit_one W _ rfl

end ChartUnit

section Coordinates

variable {U P X : AlgebraicSpaces B S hS} (ι : U ⟶ P) (π : P ⟶ X)
  {F : Modules.{u, u} B S hS X.1 X.2} {L : Modules.{u, u} B S hS P.1 P.2}
  (τ : (modulePullback B S hS π).obj F ⟶ L)
  {E : Modules.{u, u} B S hS X.1 X.2} (hEq : E.IsQuasicoherentOnSite)
  (hOq : (SheafOfModules.unit (structureRingSheaf B S hS X) :
    Modules.{u, u} B S hS X.1 X.2).IsQuasicoherentOnSite)
  (σE : E ⟶ F)
  (σO : (SheafOfModules.unit (structureRingSheaf B S hS X) : Modules.{u, u} B S hS X.1 X.2) ⟶ F)
  (d : ChartDiagram B S hS U.1 X.1 (ι ≫ π).hom)
  (wρ : representedSpaceMap B S hS d.g ≫ chartToSpace B S hS X d.V =
    @CategoryStruct.comp _ _
      (representedAlgebraicSpace B S hS ((SmallEtale.toOver B S hS U.1).obj d.U)) U X
      (chartToSpace B S hS U d.U) (ι ≫ π))

include wρ hEq hOq in
/-- **The coordinates of `f : U_c ⟶ 𝐏(𝓕|_V)` are the values of `q`**
(`AlgebraicGeometry.Space.modulePullbackChartSection_value_eq_coordVector`), for the
identifications `UV`, `UA` of the readings of `𝒪` at `V` and at `U_c` with `𝒪` given by
`schemeReadingChartIso ≪≫ restrictToChartSchemeUnitIso`: the unit compatibility of `θ` is then
proved, not assumed. -/
theorem modulePullbackChartSection_value_eq_coordVector_of_chartUnit
    [(schemeReading F (chartToSpace B S hS X d.V)).IsQuasicoherent]
    [(schemeReading E (chartToSpace B S hS X d.V)).IsQuasicoherent]
    {us : schemeReading F (chartToSpace B S hS X d.V) ⟶ schemeReading E (chartToSpace B S hS X d.V)}
    [Epi us] (Sp : Stacks.RelativeProj.UnitSplitting us)
    (UV : schemeReading (T := (SmallEtale.toOver B S hS X.1).obj d.V)
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O))) (chartToSpace B S hS X d.V) ≅
      Scheme.unitModule (chartScheme d.V))
    (hUV : UV = (schemeReadingChartIso (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O))) d.V ≪≫
      restrictToChartSchemeUnitIso B S hS X.1 X.2 d.V))
    (UA : schemeReading (T := (SmallEtale.toOver B S hS U.1).obj d.U)
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS U.1 U.2).O))) (chartToSpace B S hS U d.U) ≅
      Scheme.unitModule (chartScheme d.U))
    (hUA : UA = (schemeReadingChartIso (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS U.1 U.2).O))) d.U ≪≫
      restrictToChartSchemeUnitIso B S hS U.1 U.2 d.U))
    (hσ : Sp.σ = UV.inv ≫ schemeReadingMap (chartToSpace B S hS X d.V) σO)
    (hσ' : Sp.σ' = schemeReadingMap (chartToSpace B S hS X d.V) σE)
    (f : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS U.1).obj d.U) ⟶
      Stacks.RelativeProj.projectiveBundle (chartScheme d.V)
        (schemeReading F (chartToSpace B S hS X d.V)))
    (hg : f ≫ Stacks.RelativeProj.projectiveBundleToBase (chartScheme d.V)
        (schemeReading F (chartToSpace B S hS X d.V)) =
      _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) d.g.left)
    (hf : Set.range f.base ⊆ Stacks.RelativeProj.splitQuotientComplement us)
    (ε : representedZariskiModule B S hS ((SmallEtale.toOver B S hS U.1).obj d.U)
      ((modulePullback B S hS
        (X := representedAlgebraicSpace B S hS ((SmallEtale.toOver B S hS U.1).obj d.U))
        (chartToSpace B S hS U d.U)).obj ((modulePullback B S hS ι).obj L)) ≅
      (Scheme.Modules.pullback f).obj
        (Stacks.RelativeProj.tautologicalDatum (schemeReading F (chartToSpace B S hS X d.V))).twist)
    (hML : ∀ (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) (σ₀ : M ⟶ F),
      QuotientReadingHyp M hM wρ
        ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
            (associatedBigEtaleSite B) d.g.left)).map
          (schemeReadingMap (chartToSpace B S hS X d.V) σ₀) ≫
          (Stacks.RelativeProj.tautologicalDatum
            (schemeReading F (chartToSpace B S hS X d.V))).overQuotientMap f hg) ε
        ((modulePullback B S hS
          (X := representedAlgebraicSpace B S hS ((SmallEtale.toOver B S hS U.1).obj d.U))
          (chartToSpace B S hS U d.U)).map (compPullbackQuotient ι π τ σ₀))
        (QuasiCoherentDescent.pullbackComparison B S hS (chartToSpace B S hS U d.U) (ι ≫ π)
          (@CategoryStruct.comp _ _
            (representedAlgebraicSpace B S hS ((SmallEtale.toOver B S hS U.1).obj d.U))
            U X (chartToSpace B S hS U d.U) (ι ≫ π)) rfl M).symm)
    [hs : IsIso ((modulePullback B S hS ι).map ((modulePullbackUnitIso B S hS π).inv ≫
      (modulePullback B S hS π).map σO ≫ τ))]
    (hw0 : ((modulePullbackUnitCompIso ι π).inv ≫ (modulePullbackUnitIso B S hS ι).hom).val.app
      (op d.U) (modulePullbackChartSection B S hS (ι ≫ π)
        (SheafOfModules.unit (structureRingSheaf B S hS X)) d
          (1 : (structureRingSheaf B S hS X).obj.obj (op d.V))) =
      (1 : (structureRingSheaf B S hS U).obj.obj (op d.U)))
    {n : Type u} (e : SheafOfModules.free (R := (chartScheme d.V).ringCatSheaf) n ≅
      schemeReading E (chartToSpace B S hS X d.V)) (j : n) (x : E.val.obj (op d.V))
    (hx : (Stacks.RelativeProj.UnitSplitting.basisMap e j).app ⊤ (1 : Γ(chartScheme d.V, ⊤)) =
      chartSectionsReadingEquiv E d.V x) :
    ((modulePullbackCompIso B S hS ι π).inv.app E ≫
        (modulePullback B S hS ι).map ((modulePullback B S hS π).map σE ≫ τ) ≫
        inv ((modulePullback B S hS ι).map ((modulePullbackUnitIso B S hS π).inv ≫
          (modulePullback B S hS π).map σO ≫ τ)) ≫
        (modulePullbackUnitIso B S hS ι).hom).val.app (op d.U)
      (modulePullbackChartSection B S hS (ι ≫ π) E d x) =
      Stacks.RelativeProj.UnitSplitting.coordVector e (Sp.splitCoordMap f hg hf) j := by
  have hbV := chartUnitReading_inv_app_one_of_eq d.V UV hUV
  have hbU := chartUnitReading_hom_app_chartSectionsReadingEquiv_unit_of_eq d.U UA hUA
  exact modulePullbackChartSection_value_eq_coordVector ι π τ hEq hOq σE σO d wρ Sp UV UA hσ hσ'
    f hg hf ε hML hbV hbU hw0 e j x hx

end Coordinates

section CoordinatesMk

variable {U P X : AlgebraicSpaces B S hS} (ι : U ⟶ P) (π : P ⟶ X)
  {F : Modules.{u, u} B S hS X.1 X.2} {L : Modules.{u, u} B S hS P.1 P.2}
  (τ : (modulePullback B S hS π).obj F ⟶ L)
  {E : Modules.{u, u} B S hS X.1 X.2} (hEq : E.IsQuasicoherentOnSite)
  (hOq : (SheafOfModules.unit (structureRingSheaf B S hS X) :
    Modules.{u, u} B S hS X.1 X.2).IsQuasicoherentOnSite)
  (σE : E ⟶ F)
  (σO : (SheafOfModules.unit (structureRingSheaf B S hS X) : Modules.{u, u} B S hS X.1 X.2) ⟶ F)
  (Uc : SmallEtale B S hS U.1) (Vc : SmallEtale B S hS X.1)
  (g : (SmallEtale.toOver B S hS U.1).obj Uc ⟶ (SmallEtale.toOver B S hS X.1).obj Vc)
  (comm : Uc.1.hom ≫ (ι ≫ π).hom = yoneda.map g ≫ Vc.1.hom)
  (wρ : representedSpaceMap B S hS g ≫ chartToSpace B S hS X Vc =
    @CategoryStruct.comp _ _
      (representedAlgebraicSpace B S hS ((SmallEtale.toOver B S hS U.1).obj Uc)) U X
      (chartToSpace B S hS U Uc) (ι ≫ π))

include wρ hEq hOq in
/-- `AlgebraicGeometry.Space.modulePullbackChartSection_value_eq_coordVector_of_chartUnit` with the
chart diagram `U_c ⟶ V` given by its components. -/
theorem modulePullbackChartSection_value_eq_coordVector_of_chartUnit_mk
    [hFq : (schemeReading F (chartToSpace B S hS X Vc)).IsQuasicoherent]
    [hEq' : (schemeReading E (chartToSpace B S hS X Vc)).IsQuasicoherent]
    {us : schemeReading F (chartToSpace B S hS X Vc) ⟶ schemeReading E (chartToSpace B S hS X Vc)}
    [hus : Epi us] (Sp : Stacks.RelativeProj.UnitSplitting us)
    (UV : schemeReading (T := (SmallEtale.toOver B S hS X.1).obj Vc)
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O))) (chartToSpace B S hS X Vc) ≅
      Scheme.unitModule (chartScheme Vc))
    (hUV : UV = (schemeReadingChartIso (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O))) Vc ≪≫
      restrictToChartSchemeUnitIso B S hS X.1 X.2 Vc))
    (UA : schemeReading (T := (SmallEtale.toOver B S hS U.1).obj Uc)
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS U.1 U.2).O))) (chartToSpace B S hS U Uc) ≅
      Scheme.unitModule (chartScheme Uc))
    (hUA : UA = (schemeReadingChartIso (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS U.1 U.2).O))) Uc ≪≫
      restrictToChartSchemeUnitIso B S hS U.1 U.2 Uc))
    (hσ : Sp.σ = UV.inv ≫ schemeReadingMap (chartToSpace B S hS X Vc) σO)
    (hσ' : Sp.σ' = schemeReadingMap (chartToSpace B S hS X Vc) σE)
    (f : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS U.1).obj Uc) ⟶
      Stacks.RelativeProj.projectiveBundle (chartScheme Vc)
        (schemeReading F (chartToSpace B S hS X Vc)))
    (hg : f ≫ Stacks.RelativeProj.projectiveBundleToBase (chartScheme Vc)
        (schemeReading F (chartToSpace B S hS X Vc)) =
      _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)
    (hf : Set.range f.base ⊆ Stacks.RelativeProj.splitQuotientComplement us)
    (ε : representedZariskiModule B S hS ((SmallEtale.toOver B S hS U.1).obj Uc)
      ((modulePullback B S hS
        (X := representedAlgebraicSpace B S hS ((SmallEtale.toOver B S hS U.1).obj Uc))
        (chartToSpace B S hS U Uc)).obj ((modulePullback B S hS ι).obj L)) ≅
      (Scheme.Modules.pullback f).obj
        (Stacks.RelativeProj.tautologicalDatum (schemeReading F (chartToSpace B S hS X Vc))).twist)
    (hML : ∀ (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) (σ₀ : M ⟶ F),
      QuotientReadingHyp M hM wρ
        ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
            (associatedBigEtaleSite B) g.left)).map
          (schemeReadingMap (chartToSpace B S hS X Vc) σ₀) ≫
          (Stacks.RelativeProj.tautologicalDatum
            (schemeReading F (chartToSpace B S hS X Vc))).overQuotientMap f hg) ε
        ((modulePullback B S hS
          (X := representedAlgebraicSpace B S hS ((SmallEtale.toOver B S hS U.1).obj Uc))
          (chartToSpace B S hS U Uc)).map (compPullbackQuotient ι π τ σ₀))
        (QuasiCoherentDescent.pullbackComparison B S hS (chartToSpace B S hS U Uc) (ι ≫ π)
          (@CategoryStruct.comp _ _
            (representedAlgebraicSpace B S hS ((SmallEtale.toOver B S hS U.1).obj Uc))
            U X (chartToSpace B S hS U Uc) (ι ≫ π)) rfl M).symm)
    [hs : IsIso ((modulePullback B S hS ι).map ((modulePullbackUnitIso B S hS π).inv ≫
      (modulePullback B S hS π).map σO ≫ τ))]
    (hw0 : ((modulePullbackUnitCompIso ι π).inv ≫ (modulePullbackUnitIso B S hS ι).hom).val.app
      (op Uc) (modulePullbackChartSection B S hS (ι ≫ π)
        (SheafOfModules.unit (structureRingSheaf B S hS X))
        ⟨Uc, Vc, g, comm⟩
          (1 : (structureRingSheaf B S hS X).obj.obj (op Vc))) =
      (1 : (structureRingSheaf B S hS U).obj.obj (op Uc)))
    {n : Type u} (e : SheafOfModules.free (R := (chartScheme Vc).ringCatSheaf) n ≅
      schemeReading E (chartToSpace B S hS X Vc)) (j : n) (x : E.val.obj (op Vc))
    (hx : (Stacks.RelativeProj.UnitSplitting.basisMap e j).app ⊤ (1 : Γ(chartScheme Vc, ⊤)) =
      chartSectionsReadingEquiv E Vc x) :
    ((modulePullbackCompIso B S hS ι π).inv.app E ≫
        (modulePullback B S hS ι).map ((modulePullback B S hS π).map σE ≫ τ) ≫
        inv ((modulePullback B S hS ι).map ((modulePullbackUnitIso B S hS π).inv ≫
          (modulePullback B S hS π).map σO ≫ τ)) ≫
        (modulePullbackUnitIso B S hS ι).hom).val.app (op Uc)
      (modulePullbackChartSection B S hS (ι ≫ π) E ⟨Uc, Vc, g, comm⟩ x) =
      Stacks.RelativeProj.UnitSplitting.coordVector e (Sp.splitCoordMap f hg hf) j := by
  have key := modulePullbackChartSection_value_eq_coordVector_of_chartUnit ι π τ hEq hOq σE σO
    ⟨Uc, Vc, g, comm⟩
  dsimp only at key
  exact key wρ Sp UV hUV UA hUA hσ hσ' f hg hf ε hML hw0 e j x hx

include wρ hEq hOq in
/-- `AlgebraicGeometry.Space.modulePullbackChartSection_value_eq_coordVector_of_chartUnit_mk` with
the comparison of iterated inverse images in `hML` spelled with source the represented chart, as
the quotient readings of the projective bundle produce it. -/
theorem modulePullbackChartSection_value_eq_coordVector_of_chartUnit_site
    [hFq : (schemeReading F (chartToSpace B S hS X Vc)).IsQuasicoherent]
    [hEq' : (schemeReading E (chartToSpace B S hS X Vc)).IsQuasicoherent]
    {us : schemeReading F (chartToSpace B S hS X Vc) ⟶ schemeReading E (chartToSpace B S hS X Vc)}
    [hus : Epi us] (Sp : Stacks.RelativeProj.UnitSplitting us)
    (UV : schemeReading (T := (SmallEtale.toOver B S hS X.1).obj Vc)
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O))) (chartToSpace B S hS X Vc) ≅
      Scheme.unitModule (chartScheme Vc))
    (hUV : UV = (schemeReadingChartIso (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O))) Vc ≪≫
      restrictToChartSchemeUnitIso B S hS X.1 X.2 Vc))
    (UA : schemeReading (T := (SmallEtale.toOver B S hS U.1).obj Uc)
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS U.1 U.2).O))) (chartToSpace B S hS U Uc) ≅
      Scheme.unitModule (chartScheme Uc))
    (hUA : UA = (schemeReadingChartIso (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS U.1 U.2).O))) Uc ≪≫
      restrictToChartSchemeUnitIso B S hS U.1 U.2 Uc))
    (hσ : Sp.σ = UV.inv ≫ schemeReadingMap (chartToSpace B S hS X Vc) σO)
    (hσ' : Sp.σ' = schemeReadingMap (chartToSpace B S hS X Vc) σE)
    (f : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS U.1).obj Uc) ⟶
      Stacks.RelativeProj.projectiveBundle (chartScheme Vc)
        (schemeReading F (chartToSpace B S hS X Vc)))
    (hg : f ≫ Stacks.RelativeProj.projectiveBundleToBase (chartScheme Vc)
        (schemeReading F (chartToSpace B S hS X Vc)) =
      _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)
    (hf : Set.range f.base ⊆ Stacks.RelativeProj.splitQuotientComplement us)
    (ε : representedZariskiModule B S hS ((SmallEtale.toOver B S hS U.1).obj Uc)
      ((modulePullback B S hS
        (X := representedAlgebraicSpace B S hS ((SmallEtale.toOver B S hS U.1).obj Uc))
        (chartToSpace B S hS U Uc)).obj ((modulePullback B S hS ι).obj L)) ≅
      (Scheme.Modules.pullback f).obj
        (Stacks.RelativeProj.tautologicalDatum (schemeReading F (chartToSpace B S hS X Vc))).twist)
    (hML : ∀ (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) (σ₀ : M ⟶ F),
      QuotientReadingHyp M hM wρ
        ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
            (associatedBigEtaleSite B) g.left)).map
          (schemeReadingMap (chartToSpace B S hS X Vc) σ₀) ≫
          (Stacks.RelativeProj.tautologicalDatum
            (schemeReading F (chartToSpace B S hS X Vc))).overQuotientMap f hg) ε
        ((modulePullback B S hS
          (X := representedAlgebraicSpace B S hS ((SmallEtale.toOver B S hS U.1).obj Uc))
          (chartToSpace B S hS U Uc)).map (compPullbackQuotient ι π τ σ₀))
        (QuasiCoherentDescent.pullbackComparison B S hS
          (T := representedAlgebraicSpace B S hS ((SmallEtale.toOver B S hS U.1).obj Uc))
          (chartToSpace B S hS U Uc) (ι ≫ π)
          (@CategoryStruct.comp _ _
            (representedAlgebraicSpace B S hS ((SmallEtale.toOver B S hS U.1).obj Uc))
            U X (chartToSpace B S hS U Uc) (ι ≫ π)) rfl M).symm)
    [hs : IsIso ((modulePullback B S hS ι).map ((modulePullbackUnitIso B S hS π).inv ≫
      (modulePullback B S hS π).map σO ≫ τ))]
    (hw0 : ((modulePullbackUnitCompIso ι π).inv ≫ (modulePullbackUnitIso B S hS ι).hom).val.app
      (op Uc) (modulePullbackChartSection B S hS (ι ≫ π)
        (SheafOfModules.unit (structureRingSheaf B S hS X))
        ⟨Uc, Vc, g, comm⟩
          (1 : (structureRingSheaf B S hS X).obj.obj (op Vc))) =
      (1 : (structureRingSheaf B S hS U).obj.obj (op Uc)))
    {n : Type u} (e : SheafOfModules.free (R := (chartScheme Vc).ringCatSheaf) n ≅
      schemeReading E (chartToSpace B S hS X Vc)) (j : n) (x : E.val.obj (op Vc))
    (hx : (Stacks.RelativeProj.UnitSplitting.basisMap e j).app ⊤ (1 : Γ(chartScheme Vc, ⊤)) =
      chartSectionsReadingEquiv E Vc x) :
    ((modulePullbackCompIso B S hS ι π).inv.app E ≫
        (modulePullback B S hS ι).map ((modulePullback B S hS π).map σE ≫ τ) ≫
        inv ((modulePullback B S hS ι).map ((modulePullbackUnitIso B S hS π).inv ≫
          (modulePullback B S hS π).map σO ≫ τ)) ≫
        (modulePullbackUnitIso B S hS ι).hom).val.app (op Uc)
      (modulePullbackChartSection B S hS (ι ≫ π) E ⟨Uc, Vc, g, comm⟩ x) =
      Stacks.RelativeProj.UnitSplitting.coordVector e (Sp.splitCoordMap f hg hf) j :=
  modulePullbackChartSection_value_eq_coordVector_of_chartUnit_mk ι π τ hEq hOq σE σO Uc Vc g comm
    wρ Sp UV hUV UA hUA hσ hσ' f hg hf ε hML hw0 e j x hx

end CoordinatesMk

end AlgebraicGeometry.Space

end
