module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyDualizingCharts
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyRelativeDualizingSheaf
public import StacksFrontier.AlgebraicGeometry.Duality.CurveFamilyDualizing.TransitionChart
public import StacksFrontier.AlgebraicGeometry.Duality.CurveFamilyDualizing.ModuleTransition
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleSystem.Invertible
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeMapEtale
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist

/-!
# The relative dualizing sheaf of a nodal family of curves, glued from its étale charts

Let `f : X ⟶ S` be a family of curves (Stacks 0D4Z) which is at-worst-nodal of relative dimension
one. On the scheme of every étale chart `U` of the total space, the chosen relative dualizing
complex of `U ⟶ S` is `ω_{U/S}[1]` with `ω_{U/S}` invertible
(`AlgebraicGeometry.CurveFamily.chartDualizingComplex_shape`, Stacks 0E6P and 0E6R on the chart).
A morphism `g : V ⟶ U` of étale charts gives a chart square from `U ⟶ S` to `V ⟶ S` over the
identity of `S`, whose transition isomorphism `L(g)^*ω^•_{U/S} ≅ ω^•_{V/S}` (Stacks 0E2Y, 0E2W)
is read in degree `-1` as `g^*ω_{U/S} ≅ ω_{V/S}`
(`Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDegreeTransition`). The cocycle law of the
transitions of relative dualizing complexes gives the cocycle condition, and the chart modules
glue to an invertible module `ω_{X/S}` on the small étale site of `X`
(`AlgebraicGeometry.CurveFamily.gluedRelativeDualizingSheaf`).

The transitions of chart squares whose gap map is étale over the identity of the base are the
one input not available here; they are taken as the hypothesis `hEt`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.relDualizingModuleTransition`: the module transition
  `g'^*H^{-1}(ω^•_{X/S}) ≅ H^{-1}(ω^•_{X'/S'})` of a square with a transition isomorphism.
* `AlgebraicGeometry.CurveFamily.dualizingSystem`: the chart-scheme module system of the
  relative dualizing sheaves of the charts.
* `AlgebraicGeometry.CurveFamily.gluedRelativeDualizingSheaf`: the glued module `ω_{X/S}`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.relDualizingModuleTransition_comp`: the cocycle law of module
  transitions of pasted squares.
* `AlgebraicGeometry.CurveFamily.isInvertible_relativeDualizingSheaf`: `ω_{X/S}` is invertible.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-! ### Module transitions of squares with a transition isomorphism -/

section ModuleTransition

variable {X S X' S' : Scheme.{u}}

/-- The module `H^{-1}(ω^•_{X/S})` of the chosen relative dualizing complex. -/
abbrev relDualizingSheafNegOne (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] :
    X.Modules :=
  letI := HasDerivedCategory.standard X.Modules
  (DerivedCategory.homologyFunctor X.Modules (-1)).obj (relDualizingComplex f)

variable {f : X ⟶ S} {f' : X' ⟶ S'} [Flat f] [LocallyOfFinitePresentation f] [Flat f']
  [LocallyOfFinitePresentation f']

/-- **The module transition of a square with a transition isomorphism**: the transition
`L(g')^*ω^•_{X/S} ≅ ω^•_{X'/S'}` read in degree `-1`, for `ω^•_{X/S}` without cohomology above
degree `-1`, as `g'^*H^{-1}(ω^•_{X/S}) ≅ H^{-1}(ω^•_{X'/S'})`. -/
def relDualizingModuleTransition (g' : X' ⟶ X) (g : S' ⟶ S) (comm : g' ≫ f = f' ≫ g)
    (h : HasRelDualizingTransition g' g comm)
    (hK : letI :=
        HasDerivedCategory.standard (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)
      DerivedCategory.TStructure.t.IsLE (relDualizingComplex f) (-1)) :
    (Scheme.Modules.pullback g').obj (relDualizingSheafNegOne f) ≅
      relDualizingSheafNegOne f' :=
  letI (T : RingedSpace.{u, u}) :=
    HasDerivedCategory.standard (StrictlyPerfect.OXMod.{u, u} T)
  letI (T : Scheme.{u}) := HasDerivedCategory.standard T.Modules
  letI (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules (structureSheafRing T.toRingedSpace))
  Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDegreeTransition g'.toLRSHom.toShHom (-1) hK
    (relDualizingTransition g' g comm h)

/-- The module transition only depends on the map of bases through the square. -/
theorem relDualizingModuleTransition_congr (g' : X' ⟶ X) {g₁ g₂ : S' ⟶ S}
    (comm₁ : g' ≫ f = f' ≫ g₁) (comm₂ : g' ≫ f = f' ≫ g₂) (hg : g₁ = g₂)
    (h₁ : HasRelDualizingTransition g' g₁ comm₁) (h₂ : HasRelDualizingTransition g' g₂ comm₂)
    (hK : letI :=
        HasDerivedCategory.standard (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)
      DerivedCategory.TStructure.t.IsLE (relDualizingComplex f) (-1)) :
    relDualizingModuleTransition g' g₁ comm₁ h₁ hK =
      relDualizingModuleTransition g' g₂ comm₂ h₂ hK := by
  subst hg
  rfl

end ModuleTransition

section ModuleTransitionComp

variable {X₁ X₂ X₃ S₁ S₂ S₃ : Scheme.{u}} {f₁ : X₁ ⟶ S₁} {f₂ : X₂ ⟶ S₂} {f₃ : X₃ ⟶ S₃}
  [Flat f₁] [LocallyOfFinitePresentation f₁] [Flat f₂] [LocallyOfFinitePresentation f₂]
  [Flat f₃] [LocallyOfFinitePresentation f₃]

/-- **The cocycle law of module transitions**: for squares `(g₁', g₁)` from `f₁` to `f₂` and
`(g₂', g₂)` from `f₂` to `f₃` with transition isomorphisms, `g₂'^*` of the first module
transition followed by the second is the composition comparison of pullbacks followed by the
module transition of the pasted square (over any map of bases equal to `g₂ ≫ g₁`). -/
theorem relDualizingModuleTransition_comp {g₁' : X₂ ⟶ X₁} {g₁ : S₂ ⟶ S₁}
    (comm₁ : g₁' ≫ f₁ = f₂ ≫ g₁) {g₂' : X₃ ⟶ X₂} {g₂ : S₃ ⟶ S₂} (comm₂ : g₂' ≫ f₂ = f₃ ≫ g₂)
    {c : S₃ ⟶ S₁} (comm : (g₂' ≫ g₁') ≫ f₁ = f₃ ≫ c) (hc : g₂ ≫ g₁ = c)
    (h₁ : HasRelDualizingTransition g₁' g₁ comm₁) (h₂ : HasRelDualizingTransition g₂' g₂ comm₂)
    (h : HasRelDualizingTransition (g₂' ≫ g₁') c comm)
    (hK₁ : letI :=
        HasDerivedCategory.standard (StrictlyPerfect.OXMod.{u, u} X₁.toRingedSpace)
      DerivedCategory.TStructure.t.IsLE (relDualizingComplex f₁) (-1))
    (hK₂ : letI :=
        HasDerivedCategory.standard (StrictlyPerfect.OXMod.{u, u} X₂.toRingedSpace)
      DerivedCategory.TStructure.t.IsLE (relDualizingComplex f₂) (-1)) :
    (Scheme.Modules.pullback g₂').map (relDualizingModuleTransition g₁' g₁ comm₁ h₁ hK₁).hom ≫
        (relDualizingModuleTransition g₂' g₂ comm₂ h₂ hK₂).hom =
      (Scheme.Modules.pullbackComp g₂' g₁').hom.app (relDualizingSheafNegOne f₁) ≫
        (relDualizingModuleTransition (g₂' ≫ g₁') c comm h hK₁).hom := by
  let (T : RingedSpace.{u, u}) :=
    HasDerivedCategory.standard (StrictlyPerfect.OXMod.{u, u} T)
  let (T : Scheme.{u}) := HasDerivedCategory.standard T.Modules
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
  subst hc
  have e := relDualizingTransition_comp h₁ h₂ comm h
  unfold relDualizingModuleTransition
  rw [e]
  exact Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDegreeTransition_comp_scheme g₂' g₁' (-1)
    hK₁ hK₂ _ _

end ModuleTransitionComp

/-! ### Squares over the identity of the base whose total map is étale -/

section EtaleSquare

variable {X S X' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S}

/-- **A square over the identity of the base whose map of total spaces is étale is a chart
square**: its gap map is the étale map followed by the inverse of the isomorphism
`X ×_S S ⟶ X`. -/
abbrev ChartSquare.ofEtale (e : X' ⟶ X) [Etale e] (comm : e ≫ f = f' ≫ 𝟙 S) :
    ChartSquare f f' where
  g' := e
  g := 𝟙 S
  comm := comm
  etale_gap := by
    have h : pullback.lift e f' comm = e ≫ inv (pullback.fst f (𝟙 S)) := by
      rw [IsIso.eq_comp_inv, pullback.lift_fst]
    rw [h]
    infer_instance

end EtaleSquare

/-- **Every chart square has a transition isomorphism, given transitions for squares over the
identity of the base with étale map of total spaces** (`hEt`): the gap square of a chart square
is such a square. -/
theorem ChartSquare.hasRelDualizingTransition_of_etale {X S X' S' : Scheme.{u}} {f : X ⟶ S}
    {f' : X' ⟶ S'} [Flat f] [LocallyOfFinitePresentation f] [Flat f']
    [LocallyOfFinitePresentation f'] (sq : ChartSquare f f')
    (hEt : ∀ {Y T X' : Scheme.{u}} {fY : Y ⟶ T} {f' : X' ⟶ T} [Flat fY]
      [LocallyOfFinitePresentation fY] [Flat f'] [LocallyOfFinitePresentation f'] (e : X' ⟶ Y)
      [Etale e] (comm : e ≫ fY = f' ≫ 𝟙 T), Scheme.Hom.HasRelDualizingTransition e (𝟙 T) comm) :
    HasRelDualizingTransition sq.g' sq.g sq.comm := by
  have : Etale sq.gap := sq.etale_gap
  exact sq.hasRelDualizingTransition_of_gap (hEt sq.gap sq.gap_comm)

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase} {F : CurveFamily B hZ}

/-! ### The module system of the relative dualizing sheaves of the charts -/

/-- A morphism of étale charts of the total space lies over the base. -/
theorem toOver_map_comp_chartToBase {U V : Space.SmallEtale B integerBase hZ F.total.1}
    (g : V ⟶ U) :
    (Space.SmallEtale.toOver B integerBase hZ F.total.1).map g ≫ F.chartToBase U =
      F.chartToBase V := by
  apply Yoneda.fullyFaithful.map_injective
  rw [Functor.map_comp, yoneda_map_chartToBase, yoneda_map_chartToBase, ← Category.assoc,
    Space.yoneda_map_toOver_map_comp_hom]

/-- The square of a morphism of étale charts over the identity of the base commutes. -/
theorem chartSchemeMap_comp_chartMorphism {U V : Space.SmallEtale B integerBase hZ F.total.1}
    (g : V ⟶ U) :
    Space.chartSchemeMap g ≫ F.chartMorphism U = F.chartMorphism V ≫ 𝟙 _ := by
  rw [Category.comp_id]
  exact ((BigFppfOver.toScheme B integerBase hZ).map_comp _ _).symm.trans
    (congrArg (BigFppfOver.toScheme B integerBase hZ).map (toOver_map_comp_chartToBase g))

/-- **The chart square of a morphism of étale charts** `g : V ⟶ U`, from `U ⟶ S` to `V ⟶ S`
over the identity of `S`. -/
abbrev chartHomChartSquare {U V : Space.SmallEtale B integerBase hZ F.total.1} (g : V ⟶ U) :
    Scheme.Hom.ChartSquare (F.chartMorphism U) (F.chartMorphism V) :=
  haveI := Space.etale_chartSchemeMap g
  Scheme.Hom.ChartSquare.ofEtale (Space.chartSchemeMap g) (chartSchemeMap_comp_chartMorphism g)

/-- For a nodal family, the relative dualizing complex of a chart has no cohomology above
degree `-1`. -/
theorem isLE_chartDualizingComplex (hF : Space.IsAtWorstNodalOfRelativeDimensionOne B
      integerBase hZ F.toBase.hom) (U : Space.SmallEtale B integerBase hZ F.total.1) :
    letI := HasDerivedCategory.standard
      (StrictlyPerfect.OXMod.{u, u} (Space.chartScheme U).toRingedSpace)
    DerivedCategory.TStructure.t.IsLE (F.chartDualizingComplex U) (-1) :=
  let (T : RingedSpace.{u, u}) :=
    HasDerivedCategory.standard (StrictlyPerfect.OXMod.{u, u} T)
  let (T : Scheme.{u}) := HasDerivedCategory.standard T.Modules
  letI (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules (structureSheafRing T.toRingedSpace))
  (DerivedCategory.isLE_iff _ _).2 fun i hi => (chartDualizingComplex_shape hF U).1 i (by omega)

variable (F)

/-- **The transition of the relative dualizing sheaves of two charts**: for a morphism of étale
charts `g : V ⟶ U`, the module transition `g^*ω_{U/S} ≅ ω_{V/S}` of its chart square. -/
def chartDualizingTransition (hF : Space.IsAtWorstNodalOfRelativeDimensionOne B
      integerBase hZ F.toBase.hom)
    (hEt : ∀ {Y T X' : Scheme.{u}} {fY : Y ⟶ T} {f' : X' ⟶ T} [Flat fY]
      [LocallyOfFinitePresentation fY] [Flat f'] [LocallyOfFinitePresentation f'] (e : X' ⟶ Y)
      [Etale e] (comm : e ≫ fY = f' ≫ 𝟙 T), Scheme.Hom.HasRelDualizingTransition e (𝟙 T) comm)
    {U V : Space.SmallEtale B integerBase hZ F.total.1} (g : V ⟶ U) :
    (Scheme.Modules.pullback (Space.chartSchemeMap g)).obj (F.chartDualizingSheaf U) ≅
      F.chartDualizingSheaf V :=
  Scheme.Hom.relDualizingModuleTransition (chartHomChartSquare g).g' (chartHomChartSquare g).g
    (chartHomChartSquare g).comm
    ((chartHomChartSquare g).hasRelDualizingTransition_of_etale hEt)
    (isLE_chartDualizingComplex hF U)

/-- **The cocycle condition of the transitions of the relative dualizing sheaves of the
charts.** -/
theorem isChartSchemeModuleCocycle_chartDualizingTransition
    (hF : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F.toBase.hom)
    (hEt : ∀ {Y T X' : Scheme.{u}} {fY : Y ⟶ T} {f' : X' ⟶ T} [Flat fY]
      [LocallyOfFinitePresentation fY] [Flat f'] [LocallyOfFinitePresentation f'] (e : X' ⟶ Y)
      [Etale e] (comm : e ≫ fY = f' ≫ 𝟙 T), Scheme.Hom.HasRelDualizingTransition e (𝟙 T) comm) :
    Space.IsChartSchemeModuleCocycle B integerBase hZ F.total F.chartDualizingSheaf
      (fun g => F.chartDualizingTransition hF hEt g) := by
  intro W V U g h
  exact Scheme.Hom.relDualizingModuleTransition_comp _ _ _ (Category.id_comp _) _ _ _
    (isLE_chartDualizingComplex hF U) (isLE_chartDualizingComplex hF V)

/-- **The chart-scheme module system of the relative dualizing sheaves of the charts** of a
nodal family of curves: `ω_{U/S}` on the scheme of every étale chart `U`, with the module
transitions of the chart squares of the morphisms of charts. -/
def dualizingSystem (hF : Space.IsAtWorstNodalOfRelativeDimensionOne B
      integerBase hZ F.toBase.hom)
    (hEt : ∀ {Y T X' : Scheme.{u}} {fY : Y ⟶ T} {f' : X' ⟶ T} [Flat fY]
      [LocallyOfFinitePresentation fY] [Flat f'] [LocallyOfFinitePresentation f'] (e : X' ⟶ Y)
      [Etale e] (comm : e ≫ fY = f' ≫ 𝟙 T), Scheme.Hom.HasRelDualizingTransition e (𝟙 T) comm) :
    Space.ChartSchemeModuleSystem B integerBase hZ F.total where
  M := F.chartDualizingSheaf
  isQuasicoherent U := by
    have := isInvertibleModule_chartDualizingSheaf hF U
    exact Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _
  τ g := F.chartDualizingTransition hF hEt g
  cocycle := F.isChartSchemeModuleCocycle_chartDualizingTransition hF hEt

/-! ### The relative dualizing sheaf -/

/-- **The relative dualizing sheaf `ω_{X/S}` of a nodal family of curves**: the module on the
small étale site of the total space glued from the relative dualizing sheaves of the charts. -/
def gluedRelativeDualizingSheaf (hF : Space.IsAtWorstNodalOfRelativeDimensionOne B
      integerBase hZ F.toBase.hom)
    (hEt : ∀ {Y T X' : Scheme.{u}} {fY : Y ⟶ T} {f' : X' ⟶ T} [Flat fY]
      [LocallyOfFinitePresentation fY] [Flat f'] [LocallyOfFinitePresentation f'] (e : X' ⟶ Y)
      [Etale e] (comm : e ≫ fY = f' ≫ 𝟙 T), Scheme.Hom.HasRelDualizingTransition e (𝟙 T) comm) :
    Space.Modules.{u, u} B integerBase hZ F.total.1 F.total.2 :=
  (F.dualizingSystem hF hEt).glue

/-- **The relative dualizing sheaf of a nodal family of curves is invertible** on the small
étale ringed site of the total space: its chart modules are invertible. -/
theorem isInvertible_relativeDualizingSheaf (hF : Space.IsAtWorstNodalOfRelativeDimensionOne B
      integerBase hZ F.toBase.hom)
    (hEt : ∀ {Y T X' : Scheme.{u}} {fY : Y ⟶ T} {f' : X' ⟶ T} [Flat fY]
      [LocallyOfFinitePresentation fY] [Flat f'] [LocallyOfFinitePresentation f'] (e : X' ⟶ Y)
      [Etale e] (comm : e ≫ fY = f' ≫ 𝟙 T), Scheme.Hom.HasRelDualizingTransition e (𝟙 T) comm) :
    Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ F.total.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ F.total.1 F.total.2).O)).property
      (F.gluedRelativeDualizingSheaf hF hEt) :=
  (F.dualizingSystem hF hEt).isInvertible_glue fun U => isInvertibleModule_chartDualizingSheaf hF U

end AlgebraicGeometry.CurveFamily

end
