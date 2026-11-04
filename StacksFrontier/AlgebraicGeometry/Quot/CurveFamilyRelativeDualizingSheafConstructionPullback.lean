module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyRelativeDualizingSheafConstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleSystem.Pullback

/-!
# The relative dualizing sheaves of nodal families along a morphism of families

Let `φ : F' ⟶ F` be a morphism of families of curves (a cartesian square of algebraic spaces over
the map of bases `S' ⟶ S`), both at-worst-nodal of relative dimension one. A chart square of the
morphism of total spaces (an étale chart `W` of `X'`, an étale chart `V` of `X` and a morphism
`g : W ⟶ V` over `X' ⟶ X`) gives a chart square of schemes from `V ⟶ S` to `W ⟶ S'`
(`AlgebraicGeometry.CurveFamily.Hom.toSchemeChartSquare`): its gap map `W ⟶ V ×_S S'` is étale
(`AlgebraicGeometry.CurveFamily.Hom.etale_chartGap`). The module transition of that square is an
identification `g^*ω_{V/S} ≅ ω_{W/S'}` (`AlgebraicGeometry.CurveFamily.Hom.dualizingComparison`),
and the cocycle law of module transitions makes these identifications compatible with the
transitions of the two chart systems of relative dualizing sheaves
(`AlgebraicGeometry.CurveFamily.Hom.comparisonCompatTarget_dualizingComparison`,
`AlgebraicGeometry.CurveFamily.Hom.comparisonCompatSource_dualizingComparison`).

The transitions of chart squares whose gap map is étale over the identity of the base are taken as
the hypothesis `hEt`, as in
`StacksFrontier/AlgebraicGeometry/Quot/CurveFamilyRelativeDualizingSheafConstruction.lean`.

## Main definitions

* `AlgebraicGeometry.CurveFamily.Hom.toSchemeChartSquare`: the chart square of schemes of a chart
  square of the morphism of total spaces.
* `AlgebraicGeometry.CurveFamily.Hom.dualizingComparison`: the comparisons `g^*ω_{V/S} ≅ ω_{W/S'}`.

## Main results

* `AlgebraicGeometry.CurveFamily.Hom.comparisonCompatTarget_dualizingComparison` and
  `AlgebraicGeometry.CurveFamily.Hom.comparisonCompatSource_dualizingComparison`.
* `AlgebraicGeometry.CurveFamily.isAtWorstNodal_of_hom`: a family mapping to a nodal family is
  nodal.
* `AlgebraicGeometry.CurveFamily.nonempty_baseChangeModule_iso_of_fibrePullbackIso`: the fibre
  clause of the relative dualizing sheaf, given an identification of its pullback to the fibre
  family with the relative dualizing sheaf of the fibre family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- Solving an equation `y = P.hom.app M ≫ x` of morphisms out of `F.obj M`, for a natural
isomorphism `P : F ≅ G`. -/
theorem hom_eq_inv_app_comp_of_eq {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (P : F ≅ G) (M : C) {Z : D} {x : G.obj M ⟶ Z} {y : F.obj M ⟶ Z}
    (h : y = P.hom.app M ≫ x) : x = P.inv.app M ≫ y := by
  rw [h, Iso.inv_hom_id_app_assoc]

/-- **A family of curves mapping to a nodal family is nodal**: it is a base change of it
(Stacks 0C5B). -/
theorem isAtWorstNodal_of_hom {F' F : CurveFamily B hZ} (φ : F' ⟶ F)
    (hF : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F.toBase.hom) :
    Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F'.toBase.hom :=
  have h : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃G H : AlgebraicSpaces B integerBase hZ⦄ (k : G ⟶ H) =>
        Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ k.hom) :=
    Space.isAtWorstNodalOfRelativeDimensionOne_isStableUnderBaseChange B integerBase hZ
  h.of_isPullback φ.cartesian hF

namespace Hom

variable {F' F : CurveFamily B hZ} (φ : F' ⟶ F)

/-- The square of schemes of a chart square of the morphism of total spaces commutes. -/
theorem toScheme_chartSquare_comm (q : Space.ChartSchemeModuleSystem.ChartSquare φ.totalMap) :
    (BigFppfOver.toScheme B integerBase hZ).map q.g ≫ F.chartMorphism q.V =
      F'.chartMorphism q.W ≫ (BigFppfOver.toScheme B integerBase hZ).map φ.baseMap :=
  ((BigFppfOver.toScheme B integerBase hZ).map_comp _ _).symm.trans
    ((congrArg (BigFppfOver.toScheme B integerBase hZ).map (φ.chartToBase_comm q.w)).trans
      ((BigFppfOver.toScheme B integerBase hZ).map_comp _ _))

/-- The gap map `W ⟶ V ×_S S'` of schemes of a chart square of the morphism of total spaces is
étale: it is the gap map of the site followed by the comparison of fibre products. -/
theorem etale_toScheme_chartGap (q : Space.ChartSchemeModuleSystem.ChartSquare φ.totalMap) :
    Etale (pullback.lift ((BigFppfOver.toScheme B integerBase hZ).map q.g) (F'.chartMorphism q.W)
      (φ.toScheme_chartSquare_comm q)) := by
  have hpres : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B integerBase hZ) := by
    dsimp [BigFppfOver.toScheme]
    infer_instance
  have := φ.etale_chartGap q.w
  have h : pullback.lift ((BigFppfOver.toScheme B integerBase hZ).map q.g) (F'.chartMorphism q.W)
      (φ.toScheme_chartSquare_comm q) =
        (BigFppfOver.toScheme B integerBase hZ).map (φ.chartGap q.w) ≫
          (PreservesPullback.iso (BigFppfOver.toScheme B integerBase hZ) (F.chartToBase q.V)
            φ.baseMap).hom := by
    apply pullback.hom_ext <;>
      simp only [pullback.lift_fst, pullback.lift_snd, Category.assoc,
        PreservesPullback.iso_hom_fst, PreservesPullback.iso_hom_snd, ← Functor.map_comp, chartGap]
  rw [h]
  infer_instance

/-- **The chart square of schemes of a chart square of the morphism of total spaces**: from
`V ⟶ S` to `W ⟶ S'`, with étale gap map. -/
abbrev toSchemeChartSquare (q : Space.ChartSchemeModuleSystem.ChartSquare φ.totalMap) :
    Scheme.Hom.ChartSquare (F.chartMorphism q.V) (F'.chartMorphism q.W) where
  g' := (BigFppfOver.toScheme B integerBase hZ).map q.g
  g := (BigFppfOver.toScheme B integerBase hZ).map φ.baseMap
  comm := φ.toScheme_chartSquare_comm q
  etale_gap := φ.etale_toScheme_chartGap q

/-- **The comparison of relative dualizing sheaves on a chart square** of the morphism of total
spaces: the module transition `g^*ω_{V/S} ≅ ω_{W/S'}` of its chart square of schemes. -/
def dualizingComparison
    (hF : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F.toBase.hom)
    (hEt : ∀ {Y T X' : Scheme.{u}} {fY : Y ⟶ T} {f' : X' ⟶ T} [Flat fY]
      [LocallyOfFinitePresentation fY] [Flat f'] [LocallyOfFinitePresentation f'] (e : X' ⟶ Y)
      [Etale e] (comm : e ≫ fY = f' ≫ 𝟙 T), Scheme.Hom.HasRelDualizingTransition e (𝟙 T) comm)
    (q : Space.ChartSchemeModuleSystem.ChartSquare φ.totalMap) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B integerBase hZ).map q.g)).obj
        (F.chartDualizingSheaf q.V) ≅ F'.chartDualizingSheaf q.W :=
  Scheme.Hom.relDualizingModuleTransition (φ.toSchemeChartSquare q).g' (φ.toSchemeChartSquare q).g
    (φ.toSchemeChartSquare q).comm
    ((φ.toSchemeChartSquare q).hasRelDualizingTransition_of_etale hEt)
    (isLE_chartDualizingComplex hF q.V)

/-- **The comparisons are compatible with the transitions of the target system.** -/
theorem comparisonCompatTarget_dualizingComparison
    (hF : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F.toBase.hom)
    (hF' : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F'.toBase.hom)
    (hEt : ∀ {Y T X' : Scheme.{u}} {fY : Y ⟶ T} {f' : X' ⟶ T} [Flat fY]
      [LocallyOfFinitePresentation fY] [Flat f'] [LocallyOfFinitePresentation f'] (e : X' ⟶ Y)
      [Etale e] (comm : e ≫ fY = f' ≫ 𝟙 T), Scheme.Hom.HasRelDualizingTransition e (𝟙 T) comm) :
    Space.ChartSchemeModuleSystem.ComparisonCompatTarget (F.dualizingSystem hF hEt)
      (F'.dualizingSystem hF' hEt) (φ.dualizingComparison hF hEt) := by
  intro q V₀ k
  exact hom_eq_inv_app_comp_of_eq _ _
    (Scheme.Hom.relDualizingModuleTransition_comp _ _ _ (Category.comp_id _) _ _ _
      (isLE_chartDualizingComplex hF V₀) (isLE_chartDualizingComplex hF q.V))

/-- **The comparisons are compatible with the transitions of the source system.** -/
theorem comparisonCompatSource_dualizingComparison
    (hF : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F.toBase.hom)
    (hF' : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F'.toBase.hom)
    (hEt : ∀ {Y T X' : Scheme.{u}} {fY : Y ⟶ T} {f' : X' ⟶ T} [Flat fY]
      [LocallyOfFinitePresentation fY] [Flat f'] [LocallyOfFinitePresentation f'] (e : X' ⟶ Y)
      [Etale e] (comm : e ≫ fY = f' ≫ 𝟙 T), Scheme.Hom.HasRelDualizingTransition e (𝟙 T) comm) :
    Space.ChartSchemeModuleSystem.ComparisonCompatSource (F.dualizingSystem hF hEt)
      (F'.dualizingSystem hF' hEt) (φ.dualizingComparison hF hEt) := by
  intro q W₁ l
  exact hom_eq_inv_app_comp_of_eq _ _
    (Scheme.Hom.relDualizingModuleTransition_comp _ _ _ (Category.id_comp _) _ _ _
      (isLE_chartDualizingComplex hF q.V) (isLE_chartDualizingComplex hF' q.W))

end Hom

/-! ### The fibre clause, from the pullback to the fibre family -/

section Fibre

variable (X : CurveFamily B hZ)
  {p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj}
  {V : BigFppfOver B integerBase hZ} {v : V ⟶ p.siteObject} {q : yoneda.obj V ⟶ X.total.obj}

/-- **The fibre clause of the relative dualizing sheaf, from the fibre family.** If the pullback of
a module `ω` on the total space to the fibre family over a field-valued point is the relative
dualizing sheaf of the fibre family, then the pullback of `ω` to the fibre is the dualizing sheaf
of the fibre (Stacks 0BS2): it is read on the identity chart of the fibre, where the relative
dualizing sheaf of the fibre family is the one of the identity chart. -/
theorem nonempty_baseChangeModule_iso_of_fibrePullbackIso
    (hsq : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value))
    (hFib : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ
      (X.fibreFamily hsq).toBase.hom)
    (hEt : ∀ {Y T X' : Scheme.{u}} {fY : Y ⟶ T} {f' : X' ⟶ T} [Flat fY]
      [LocallyOfFinitePresentation fY] [Flat f'] [LocallyOfFinitePresentation f'] (e : X' ⟶ Y)
      [Etale e] (comm : e ≫ fY = f' ≫ 𝟙 T), Scheme.Hom.HasRelDualizingTransition e (𝟙 T) comm)
    (ω : Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
    (e : (Space.modulePullback B integerBase hZ (X.fibreFamilyHom hsq).totalMap).obj ω ≅
      (X.fibreFamily hsq).gluedRelativeDualizingSheaf hFib hEt)
    [hv : IsProper ((BigFppfOver.toScheme B integerBase hZ).map v)] :
    Nonempty (Space.baseChangeModule B integerBase hZ ω V q ≅
      Stacks.Duality.dualizingSheafOverField ((BigFppfOver.toScheme B integerBase hZ).map v)) := by
  obtain ⟨i⟩ := X.nonempty_chartDualizingSheaf_fibre_iso hsq
  exact ⟨(Space.restrictToChartSchemeFunctor B integerBase hZ (yoneda.obj V)
      (isAlgebraicSpace_yoneda B integerBase hZ V)
      (Space.idEtaleChart B integerBase hZ V)).mapIso e ≪≫
    ((X.fibreFamily hsq).dualizingSystem hFib hEt).restrictToChartSchemeGlueIso
      (Space.idEtaleChart B integerBase hZ V) ≪≫ i⟩

end Fibre

end AlgebraicGeometry.CurveFamily

end
