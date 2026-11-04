module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import StacksFrontier.AlgebraicGeometry.FormalSpace.StructureSheaf.Construction

/-!
# Existence of structure sheaves, given Stacks 0DEH

Let `X` be a formal algebraic space over `S`. Under the correspondence of Stacks 0DEH between
affine étale formal charts and affine objects of `X_affine,étale`
(`AlgebraicGeometry.FormalSpace.Reduction.AffineEtaleCorrespondence`), the sheaf
`W ↦ 𝒪(U_W)` on `X_affine,étale` extends, by the equivalence of topoi of Stacks 0DEB (the
affine étale charts form a dense subsite of `X_étale`, Stacks 04JS), to a sheaf of topological
rings on `X_étale`, and that sheaf is a structure sheaf for `X` in the sense of Section 0DEI.

## Main definitions

* `AlgebraicGeometry.FormalSpace.Reduction.AffineEtaleCorrespondence.structureSheaf`: the
  sheaf of topological rings on `X_étale`.
* `AlgebraicGeometry.FormalSpace.Reduction.AffineEtaleCorrespondence.chartIso`: a chart with a
  reduction square at `W` is canonically isomorphic to the chosen chart `U_W`.

## Main results

* `AlgebraicGeometry.FormalSpace.isStructureSheaf_structureSheaf`: the sheaf `structureSheaf` is a
  structure sheaf for `X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : FppfSheaf B S hS}

namespace Reduction

namespace AffineEtaleCorrespondence

variable {R : Reduction B S hS X} (hC : R.AffineEtaleCorrespondence)

/-! ### Comparison of charts with the same reduction -/

/-- A chart `U` with a reduction square at `W` maps to the chosen chart `U_W`. -/
noncomputable def chartComparison {U : AffineEtaleFormalCharts B S hS X} {W : R.AffineEtale}
    {a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (R.affineChartObj W) ⟶
      U.obj.left} (ha : R.IsReductionSquare U W a) : U ⟶ hC.chart W :=
  (hC.existsUnique_hom ha (hC.isReductionSquare_chart W) (𝟙 W)).exists.choose

/-- The comparison square over the identity of `W` is just a composite with the map `b`. -/
private theorem map_id_comp_eq_iff {W : R.AffineEtale} {T : _}
    (b : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (R.affineChartObj W) ⟶ T)
    (x : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (R.affineChartObj W) ⟶ T) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      ((Space.AffineEtale.toOver B S hS R.space.obj).map (𝟙 W)) ≫ b = x ↔ b = x := by
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The map `a` of the reduction square, followed by the comparison `U ⟶ U_W`, is the chart map
of `U_W`. -/
theorem chartComparison_spec {U : AffineEtaleFormalCharts B S hS X} {W : R.AffineEtale}
    {a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (R.affineChartObj W) ⟶
      U.obj.left} (ha : R.IsReductionSquare U W a) :
    a ≫ (hC.chartComparison ha).hom.left = hC.chartMap W := by
  exact ((map_id_comp_eq_iff _ _).1
    (hC.existsUnique_hom ha (hC.isReductionSquare_chart W) (𝟙 W)).exists.choose_spec).symm

/-- The comparison of charts is compatible with morphisms of charts and of reductions. -/
theorem chartComparison_comp {U V : AffineEtaleFormalCharts B S hS X} {W W' : R.AffineEtale}
    {a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (R.affineChartObj W) ⟶
      U.obj.left}
    {a' : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (R.affineChartObj W') ⟶
      V.obj.left} (ha : R.IsReductionSquare U W a) (ha' : R.IsReductionSquare V W' a')
    (g : U ⟶ V) (h : W ⟶ W')
    (hgh : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((Space.AffineEtale.toOver B S hS R.space.obj).map h) ≫ a' = a ≫ g.hom.left) :
    hC.chartComparison ha ≫ hC.chartHom h = g ≫ hC.chartComparison ha' := by
  refine (hC.existsUnique_hom ha (hC.isReductionSquare_chart W') h).unique ?_ ?_
  · rw [hC.chartHom_comm, ← hC.chartComparison_spec ha, Category.assoc]
    rfl
  · rw [← hC.chartComparison_spec ha', ← Category.assoc, hgh, Category.assoc]
    rfl

/-- The inverse comparison, from the chosen chart `U_W` to a chart `U` with a reduction square at
`W`. -/
noncomputable def chartComparisonInv {U : AffineEtaleFormalCharts B S hS X} {W : R.AffineEtale}
    {a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (R.affineChartObj W) ⟶
      U.obj.left} (ha : R.IsReductionSquare U W a) : hC.chart W ⟶ U :=
  (hC.existsUnique_hom (hC.isReductionSquare_chart W) ha (𝟙 W)).exists.choose

/-- The chart map of `U_W` composed with the inverse comparison `U_W ⟶ U` is the map `a`. -/
theorem chartComparisonInv_spec {U : AffineEtaleFormalCharts B S hS X} {W : R.AffineEtale}
    {a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (R.affineChartObj W) ⟶
      U.obj.left} (ha : R.IsReductionSquare U W a) :
    hC.chartMap W ≫ (hC.chartComparisonInv ha).hom.left = a := by
  exact ((map_id_comp_eq_iff _ _).1
    (hC.existsUnique_hom (hC.isReductionSquare_chart W) ha (𝟙 W)).exists.choose_spec).symm

/-- **A chart with a reduction square at `W` is canonically isomorphic to `U_W`.** -/
noncomputable def chartIso {U : AffineEtaleFormalCharts B S hS X} {W : R.AffineEtale}
    {a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (R.affineChartObj W) ⟶
      U.obj.left} (ha : R.IsReductionSquare U W a) : U ≅ hC.chart W where
  hom := hC.chartComparison ha
  inv := hC.chartComparisonInv ha
  hom_inv_id := by
    refine (hC.existsUnique_hom ha ha (𝟙 W)).unique ?_ ?_
    · rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
      refine (hC.chartComparisonInv_spec ha).symm.trans ?_
      rw [← hC.chartComparison_spec ha, Category.assoc]
      rfl
    · rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
      exact (Category.comp_id a).symm
  inv_hom_id := by
    refine (hC.existsUnique_hom (hC.isReductionSquare_chart W) (hC.isReductionSquare_chart W)
      (𝟙 W)).unique ?_ ?_
    · simp only [CategoryTheory.Functor.map_id, Category.id_comp]
      refine (hC.chartComparison_spec ha).symm.trans ?_
      calc a ≫ (hC.chartComparison ha).hom.left
          = (hC.chartMap W ≫ (hC.chartComparisonInv ha).hom.left) ≫
              (hC.chartComparison ha).hom.left := by rw [hC.chartComparisonInv_spec ha]
        _ = hC.chartMap W ≫ (hC.chartComparisonInv ha ≫ hC.chartComparison ha).hom.left :=
          Category.assoc _ _ _
    · rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
      exact (Category.comp_id _).symm

/-- The forward map of `chartIso` is `chartComparison`. -/
@[simp]
theorem chartIso_hom {U : AffineEtaleFormalCharts B S hS X} {W : R.AffineEtale}
    {a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (R.affineChartObj W) ⟶
      U.obj.left} (ha : R.IsReductionSquare U W a) :
    (hC.chartIso ha).hom = hC.chartComparison ha :=
  rfl

/-! ### The structure sheaf on `X_étale` -/

omit hC in
/-- The affine étale charts form a dense subsite of `X_étale` (Stacks 04JS). -/
theorem _root_.AlgebraicGeometry.FormalSpace.Reduction.isDenseSubsite_affineEtaleInclusion
    (R : Reduction B S hS X) :
    (Space.AffineEtale.inclusion B S hS R.space.obj).IsDenseSubsite R.affineEtaleTopology
      R.smallEtaleTopology :=
  (Space.AffineEtale.inclusion_isSpecialCocontinuous B S hS R.space.obj R.space.property).2

/-- The sheaf `W ↦ 𝒪(U_W)` on `X_affine,étale`. -/
noncomputable def affineSheaf : Sheaf R.affineEtaleTopology TopCommRingCat.{u + 1} :=
  ⟨hC.affinePresheaf, hC.isSheaf_affinePresheaf⟩

/-- **The structure sheaf on `X_étale`**: the extension of `W ↦ 𝒪(U_W)` along the equivalence
of the affine étale topos with the small étale topos (Stacks 0DEB). -/
noncomputable def structureSheaf : Sheaf R.smallEtaleTopology TopCommRingCat.{u + 1} :=
  haveI := R.isDenseSubsite_affineEtaleInclusion
  (Functor.IsDenseSubsite.sheafEquiv (G := Space.AffineEtale.inclusion B S hS R.space.obj)
    (J := R.affineEtaleTopology) (K := R.smallEtaleTopology)
    (A := TopCommRingCat.{u + 1})).functor.obj hC.affineSheaf

/-- The restriction of the structure sheaf to `X_affine,étale` is `W ↦ 𝒪(U_W)`. -/
noncomputable def structureSheafRestrictIso :
    haveI := R.isDenseSubsite_affineEtaleInclusion
    ((Space.AffineEtale.inclusion B S hS R.space.obj).sheafPushforwardContinuous
      TopCommRingCat.{u + 1} R.affineEtaleTopology R.smallEtaleTopology).obj hC.structureSheaf ≅
      hC.affineSheaf :=
  haveI := R.isDenseSubsite_affineEtaleInclusion
  ((Functor.IsDenseSubsite.sheafEquiv (G := Space.AffineEtale.inclusion B S hS R.space.obj)
    (J := R.affineEtaleTopology) (K := R.smallEtaleTopology)
    (A := TopCommRingCat.{u + 1})).unitIso.app
      hC.affineSheaf).symm

/-- The sections of the structure sheaf over an affine object `W` of `X_étale` are `𝒪(U_W)`. -/
noncomputable def sectionsIso (W : R.AffineEtale) :
    hC.structureSheaf.obj.obj (op ((Space.AffineEtale.inclusion B S hS R.space.obj).obj W)) ≅
      ringOfFunctions (hC.chart W).obj.left :=
  ((sheafToPresheaf _ _).mapIso hC.structureSheafRestrictIso).app (op W)

/-- The isomorphisms `sectionsIso` are natural in the affine object `W`. -/
theorem sectionsIso_naturality {W W' : R.AffineEtale} (h : W ⟶ W') :
    hC.structureSheaf.obj.map ((Space.AffineEtale.inclusion B S hS R.space.obj).map h).op ≫
        (hC.sectionsIso W).hom =
      (hC.sectionsIso W').hom ≫ ringOfFunctionsMap (hC.chartHom h).hom.left :=
  (hC.structureSheafRestrictIso.hom.hom.naturality h.op)

/-- The comparison of the sections of the structure sheaf over the reduction `W` of a chart `U`
with the limit over the stages of a presentation of `U`. -/
noncomputable def sectionsLimitIso {U : AffineEtaleFormalCharts B S hS X} {W : R.AffineEtale}
    {a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (R.affineChartObj W) ⟶
      U.obj.left} (ha : R.IsReductionSquare U W a)
    (P : ThickeningPresentation B S hS U.obj.left) :
    hC.structureSheaf.obj.obj (op ((Space.AffineEtale.inclusion B S hS R.space.obj).obj W)) ≅
      limit P.rings :=
  hC.sectionsIso W ≪≫
    (ringOfFunctionsFunctor B S hS).mapIso
      ((AffineEtaleFormalCharts.forget X).mapIso (hC.chartIso ha)).op ≪≫
    P.ringOfFunctionsIso

/-- The forward map of `sectionsLimitIso` is `sectionsIso`, followed by the map on rings of
functions induced by `chartComparison` and by `ThickeningPresentation.ringOfFunctionsIso`. -/
theorem sectionsLimitIso_hom {U : AffineEtaleFormalCharts B S hS X} {W : R.AffineEtale}
    {a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (R.affineChartObj W) ⟶
      U.obj.left} (ha : R.IsReductionSquare U W a)
    (P : ThickeningPresentation B S hS U.obj.left) :
    (hC.sectionsLimitIso ha P).hom = (hC.sectionsIso W).hom ≫
      ringOfFunctionsMap (hC.chartComparison ha).hom.left ≫ P.ringOfFunctionsIso.hom :=
  rfl

/-- The forward map of `sectionsLimitIso` followed by the projection to the stage `i` is
`sectionsIso` followed by evaluation at the image under `chartComparison` of the point of stage
`i`. -/
@[reassoc]
theorem sectionsLimitIso_hom_π {U : AffineEtaleFormalCharts B S hS X} {W : R.AffineEtale}
    {a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (R.affineChartObj W) ⟶
      U.obj.left} (ha : R.IsReductionSquare U W a)
    (P : ThickeningPresentation B S hS U.obj.left) (i : P.Index) :
    (hC.sectionsLimitIso ha P).hom ≫ limit.π P.rings (op i) =
      (hC.sectionsIso W).hom ≫ ringOfFunctionsπ (hC.chart W).obj.left (P.diagram.obj i)
        ((hC.chartComparison ha).hom.left.hom.app _ (P.point i)) := by
  rw [sectionsLimitIso_hom, Category.assoc, Category.assoc,
    ThickeningPresentation.ringOfFunctionsIso_hom_π]
  exact congrArg ((hC.sectionsIso W).hom ≫ ·) (ringOfFunctionsMap_π _ _ _)

/-- The stage inclusion of a presentation, followed by a morphism of charts, as a section. -/
theorem app_point_eq_sectionEquiv {U V : AffineEtaleFormalCharts B S hS X}
    (P : ThickeningPresentation B S hS U.obj.left) (i : P.Index) (f : U.obj.left ⟶ V.obj.left) :
    f.hom.app _ (P.point i) =
      Sheaf.sectionEquiv (BigFppfOver.topology B S hS) (P.stageMap i ≫ f) :=
  (Sheaf.sectionEquiv_comp (BigFppfOver.topology B S hS) (P.stageMap i) f).symm

end AffineEtaleCorrespondence

end Reduction

/-- **Stacks 0DEJ, given Stacks 0DEH.** Under the correspondence of Stacks 0DEH between affine
étale formal charts over a formal algebraic space `X` and affine objects of `X_affine,étale`, the
sheaf `AlgebraicGeometry.FormalSpace.Reduction.AffineEtaleCorrespondence.structureSheaf` is a
structure sheaf for `X`. -/
theorem isStructureSheaf_structureSheaf (hX : IsFormalAlgebraicSpace B S hS X)
    (hC : (canonicalReduction hX).AffineEtaleCorrespondence) :
    IsStructureSheaf hX hC.structureSheaf := by
  refine ⟨fun U W a ha P => hC.sectionsLimitIso ha P, ?_⟩
  intro U V W W' a a' ha ha' g h hgh P Q i j t ht
  beta_reduce
  have hpt : (hC.chartHom h).hom.left.hom.app _
        ((hC.chartComparison ha).hom.left.hom.app _ (P.point i)) =
      (hC.chart W').obj.left.obj.map ((BigAffineFppf.inclusion B S hS).map t).op
        ((hC.chartComparison ha').hom.left.hom.app _ (Q.point j)) := by
    have hmor : P.stageMap i ≫ (hC.chartComparison ha).hom.left ≫ (hC.chartHom h).hom.left =
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map t) ≫ Q.stageMap j ≫
            (hC.chartComparison ha').hom.left := by
      have hc := congrArg (fun k => k.hom.left) (hC.chartComparison_comp ha ha' g h hgh)
      rw [← Category.assoc ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map t)), ht, Category.assoc]
      exact congrArg (P.stageMap i ≫ ·) hc
    calc (hC.chartHom h).hom.left.hom.app _
          ((hC.chartComparison ha).hom.left.hom.app _ (P.point i))
        = Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
            ((P.stageMap i ≫ (hC.chartComparison ha).hom.left) ≫ (hC.chartHom h).hom.left) := by
          rw [Sheaf.sectionEquiv_comp]
          rfl
      _ = Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
            ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
              ((BigAffineFppf.inclusion B S hS).map t) ≫ Q.stageMap j ≫
                (hC.chartComparison ha').hom.left) := by
          rw [Category.assoc, hmor]
      _ = _ := by
          rw [Sheaf.sectionEquiv_map_comp, Sheaf.sectionEquiv_comp]
          rfl
  rw [hC.sectionsLimitIso_hom_π ha P i, hC.sectionsLimitIso_hom_π_assoc ha' Q j, ← Category.assoc,
    hC.sectionsIso_naturality h, Category.assoc, ringOfFunctionsMap_π, ringOfFunctionsπ_map]
  exact congrArg (fun x => (hC.sectionsIso W').hom ≫
    ringOfFunctionsπ (hC.chart W').obj.left (P.diagram.obj i) x) hpt

end AlgebraicGeometry.FormalSpace

end
