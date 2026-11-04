module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackOfGroupoidPointEval
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackArrowSections

/-!
# The comparison through the source on the module attached to `(𝒢, α)`

Let `ℱ` be the quasi-coherent module on `[U/R]` built from a quasi-coherent module `(𝒢, α)` on a
groupoid `(U, R, s, t, c)` in algebraic spaces, and let `ψ : 𝒢 ≅ x^*ℱ|_{U_étale}` be the
isomorphism of step E4 of the proof of Stacks 06WT. Over an affine étale chart `V` of `R`, the
composite of `s^*ψ` with the comparison map `c_s` of the triangle through the source
(Stacks 076R), read in `ℱ(x(s ∘ v)) = Γ(V, (s ∘ v)^*𝒢)`, is the chart section along the point
`v` of `V`. This is the source half of the compatibility of `ψ` with the transitions.

## Main results

* `AlgebraicGeometry.Stack.pointEval_sourceComparison`: the identity above, for affine `V`
  carrying an affine chart diagram over `s`.

## References

* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
* [Stacks Project, Tag 076R](https://stacks.math.columbia.edu/tag/076R)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

/-- Two additive maps out of a module which is the image of a base change, semilinear in the
same way, agree as soon as they agree on the images of `1 ⊗ m`. -/
theorem Stacks.eq_of_baseChange_surjective {R A M P Q : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] [AddCommGroup P] [Module A P] [AddCommGroup Q]
    (BC : TensorProduct R A M →ₗ[A] P) (hBC : Function.Surjective BC) (L L' : P →+ Q)
    (act : A → Q → Q) (hL : ∀ a p, L (a • p) = act a (L p)) (hL' : ∀ a p, L' (a • p) = act a (L' p))
    (h : ∀ m, L (BC ((1 : A) ⊗ₜ[R] m)) = L' (BC ((1 : A) ⊗ₜ[R] m))) (p : P) : L p = L' p := by
  obtain ⟨t, rfl⟩ := hBC p
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a m =>
    have e : a ⊗ₜ[R] m = a • ((1 : A) ⊗ₜ[R] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, map_smul, hL, hL', h]
  | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]

namespace AlgebraicGeometry.Stack

attribute [local instance] FibredSite.objModule

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
  (M : Space.QuasicoherentModule C S hS G)

/-- The affine point `(V, s ∘ v)` of `[U/_pR]` given by an affine étale chart `V` of `R`. -/
abbrev affineArrowChartPoint (V : Space.SmallEtale C S hS G.arrows.obj)
    (hV : IsAffine ((Space.SmallEtale.toOver C S hS G.arrows.obj ⋙
      BigFppfOver.toScheme C S hS).obj V)) :
    AffineCategory C S hS (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p :=
  ⟨arrowChartPoint G V, hV⟩

/-- **The source comparison on chart sections**: over a square `d'` of affine charts over `s`, the
section `c_s(s^*ψ(s^*x))` read in `Γ(V, (s ∘ v)^*𝒢)` is the chart section along `v` of `s^*x`. -/
theorem pointEval_sourceComparison_chartSection (V : Space.SmallEtale C S hS G.arrows.obj)
    (hV : IsAffine ((Space.SmallEtale.toOver C S hS G.arrows.obj ⋙
      BigFppfOver.toScheme C S hS).obj V)) (A : Space.AffineEtale C S hS G.objects.obj)
    (g : (Space.SmallEtale.toOver C S hS G.arrows.obj).obj V ⟶
      (Space.SmallEtale.toOver C S hS G.objects.obj).obj A.obj)
    (hg : V.1.hom ≫ G.source.hom = yoneda.map g ≫ A.obj.1.hom) (x : M.F.obj.val.obj (op A.obj)) :
    pointEval G M (affineArrowChartPoint G V hV)
        ((quotientStackSourceComparison G (quotientStackModuleOfGroupoid G M)).val.app (op V)
          (Space.modulePullbackChartSection C S hS G.source _ ⟨V, A.obj, g, hg⟩
            ((quotientStackModuleOfGroupoidHom G M).val.app (op A.obj) x))) =
      arrowChartRestrict G M V
        (Space.modulePullbackChartSection C S hS G.source M.F.obj ⟨V, A.obj, g, hg⟩ x) := by
  have hc : (quotientStackSourceComparison G (quotientStackModuleOfGroupoid G M)).val.app (op V)
      (Space.modulePullbackChartSection C S hS G.source _ ⟨V, A.obj, g, hg⟩
        ((quotientStackModuleOfGroupoidHom G M).val.app (op A.obj) x)) =
      (quotientStackModuleOfGroupoid G M).val.map (Space.comparisonMorphism C S hS
        (fibredCategory C S hS G.arrows.obj).val.p (fibredCategory C S hS G.objects.obj).val.p
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (quotientStackSourceLeg G) (quotientStackSourceLeg G ⋙ quotientStackProj G)
        (quotientStackProj G) (Iso.refl _) G.source (quotientStackSourceChartIso G)
        ⟨V, A.obj, g, hg⟩).op ((quotientStackModuleOfGroupoidHom G M).val.app (op A.obj) x) :=
    Space.comparisonAlgebraicSpacesModules_chartSection (d := ⟨V, A.obj, g, hg⟩)
      (s := (quotientStackModuleOfGroupoidHom G M).val.app (op A.obj) x) ..
  rw [quotientStackSource_comparisonMorphism] at hc
  have h1 := pointEval_map_quotientStackModuleOfGroupoidHom G M (affineArrowChartPoint G V hV) A
    (chartDiagramPoint G G.source.hom V A.obj g hg) x
  have hk0 : yoneda.map g ≫ A.obj.obj.hom = yonedaEquiv.symm (arrowChartPoint G V).fiber :=
    hg.symm.trans (congrArg (fun f => f.hom) (chartArrowMap_source G V))
  have hk : ∀ f, f = g → yoneda.map f ≫ A.obj.obj.hom =
      yonedaEquiv.symm (arrowChartPoint G V).fiber := by
    rintro f rfl
    exact hk0
  have hk' := hk ((chartDiagramPoint G G.source.hom V A.obj g hg).base ≫ 𝟙 _) (Category.comp_id g)
  have hk'' := hk (𝟙 _ ≫ g) (Category.id_comp g)
  have h2 := pointSectionRestrict_pointChartSection G M
    (chartDiagramPoint G G.source.hom V A.obj g hg)
    (pointwiseArrow_chartDiagramPoint G G.source.hom V A.obj g hg) A.obj (𝟙 _)
    (chartPoint_comm G A.obj) hk' x
  have h3 := chartRestrict_compIso_transport (chartArrowMap G V) G.source (chartArrowMap_source G V)
    M.F.obj (Space.selfChart C S hS _) V A.obj (𝟙 _) g (chartArrowMap_comm G V) hg
    (pointChartDiagram G (arrowChartPoint G V) A.obj _ hk'').comm x _ rfl
  refine (congrArg (pointEval G M (affineArrowChartPoint G V hV)) hc).trans ?_
  refine h1.trans (h2.trans ?_)
  refine Eq.trans ?_ h3.symm
  exact Space.modulePullbackChartSection_congr C S hS (pointMap G (arrowChartPoint G V)) M.F.obj
    (U := Space.selfChart C S hS _) (V := A.obj)
    (g₁ := (chartDiagramPoint G G.source.hom V A.obj g hg).base ≫ 𝟙 _) (g₂ := 𝟙 _ ≫ g)
    (pointChartDiagram G (arrowChartPoint G V) A.obj _ hk').comm
    (pointChartDiagram G (arrowChartPoint G V) A.obj _ hk'').comm
    ((Category.comp_id g).trans (Category.id_comp g).symm) x

/-- A function on a chart `V` of `R`, read on the identity chart of `V`. -/
def arrowSelfScalar (V : Space.SmallEtale C S hS G.arrows.obj)
    (r : Space.chartRing C S hS G.arrows.obj G.arrows.property V) :
    Space.chartRing C S hS (Space.yonedaSpace C S hS (arrowChartPoint G V).base).1
      (Space.yonedaSpace C S hS (arrowChartPoint G V).base).2
      (Space.selfChart C S hS (arrowChartPoint G V).base) := r

/-- A function on an affine chart `V` of `R`, read on the affine point `(V, s ∘ v)`. -/
def affineArrowScalar (V : Space.SmallEtale C S hS G.arrows.obj)
    (hV : IsAffine ((Space.SmallEtale.toOver C S hS G.arrows.obj ⋙
      BigFppfOver.toScheme C S hS).obj V))
    (r : Space.chartRing C S hS G.arrows.obj G.arrows.property V) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (AffineCategory.siteKindRingedSite C S hS
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
      (isFiberedInGroupoids_presheafOfGroupoids _) .fppf).chaotic.O).obj.obj
        (op (affineArrowChartPoint G V hV)) := r

/-- A function on a chart `V` of `R`, read on the point `(V, s ∘ v)` of `[U/_pR]`. -/
def pointArrowScalar (V : Space.SmallEtale C S hS G.arrows.obj)
    (r : Space.chartRing C S hS G.arrows.obj G.arrows.property V) :
    (FibredSite.ringStructureSheafCore C S hS (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
      (isFiberedInGroupoids_presheafOfGroupoids _) .fppf).obj.obj (op (arrowChartPoint G V)) := r

/-- A section of `(x ∘ s)^*ℱ|_{R_étale}` over a chart `V` of `R`, read as a section of `ℱ`. -/
def arrowPointSection (V : Space.SmallEtale C S hS G.arrows.obj)
    (p : (quotientStackArrowRestriction G (quotientStackModuleOfGroupoid G M)).val.obj (op V)) :
    (quotientStackModuleOfGroupoid G M).val.obj
      (op ((pointwiseToQuotientStack G).obj (arrowChartPoint G V))) := p

/-- Evaluation at the affine point `(V, s ∘ v)` is linear over the functions on the chart `V` of
`R`. -/
theorem pointEval_arrow_smul (V : Space.SmallEtale C S hS G.arrows.obj)
    (hV : IsAffine ((Space.SmallEtale.toOver C S hS G.arrows.obj ⋙
      BigFppfOver.toScheme C S hS).obj V))
    (r : Space.chartRing C S hS G.arrows.obj G.arrows.property V)
    (p : (quotientStackArrowRestriction G (quotientStackModuleOfGroupoid G M)).val.obj (op V)) :
    pointEval G M (affineArrowChartPoint G V hV) (r • p) =
      arrowSelfScalar G V r • pointEval G M (affineArrowChartPoint G V hV) p := by
  have h3 := (((pointwiseRestriction G).objObjPreimageIso (pointwiseModule G M)).hom.val.app
    (op (arrowChartPoint G V))).hom.map_smul (pointArrowScalar G V r) p
  have h2 := ((pointwiseModuleAffineIso G M).hom.val.app
    (op (affineArrowChartPoint G V hV))).hom.map_smul (affineArrowScalar G V hV r)
    (((pointwiseRestriction G).objObjPreimageIso (pointwiseModule G M)).hom.val.app
      (op (arrowChartPoint G V)) p)
  have h4 := quotientStackSourceProj_chartStructureHom_apply G V r
  unfold pointEval
  refine (congrArg (fun c : FibredSite.objRing C S hS (quotientStack G).p
      ((pointwiseToQuotientStack G).obj (arrowChartPoint G V)) =>
    (pointwiseModuleAffineIso G M).hom.val.app
    (op (affineArrowChartPoint G V hV)) (((pointwiseRestriction G).objObjPreimageIso
      (pointwiseModule G M)).hom.val.app (op (arrowChartPoint G V))
        (c • arrowPointSection G M V p))) h4).trans ?_
  exact (congrArg _ h3).trans h2

/-- `arrowChartRestrict` is linear over the functions on the chart `V` of `R`. -/
theorem arrowChartRestrict_smul (V : Space.SmallEtale C S hS G.arrows.obj)
    (r : Space.chartRing C S hS G.arrows.obj G.arrows.property V)
    (z : ((Space.modulePullback C S hS G.source).obj M.F.obj).val.obj (op V)) :
    arrowChartRestrict G M V (r • z) = arrowSelfScalar G V r • arrowChartRestrict G M V z := by
  unfold arrowChartRestrict arrowRestrict
  refine (chartRestrict_smul (chartArrowMap G V)
    ((Space.modulePullback C S hS G.source).obj M.F.obj)
    ((Space.modulePullback C S hS (pointMap G (arrowChartPoint G V))).obj M.F.obj)
    (comp₃ ((Space.modulePullbackCompIso C S hS (chartArrowMap G V) G.source).app M.F.obj).hom
      (Space.pullbackTransport M.F.obj (chartArrowMap_source G V)) (𝟙 _))
    ⟨Space.selfChart C S hS _, V, 𝟙 _, chartArrowMap_comm G V⟩ r z).trans ?_
  congr 1

/-- `arrowChartRestrict` is additive. -/
theorem arrowChartRestrict_add (V : Space.SmallEtale C S hS G.arrows.obj)
    (z z' : ((Space.modulePullback C S hS G.source).obj M.F.obj).val.obj (op V)) :
    arrowChartRestrict G M V (z + z') = arrowChartRestrict G M V z + arrowChartRestrict G M V z' :=
  chartRestrict_add (chartArrowMap G V) ((Space.modulePullback C S hS G.source).obj M.F.obj)
    ((Space.modulePullback C S hS (pointMap G (arrowChartPoint G V))).obj M.F.obj)
    (comp₃ ((Space.modulePullbackCompIso C S hS (chartArrowMap G V) G.source).app M.F.obj).hom
      (Space.pullbackTransport M.F.obj (chartArrowMap_source G V)) (𝟙 _))
    ⟨Space.selfChart C S hS _, V, 𝟙 _, chartArrowMap_comm G V⟩ z z'

/-- Evaluation of sections of `ℱ` at an affine point is additive. -/
theorem pointEval_add (X : AffineCategory C S hS (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p)
    (z z' : (quotientStackModuleOfGroupoid G M).val.obj
      (op ((pointwiseToQuotientStack G).obj X.obj))) :
    pointEval G M X (z + z') = pointEval G M X z + pointEval G M X z' := by
  have a1 := (((pointwiseRestriction G).objObjPreimageIso (pointwiseModule G M)).hom.val.app
    (op X.obj)).hom.map_add z z'
  have a2 := ((pointwiseModuleAffineIso G M).hom.val.app (op X)).hom.map_add
    (((pointwiseRestriction G).objObjPreimageIso (pointwiseModule G M)).hom.val.app (op X.obj) z)
    (((pointwiseRestriction G).objObjPreimageIso (pointwiseModule G M)).hom.val.app (op X.obj) z')
  unfold pointEval
  exact (congrArg _ a1).trans a2

/-- `z ↦ c_s(s^*ψ(z))` read in `Γ(V, (s ∘ v)^*𝒢)`, as an additive map. -/
def sourceComparisonEval (V : Space.SmallEtale C S hS G.arrows.obj)
    (hV : IsAffine ((Space.SmallEtale.toOver C S hS G.arrows.obj ⋙
      BigFppfOver.toScheme C S hS).obj V)) :
    ((Space.modulePullback C S hS G.source).obj M.F.obj).val.obj (op V) →+
      pointSections G M (arrowChartPoint G V) :=
  AddMonoidHom.mk' (fun z => pointEval G M (affineArrowChartPoint G V hV)
    ((quotientStackSourceComparison G (quotientStackModuleOfGroupoid G M)).val.app (op V)
      (((Space.modulePullback C S hS G.source).map (quotientStackModuleOfGroupoidHom G M)).val.app
        (op V) z))) (fun z z' => by
    rw [(((Space.modulePullback C S hS G.source).map
      (quotientStackModuleOfGroupoidHom G M)).val.app (op V)).hom.map_add z z',
      ((quotientStackSourceComparison G (quotientStackModuleOfGroupoid G M)).val.app
        (op V)).hom.map_add]
    exact pointEval_add G M _ _ _)

/-- `arrowChartRestrict` as an additive map. -/
def arrowChartRestrictHom (V : Space.SmallEtale C S hS G.arrows.obj) :
    ((Space.modulePullback C S hS G.source).obj M.F.obj).val.obj (op V) →+
      pointSections G M (arrowChartPoint G V) :=
  AddMonoidHom.mk' (arrowChartRestrict G M V) (arrowChartRestrict_add G M V)

/-- `sourceComparisonEval` unfolded. -/
private theorem sourceComparisonEval_apply (V : Space.SmallEtale C S hS G.arrows.obj)
    (hV : IsAffine ((Space.SmallEtale.toOver C S hS G.arrows.obj ⋙
      BigFppfOver.toScheme C S hS).obj V))
    (z : ((Space.modulePullback C S hS G.source).obj M.F.obj).val.obj (op V)) :
    sourceComparisonEval G M V hV z = pointEval G M (affineArrowChartPoint G V hV)
      ((quotientStackSourceComparison G (quotientStackModuleOfGroupoid G M)).val.app (op V)
        (((Space.modulePullback C S hS G.source).map (quotientStackModuleOfGroupoidHom G M)).val.app
          (op V) z)) := rfl

/-- **The source half of the compatibility with the transitions**: over an affine chart `V` of
`R` carrying an affine square over `s`, `c_s ∘ s^*ψ` read in `Γ(V, (s ∘ v)^*𝒢)` is the chart
section along the point `v` of `V`. -/
theorem pointEval_sourceComparison (V : Space.SmallEtale C S hS G.arrows.obj)
    (hV : IsAffine ((Space.SmallEtale.toOver C S hS G.arrows.obj ⋙
      BigFppfOver.toScheme C S hS).obj V)) (A : Space.AffineEtale C S hS G.objects.obj)
    (g : (Space.SmallEtale.toOver C S hS G.arrows.obj).obj V ⟶
      (Space.SmallEtale.toOver C S hS G.objects.obj).obj A.obj)
    (hg : V.1.hom ≫ G.source.hom = yoneda.map g ≫ A.obj.1.hom)
    (z : ((Space.modulePullback C S hS G.source).obj M.F.obj).val.obj (op V)) :
    sourceComparisonEval G M V hV z = arrowChartRestrict G M V z := by
  let := Space.chartDiagramAlgebra C S hS G.source ⟨V, A.obj, g, hg⟩
  have hb := Space.bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite C S hS
    G.source M.F.obj M.F.property ⟨V, A.obj, g, hg⟩ hV A.property
  refine Stacks.eq_of_baseChange_surjective
    (Space.modulePullbackChartBaseChange C S hS G.source M.F.obj ⟨V, A.obj, g, hg⟩) hb.2
    (sourceComparisonEval G M V hV) (arrowChartRestrictHom G M V)
    (fun a q => arrowSelfScalar G V a • q) (fun a p => ?_) (fun a p => ?_) (fun m => ?_) z
  · rw [sourceComparisonEval_apply, (((Space.modulePullback C S hS G.source).map
      (quotientStackModuleOfGroupoidHom G M)).val.app (op V)).hom.map_smul a p,
      ((quotientStackSourceComparison G (quotientStackModuleOfGroupoid G M)).val.app
        (op V)).hom.map_smul]
    exact pointEval_arrow_smul G M V hV a _
  · exact arrowChartRestrict_smul G M V a p
  · have key : Space.modulePullbackChartBaseChange C S hS G.source M.F.obj ⟨V, A.obj, g, hg⟩
        ((1 : Space.chartRing C S hS G.arrows.obj G.arrows.property V) ⊗ₜ m) =
        Space.modulePullbackChartSection C S hS G.source M.F.obj ⟨V, A.obj, g, hg⟩ m :=
      (Space.modulePullbackChartBaseChange_tmul C S hS G.source M.F.obj _ 1 m).trans (one_smul _ _)
    rw [key, sourceComparisonEval_apply]
    have e := Space.modulePullbackChartSection_map C S hS G.source _
      (quotientStackModuleOfGroupoidHom G M) ⟨V, A.obj, g, hg⟩ m
    refine (congrArg (fun w => pointEval G M (affineArrowChartPoint G V hV)
      ((quotientStackSourceComparison G (quotientStackModuleOfGroupoid G M)).val.app (op V) w))
        e).trans ?_
    exact pointEval_sourceComparison_chartSection G M V hV A g hg m

end AlgebraicGeometry.Stack

end
