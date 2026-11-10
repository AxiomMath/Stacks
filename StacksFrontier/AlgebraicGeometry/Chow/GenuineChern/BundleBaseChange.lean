module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange

/-!
# Base change of the projective bundle, with its charts

For `g : X' ⟶ X`, a quasi-coherent `E` on `X` and a quasi-coherent `E'` on `X'` identified with
`g^*E`, the projective bundle `𝐏(E') = Proj_{X'}(Sym E')` of
`Stacks.SymGraded.schemeProjectiveBundle` is the base change `X' ×_X 𝐏(E)` ([Stacks, Tag 01O3]).
The library proves this for the other presentation of the projective bundle,
`Stacks.RelativeProj.projectiveBundle`, and compares the two presentations only up to an
existential isomorphism. This file names both comparisons, so that the base-change morphism
`𝐏(E') ⟶ 𝐏(E)` comes with a formula on charts: over affine opens `W' ⊆ g⁻¹W` it is `Proj` of an
explicit homomorphism of graded rings of sections `Γ(W, Sym E) ⟶ Γ(W', Sym E')`.

## Main definitions

* `Stacks.ProjectiveBundle.presentationIso`: the comparison of the two presentations of `𝐏(E)`.
* `Stacks.ProjectiveBundle.baseChangeGradedHom`: the graded ring map
  `Γ(W, Sym E) ⟶ Γ(W', Sym E')` for `W' ⊆ g⁻¹W`.
* `Stacks.ProjectiveBundle.baseChangeHom`: the base-change morphism `𝐏(E') ⟶ 𝐏(E)`.
* `Stacks.ProjectiveBundle.baseChangeIso`: `𝐏(E') ≅ X' ×_X 𝐏(E)`.

## Main results

* `Stacks.ProjectiveBundle.chart_presentationIso_hom`: the presentation comparison on charts.
* `Stacks.ProjectiveBundle.chart_baseChangeHom`: the base-change morphism on charts.
* `Stacks.ProjectiveBundle.isPullback_baseChangeHom`: the base-change square is cartesian.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.SymGraded Stacks.AlgebraicGeometry.ProjPresentation
open Stacks.AlgebraicGeometry.RelativeProjGlue (relativeProj relativeProjToBase chart)

universe u

namespace Stacks.ProjectiveBundle

section Presentation

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] (hqc : IsQuasicoherentPieces E)

/-- The inverse comparison of the graded rings of sections, from the situation model to the
graded-algebra model. -/
def presentationInv (U : X.AffineZariskiSite) :
    (symSituation E).sectionRingGrading (siteAffineOpen U).1 →+*ᵍ
      (situationSheafGradedAlgebra E hqc).toGradedAlgebra.grading U :=
  gradedRingHomInverse (situationGradedHom E hqc U.toOpens)
    (situationSectionRingHomInv E hqc U.toOpens)
    (situationSectionRingHomInv_hom E hqc U.toOpens)
    (situationSectionRingHom_inv E hqc U.toOpens)
    (situationSectionRingHomInv_mem E hqc U.toOpens)

/-- The structure map in degree zero of the graded-algebra model, followed by the degree-zero
ring map of the comparison of graded rings of sections, is the base map of the chart data of the
situation model. -/
theorem presentation_hbase (U : X.AffineZariskiSite) :
    (situationSheafGradedAlgebra E hqc).toGradedAlgebra.strZero U ≫
        CommRingCat.ofHom (situationGradedHom E hqc U.toOpens).gradedZeroRingHom =
      (Stacks.RelativeProj.Situation.chartData (symSituation E)).base (siteAffineOpen U) := by
  refine CommRingCat.hom_ext (RingHom.ext fun r => Subtype.ext ?_)
  exact (congrArg (situationSectionRingHom E hqc U.toOpens)
      (((situationSheafGradedAlgebra E hqc).toGradedAlgebra).coe_strZero_apply U r)).trans
    ((situationSectionRingHom_strHom E hqc U.toOpens r).trans
      (Stacks.AlgebraicGeometry.RelativeProj.projZeroRingHom'_coe_of_mem _
        (Stacks.RelativeProj.Situation.sectionRingBaseMap_mem_zero
          (symSituation E) U.toOpens r)).symm)

/-- The chart family on the situation model of `𝐏(E)` that compares it with the graded-algebra
model. -/
def presentationChartFamily :=
  chartFamily (Stacks.RelativeProj.Situation.chartData (symSituation E))
    (situationSheafGradedAlgebra E hqc).toGradedAlgebra
    (fun U => situationGradedHom E hqc U.toOpens) (presentationInv E hqc)
    (fun U => GradedRingHom.ext fun x => situationSectionRingHomInv_hom E hqc U.toOpens x)
    (fun U => GradedRingHom.ext fun y => situationSectionRingHom_inv E hqc U.toOpens y)
    (fun U V h => situationGradedHom_res E hqc U.toOpens V.toOpens h)
    (presentation_hbase E hqc)

/-- **The two presentations of the projective bundle**, `Stacks.SymGraded.schemeProjectiveBundle`
and `Stacks.RelativeProj.projectiveBundle`, compared by a named isomorphism. -/
def presentationIso :
    relativeProj (situationSheafGradedAlgebra E hqc).toGradedAlgebra ≅
      Stacks.RelativeProj.projectiveBundle X E :=
  (presentationChartFamily E hqc).iso

/-- The comparison of presentations lies over the base. -/
@[reassoc (attr := simp)]
theorem presentationIso_hom_toBase :
    (presentationIso E hqc).hom ≫ Stacks.RelativeProj.projectiveBundleToBase X E =
      relativeProjToBase (situationSheafGradedAlgebra E hqc).toGradedAlgebra :=
  (presentationChartFamily E hqc).iso_hom_comp

/-- The inverse comparison of graded rings of sections over an affine open, after the comparison,
is the identity on the grading of the graded-algebra model. -/
theorem presentation_hnm (U : X.AffineZariskiSite) :
    (presentationInv E hqc U).comp (situationGradedHom E hqc U.toOpens) =
      GradedRingHom.id ((situationSheafGradedAlgebra E hqc).toGradedAlgebra.grading U) :=
  GradedRingHom.ext fun x => situationSectionRingHomInv_hom E hqc U.toOpens x

/-- The comparison of graded rings of sections over an affine open, after its inverse, is the
identity on the section-ring grading of the situation model. -/
theorem presentation_hmn (U : X.AffineZariskiSite) :
    (situationGradedHom E hqc U.toOpens).comp (presentationInv E hqc U) =
      GradedRingHom.id ((symSituation E).sectionRingGrading (siteAffineOpen U).1) :=
  GradedRingHom.ext fun y => situationSectionRingHom_inv E hqc U.toOpens y

/-- **The comparison of presentations on charts**: the chart of the graded-algebra model over an
affine open, followed by the comparison, is `Proj` of the inverse comparison of graded rings of
sections followed by the chart of the situation model. -/
@[reassoc]
theorem chart_presentationIso_hom (U : X.AffineZariskiSite) :
    chart (situationSheafGradedAlgebra E hqc).toGradedAlgebra U ≫ (presentationIso E hqc).hom =
      AlgebraicGeometry.Proj.map (presentationInv E hqc U)
          (Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id _ _ (presentation_hnm E hqc U)) ≫
        Stacks.RelativeProj.Situation.relativeProjChart (symSituation E) (siteAffineOpen U) :=
  (presentationChartFamily E hqc).chart_iso_hom U

/-- The chart of the situation model through the inverse comparison of presentations. -/
@[reassoc]
theorem relativeProjChart_presentationIso_inv (U : X.AffineZariskiSite) :
    Stacks.RelativeProj.Situation.relativeProjChart (symSituation E) (siteAffineOpen U) ≫
        (presentationIso E hqc).inv =
      AlgebraicGeometry.Proj.map (situationGradedHom E hqc U.toOpens)
          (Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id _ _ (presentation_hmn E hqc U)) ≫
        chart (situationSheafGradedAlgebra E hqc).toGradedAlgebra U := by
  have e1 : AlgebraicGeometry.Proj.map (situationGradedHom E hqc U.toOpens)
        (Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id _ _ (presentation_hmn E hqc U)) ≫
      AlgebraicGeometry.Proj.map (presentationInv E hqc U)
        (Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id _ _ (presentation_hnm E hqc U)) =
      𝟙 _ :=
    (AlgebraicGeometry.Proj.map_comp (presentationInv E hqc U)
      (situationGradedHom E hqc U.toOpens) _ _).symm.trans
      ((AlgebraicGeometry.Proj.map_congr (presentation_hmn E hqc U) _ (by simp)).trans
        AlgebraicGeometry.Proj.map_id)
  refine (Iso.comp_inv_eq _).2 ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (fun k => AlgebraicGeometry.Proj.map
    (situationGradedHom E hqc U.toOpens)
    (Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id _ _ (presentation_hmn E hqc U)) ≫ k)
    (chart_presentationIso_hom E hqc U)).symm
  refine Eq.trans ?_ (Category.assoc _ _ _)
  exact (congrArg (fun k => k ≫ Stacks.RelativeProj.Situation.relativeProjChart (symSituation E)
    (siteAffineOpen U)) e1 |>.trans (Category.id_comp _)).symm

end Presentation

section BaseChange

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (E : X.Modules) [E.IsQuasicoherent]
  (hqc : IsQuasicoherentPieces E) (E' : X'.Modules) [E'.IsQuasicoherent]
  (hqc' : IsQuasicoherentPieces E') (hE : E' ≅ (Scheme.Modules.pullback g).obj E)

/-- **The base-change morphism of projective bundles** `𝐏(E') ⟶ 𝐏(E)`, for `E' ≅ g^*E`: the
base-change morphism of the situation model, read through the two comparisons of
presentations. -/
def baseChangeHom :
    relativeProj (situationSheafGradedAlgebra E' hqc').toGradedAlgebra ⟶
      relativeProj (situationSheafGradedAlgebra E hqc).toGradedAlgebra :=
  (presentationIso E' hqc').hom ≫ Stacks.RelativeProj.projectiveBundleBaseChange g E E' hE ≫
    (presentationIso E hqc).inv

/-- The base-change morphism lies over `g`. -/
@[reassoc]
theorem baseChangeHom_toBase :
    baseChangeHom g E hqc E' hqc' hE ≫
        relativeProjToBase (situationSheafGradedAlgebra E hqc).toGradedAlgebra =
      relativeProjToBase (situationSheafGradedAlgebra E' hqc').toGradedAlgebra ≫ g := by
  rw [baseChangeHom, ← presentationIso_hom_toBase E hqc, ← presentationIso_hom_toBase E' hqc',
    Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
    Stacks.RelativeProj.projectiveBundleBaseChange_comp_projectiveBundleToBase, Category.assoc]

/-- **The base-change square of projective bundles is cartesian**: `𝐏(E')` is `X' ×_X 𝐏(E)`
([Stacks, Tag 01O3]). -/
theorem isPullback_baseChangeHom :
    IsPullback (relativeProjToBase (situationSheafGradedAlgebra E' hqc').toGradedAlgebra)
      (baseChangeHom g E hqc E' hqc' hE) g
      (relativeProjToBase (situationSheafGradedAlgebra E hqc).toGradedAlgebra) := by
  refine (Stacks.RelativeProj.isPullback_projectiveBundleToBase_baseChange g E E' hE).of_iso
    (presentationIso E' hqc').symm (Iso.refl _) (presentationIso E hqc).symm (Iso.refl _)
    ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, ← presentationIso_hom_toBase E' hqc',
      Iso.inv_hom_id_assoc]
  · rw [Iso.symm_hom, Iso.symm_hom, baseChangeHom, Iso.inv_hom_id_assoc]
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, ← presentationIso_hom_toBase E hqc,
      Iso.inv_hom_id_assoc]

/-- **The base-change isomorphism** `𝐏(E') ≅ X' ×_X 𝐏(E)`. -/
def baseChangeIso :
    relativeProj (situationSheafGradedAlgebra E' hqc').toGradedAlgebra ≅
      pullback g (relativeProjToBase (situationSheafGradedAlgebra E hqc).toGradedAlgebra) :=
  (isPullback_baseChangeHom g E hqc E' hqc' hE).isoPullback

/-- The base-change isomorphism `𝐏(E') ≅ X' ×_X 𝐏(E)` followed by the first projection is the
structure morphism of `𝐏(E')` over `X'`. -/
@[reassoc (attr := simp)]
theorem baseChangeIso_hom_fst :
    (baseChangeIso g E hqc E' hqc' hE).hom ≫
        pullback.fst g (relativeProjToBase (situationSheafGradedAlgebra E hqc).toGradedAlgebra) =
      relativeProjToBase (situationSheafGradedAlgebra E' hqc').toGradedAlgebra :=
  (isPullback_baseChangeHom g E hqc E' hqc' hE).isoPullback_hom_fst

/-- The base-change isomorphism `𝐏(E') ≅ X' ×_X 𝐏(E)` followed by the second projection is the
base-change morphism `𝐏(E') ⟶ 𝐏(E)`. -/
@[reassoc (attr := simp)]
theorem baseChangeIso_hom_snd :
    (baseChangeIso g E hqc E' hqc' hE).hom ≫
        pullback.snd g (relativeProjToBase (situationSheafGradedAlgebra E hqc).toGradedAlgebra) =
      baseChangeHom g E hqc E' hqc' hE :=
  (isPullback_baseChangeHom g E hqc E' hqc' hE).isoPullback_hom_snd

/-- **The graded ring map of sections** `Γ(W, Sym E) ⟶ Γ(W', Sym E')` for affine opens
`W' ⊆ g⁻¹W`: a section is pulled back along `g` and carried into `Sym E'` by `hE`. -/
def baseChangeGradedHom (W : X.AffineZariskiSite) (W' : X'.AffineZariskiSite)
    (h : W'.toOpens ≤ g ⁻¹ᵁ W.toOpens) :
    (situationSheafGradedAlgebra E hqc).toGradedAlgebra.grading W →+*ᵍ
      (situationSheafGradedAlgebra E' hqc').toGradedAlgebra.grading W' :=
  (presentationInv E' hqc' W').comp
    ((Stacks.RelativeProj.Situation.gradedBaseChange (s := symSituation E) (s' := symSituation E')
      g (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE) W.toOpens W'.toOpens h).comp
      (situationGradedHom E hqc W.toOpens))

/-- The irrelevant ideal of `Γ(W', Sym E')` is contained in the image of the irrelevant ideal of
`Γ(W, Sym E)` under the graded ring map of sections, for affine opens `W' ⊆ g⁻¹W`. -/
theorem irrelevant_le_baseChangeGradedHom (W : X.AffineZariskiSite) (W' : X'.AffineZariskiSite)
    (h : W'.toOpens ≤ g ⁻¹ᵁ W.toOpens) :
    HomogeneousIdeal.irrelevant
        ((situationSheafGradedAlgebra E' hqc').toGradedAlgebra.grading W') ≤
      (HomogeneousIdeal.irrelevant
        ((situationSheafGradedAlgebra E hqc).toGradedAlgebra.grading W)).map
          (baseChangeGradedHom g E hqc E' hqc' hE W W' h) :=
  HomogeneousIdeal.irrelevant_le_map_comp
    (HomogeneousIdeal.irrelevant_le_map_comp
      (Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id _ _ (presentation_hmn E hqc W))
      (Stacks.RelativeProj.Situation.irrelevant_le_gradedBaseChange (s := symSituation E)
        (s' := symSituation E') g (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE)
        (siteAffineOpen W) (siteAffineOpen W') h
        (fun m => Stacks.RelativeProj.isIso_symmetricSituationPullbackHom_app g E E' hE (m : ℤ))))
    (Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id _ _ (presentation_hnm E' hqc' W'))

/-- **The graded ring map of sections on a homogeneous element**: a section `a` of `Sym^n E`
over `W` goes to the pullback of `a` along `g`, restricted to `W'` and carried into `Sym^n E'`
by the identification `g^*Sym E ≅ Sym E'` induced by `hE`. -/
theorem baseChangeGradedHom_of (W : X.AffineZariskiSite) (W' : X'.AffineZariskiSite)
    (h : W'.toOpens ≤ g ⁻¹ᵁ W.toOpens) (n : ℕ)
    (a : (situationSheafGradedAlgebra E hqc).sectionPieces W.toOpens n) :
    baseChangeGradedHom g E hqc E' hqc' hE W W' h
        (DirectSum.of ((situationSheafGradedAlgebra E hqc).sectionPieces W.toOpens) n a) =
      DirectSum.of ((situationSheafGradedAlgebra E' hqc').sectionPieces W'.toOpens) n
        (((Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).app (n : ℤ)).val.app
          (Opposite.op W'.toOpens)
          (Scheme.Modules.pullbackSection g ((symSituation E).algebra.piece (n : ℤ)) W.toOpens
            W'.toOpens h a)) := by
  change situationSectionRingHomInv E' hqc' W'.toOpens
      (Stacks.RelativeProj.Situation.sectionRingBaseChange (s := symSituation E)
        (s' := symSituation E') g (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE)
        W.toOpens W'.toOpens h (situationSectionRingHom E hqc W.toOpens
          (DirectSum.of ((situationSheafGradedAlgebra E hqc).sectionPieces W.toOpens) n a))) = _
  rw [situationSectionRingHom_of]
  exact (congrArg (situationSectionRingHomInv E' hqc' W'.toOpens)
    (Stacks.RelativeProj.Situation.sectionRingBaseChange_of (s := symSituation E)
      (s' := symSituation E') g (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE)
      W.toOpens W'.toOpens h n a)).trans (situationSectionRingHomInv_of E' hqc' W'.toOpens _)

/-- **The base-change morphism on charts**: over affine opens `W' ⊆ g⁻¹W` it is `Proj` of the
graded ring map of sections followed by the chart over `W`. -/
theorem chart_baseChangeHom (W : X.AffineZariskiSite) (W' : X'.AffineZariskiSite)
    (h : W'.toOpens ≤ g ⁻¹ᵁ W.toOpens) :
    chart (situationSheafGradedAlgebra E' hqc').toGradedAlgebra W' ≫
        baseChangeHom g E hqc E' hqc' hE =
      AlgebraicGeometry.Proj.map (baseChangeGradedHom g E hqc E' hqc' hE W W' h)
          (irrelevant_le_baseChangeGradedHom g E hqc E' hqc' hE W W' h) ≫
        chart (situationSheafGradedAlgebra E hqc).toGradedAlgebra W := by
  have h2 : Stacks.RelativeProj.Situation.relativeProjChart (symSituation E')
        (siteAffineOpen W') ≫ Stacks.RelativeProj.projectiveBundleBaseChange g E E' hE =
      AlgebraicGeometry.Proj.map
          (Stacks.RelativeProj.Situation.gradedBaseChange (s := symSituation E)
            (s' := symSituation E') g (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE)
            W.toOpens W'.toOpens h)
          (Stacks.RelativeProj.Situation.irrelevant_le_gradedBaseChange (s := symSituation E)
            (s' := symSituation E') g (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE)
            (siteAffineOpen W) (siteAffineOpen W') h
            (fun m => Stacks.RelativeProj.isIso_symmetricSituationPullbackHom_app g E E' hE
              (m : ℤ))) ≫
        Stacks.RelativeProj.Situation.relativeProjChart (symSituation E) (siteAffineOpen W) :=
    Stacks.RelativeProj.Situation.relativeProjChart_comp_relativeProjBaseChange
      (s := symSituation E) (s' := symSituation E')
      g (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE)
      (fun m => Stacks.RelativeProj.isIso_symmetricSituationPullbackHom_app g E E' hE (m : ℤ))
      ⟨(siteAffineOpen W', siteAffineOpen W), h⟩
  have e1 := congrArg (fun k => k ≫ Stacks.RelativeProj.projectiveBundleBaseChange g E E' hE ≫
    (presentationIso E hqc).inv) (chart_presentationIso_hom E' hqc' W')
  have e2 := congrArg (fun k => k ≫ (presentationIso E hqc).inv) h2
  have e3 := relativeProjChart_presentationIso_inv E hqc W
  have e4 := AlgebraicGeometry.Proj.map_comp
    ((Stacks.RelativeProj.Situation.gradedBaseChange (s := symSituation E)
      (s' := symSituation E') g (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE)
      W.toOpens W'.toOpens h).comp (situationGradedHom E hqc W.toOpens))
    (presentationInv E' hqc' W') (HomogeneousIdeal.irrelevant_le_map_comp
      (Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id _ _ (presentation_hmn E hqc W))
      (Stacks.RelativeProj.Situation.irrelevant_le_gradedBaseChange (s := symSituation E)
        (s' := symSituation E') g (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE)
        (siteAffineOpen W) (siteAffineOpen W') h
        (fun m => Stacks.RelativeProj.isIso_symmetricSituationPullbackHom_app g E E' hE (m : ℤ))))
    (Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id _ _ (presentation_hnm E' hqc' W'))
  have e5 := AlgebraicGeometry.Proj.map_comp (situationGradedHom E hqc W.toOpens)
    (Stacks.RelativeProj.Situation.gradedBaseChange (s := symSituation E)
      (s' := symSituation E') g (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE)
      W.toOpens W'.toOpens h)
    (Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id _ _ (presentation_hmn E hqc W))
    (Stacks.RelativeProj.Situation.irrelevant_le_gradedBaseChange (s := symSituation E)
        (s' := symSituation E') g (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE)
        (siteAffineOpen W) (siteAffineOpen W') h
        (fun m => Stacks.RelativeProj.isIso_symmetricSituationPullbackHom_app g E E' hE (m : ℤ)))
  simp only [Category.assoc] at e1 e2 e3
  refine e1.trans ?_
  refine (congrArg (fun k => AlgebraicGeometry.Proj.map (presentationInv E' hqc' W') _ ≫ k)
    e2).trans ?_
  refine (congrArg (fun k => AlgebraicGeometry.Proj.map (presentationInv E' hqc' W') _ ≫
    AlgebraicGeometry.Proj.map (Stacks.RelativeProj.Situation.gradedBaseChange
      (s := symSituation E) (s' := symSituation E') g
      (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE) W.toOpens W'.toOpens h) _ ≫ k)
    e3).trans ?_
  refine Eq.trans ?_ (congrArg (fun k =>
      k ≫ chart (situationSheafGradedAlgebra E hqc).toGradedAlgebra W)
    (e4.trans (congrArg (fun k => AlgebraicGeometry.Proj.map (presentationInv E' hqc' W') _ ≫ k)
      e5))).symm
  exact ((Category.assoc _ _ _).trans (congrArg (fun k => _ ≫ k) (Category.assoc _ _ _))).symm

omit [E.IsQuasicoherent] [E'.IsQuasicoherent] in
/-- **Every point of `X'` lies in an affine open mapping into an affine open of `X`**, the
charts on which the base-change morphism has its formula. -/
theorem exists_affineZariskiSite_le_preimage (x' : X') :
    ∃ (W : X.AffineZariskiSite) (W' : X'.AffineZariskiSite) (_ : W'.toOpens ≤ g ⁻¹ᵁ W.toOpens),
      x' ∈ W'.toOpens := by
  obtain ⟨W, hW, hgx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show g.base x' ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨W', hW', hxW', hle'⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    X'.isBasis_affineOpens (show x' ∈ g ⁻¹ᵁ W from hgx)
  exact ⟨⟨W, hW⟩, ⟨W', hW'⟩, hle', hxW'⟩

end BaseChange

end Stacks.ProjectiveBundle

end
