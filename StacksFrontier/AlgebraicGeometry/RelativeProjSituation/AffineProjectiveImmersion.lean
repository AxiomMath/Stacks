module

public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.AffineProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.ChartTwistOne
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.ChartTwistPoly
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjTwistTransition

/-!
# A relative `Proj` over an affine base is a closed subscheme of `ℙⁿ` over that base

Let `s` be a relative `Proj` situation over an affine base `S`, with the graded algebra generated
in degree one over `⊤`, the degree-zero identification at `⊤` surjective, and the degree-one
global sections spanned by a finite family `g`. This file assembles, from the presentation of
`StacksFrontier/AlgebraicGeometry/RelativeProjSituation/AffineProjectiveSpace.lean` and the two
halves of [Stacks, Tag 01OE] over an affine base, a closed immersion

`Proj_S(s) ⟶ ℙ^{g.card}_S` over `S`,

carrying the hyperplane sheaf of `ℙ^{g.card}_S` back to the degree-one twisting sheaf of
`Proj_S(s)`.

The route is three morphisms: the chart of `Proj_S(s)` over `⊤`, which is an isomorphism; the
presentation `Proj Γ(S, ⊤, s) ⟶ Proj Γ(S, ⊤)[T₀, …, T_d]`, a closed immersion; and an
isomorphism `Proj Γ(S, ⊤)[T₀, …, T_d] ≅ ℙ^d_S`, which is the chart comparison
`Stacks.SymGraded.chartIsoProjPoly`, the chart of the projective bundle of `𝒪_S^{d+1}` over `⊤`,
and Tag 01OE's identification of that bundle with `ℙ^d_S`.

## Main definitions

* `Stacks.RelativeProj.Situation.topBundleIso`: the isomorphism
  `Proj Γ(S, ⊤)[T₀, …, T_d] ≅ ℙ^d_S`.
* `Stacks.RelativeProj.Situation.topImmersion`: the morphism `Proj_S(s) ⟶ ℙ^{g.card}_S`.

## Main results

* `Stacks.RelativeProj.Situation.isImmersion_topImmersion`: **it is an immersion**, the
  composite of an isomorphism, a closed immersion
  (`Stacks.RelativeProj.Situation.isClosedImmersion_topProjHom`) and an isomorphism.
* `Stacks.RelativeProj.Situation.topImmersion_comp_fst`: **it lies over `S`.**
* `Stacks.RelativeProj.Situation.nonempty_twistSheaf_iso_pullback_topImmersion`: **the hyperplane
  sheaf pulls back to the degree-one twisting sheaf of the relative `Proj`.**

## Implementation notes

The over-the-base clause is where the degree-zero bookkeeping is spent:
`Stacks.SymGraded.chartIsoProjPoly_hom_comp_projToSpecCoeff` carries the degree-zero
half of the chart comparison, `Stacks.RelativeProj.Situation.topProjHom_comp_projToSpecCoeff` that
of the presentation, and the structure morphisms of the two charts are the cartesian squares of
[Stacks, Tag 01NQ].

The three factors are collapsed to an isomorphism, a closed immersion and an isomorphism before
any instance is asked for: instance synthesis does not reach through a five-fold composite at the
project's `maxSynthPendingDepth`.

Only degree one of the twist is transported, because that is the degree in which
[Stacks, Tag 01OE]'s module half is available.

## References

* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite DirectSum
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

attribute [local instance] MvPolynomial.gradedAlgebra SetLike.GradeZero.instCommRing

namespace Stacks.RelativeProj.Situation

variable (s : Situation.{u}) [IsAffine s.base] (g : Finset (s.sectionPieces ⊤ 1))

/-! ### The projective space over an affine base as an absolute `Proj` -/

omit [IsAffine s.base] in
/-- The chart of the projective bundle of `𝒪_S^{d+1}` over `⊤` is an isomorphism when `S` is
affine. -/
theorem isIso_freeBundleChart_top (hS : IsAffineOpen (⊤ : s.base.Opens)) (d : ℕ) :
    IsIso ((Stacks.SymGraded.freeProjectiveBundle (X := s.base) d).chart ⊤ hS) :=
  Stacks.AlgebraicGeometry.RelativeProjAffineBase.isIso_chart_top
    (Stacks.SymGraded.freeSymGradedAlgebra (X := s.base)
      (Stacks.SymGraded.coordIndex.{u} d)).toGradedAlgebra hS

/-- **`ℙ^d_S` is the absolute `Proj` of `Γ(S, ⊤)[T₀, …, T_d]` when `S` is affine**: the chart
comparison of the projective bundle of `𝒪_S^{d+1}`, the chart of that bundle over `⊤`, and
[Stacks, Tag 01OE]. -/
def topBundleIso (hS : IsAffineOpen (⊤ : s.base.Opens)) (d : ℕ) :
    AlgebraicGeometry.Proj
        (polyGrading ↥(Stacks.SymGraded.siteRing s.base (op (⊤ : s.base.Opens))) d) ≅
      AlgebraicGeometry.projectiveSpaceOver.{u} d s.base :=
  haveI := isIso_freeBundleChart_top s hS d
  (Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).symm ≪≫
    asIso ((Stacks.SymGraded.freeProjectiveBundle (X := s.base) d).chart ⊤ hS) ≪≫
      Stacks.SymGraded.projectiveBundleIsoProjectiveSpace (X := s.base) d

omit [IsAffine s.base] in
/-- The forward morphism of `Stacks.RelativeProj.Situation.topBundleIso`, unfolded. -/
theorem topBundleIso_hom (hS : IsAffineOpen (⊤ : s.base.Opens)) (d : ℕ) :
    (topBundleIso s hS d).hom =
      (Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).inv ≫
        (Stacks.SymGraded.freeProjectiveBundle (X := s.base) d).chart ⊤ hS ≫
          (Stacks.SymGraded.projectiveBundleIsoProjectiveSpace (X := s.base) d).hom :=
  rfl

omit [IsAffine s.base] in
/-- The isomorphism of `Stacks.RelativeProj.Situation.topBundleIso` lies over `S`, the structure
morphism of the absolute `Proj` being the one of
`Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff`. -/
theorem topBundleIso_hom_comp_fst (hS : IsAffineOpen (⊤ : s.base.Opens)) (d : ℕ) :
    (topBundleIso s hS d).hom ≫ pullback.fst (terminal.from s.base) (terminal.from
        (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} d)) = projToSpecCoeff
        ↥(Stacks.SymGraded.siteRing s.base (op (⊤ : s.base.Opens))) d ≫ hS.isoSpec.inv ≫ (⊤ :
        s.base.Opens).ι := by
  have := isIso_freeBundleChart_top s hS d
  have hcomp := Stacks.SymGraded.chartIsoProjPoly_hom_comp_projToSpecCoeff d
    (⊤ : s.base.Opens) hS
  have a1 : ((Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).inv ≫
      Stacks.AlgebraicGeometry.RelativeProj.projInclusionToOpen
      (Stacks.SymGraded.freeSymGradedAlgebra (X := s.base) (Stacks.SymGraded.coordIndex.{u} d)) ⊤
      hS) ≫ hS.isoSpec.hom =
      (Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).inv ≫
          (Stacks.AlgebraicGeometry.RelativeProj.projInclusionToOpen
          (Stacks.SymGraded.freeSymGradedAlgebra (X := s.base) (Stacks.SymGraded.coordIndex.{u}
          d)) ⊤ hS ≫ hS.isoSpec.hom) := Category.assoc _ _ _
  have a2 : (Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).inv ≫
      (Stacks.AlgebraicGeometry.RelativeProj.projInclusionToOpen
      (Stacks.SymGraded.freeSymGradedAlgebra (X := s.base) (Stacks.SymGraded.coordIndex.{u} d)) ⊤
      hS ≫ hS.isoSpec.hom) =
      (Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).inv ≫
          ((Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).hom ≫ projToSpecCoeff
          ↥(Stacks.SymGraded.siteRing s.base (op (⊤ : s.base.Opens))) d) :=
    congrArg (fun m => (Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).inv ≫ m) hcomp.symm
  have a3 : (Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).inv ≫
      ((Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).hom ≫ projToSpecCoeff
      ↥(Stacks.SymGraded.siteRing s.base (op (⊤ : s.base.Opens))) d) = projToSpecCoeff
      ↥(Stacks.SymGraded.siteRing s.base (op (⊤ : s.base.Opens))) d := Iso.inv_hom_id_assoc _ _
  have a4 : projToSpecCoeff ↥(Stacks.SymGraded.siteRing s.base (op (⊤ : s.base.Opens))) d =
      (projToSpecCoeff ↥(Stacks.SymGraded.siteRing s.base (op (⊤ : s.base.Opens))) d ≫
      hS.isoSpec.inv) ≫ hS.isoSpec.hom :=
    ((Category.assoc _ _ _).trans
      ((congrArg (fun m => projToSpecCoeff ↥(Stacks.SymGraded.siteRing s.base (op (⊤ :
          s.base.Opens))) d ≫ m) (Iso.inv_hom_id hS.isoSpec)).trans
        (Category.comp_id _))).symm
  have h3 : (Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).inv ≫
      Stacks.AlgebraicGeometry.RelativeProj.projInclusionToOpen
      (Stacks.SymGraded.freeSymGradedAlgebra (X := s.base) (Stacks.SymGraded.coordIndex.{u} d)) ⊤
      hS = projToSpecCoeff ↥(Stacks.SymGraded.siteRing s.base (op (⊤ : s.base.Opens))) d ≫
      hS.isoSpec.inv :=
    (cancel_mono hS.isoSpec.hom).1 (a1.trans (a2.trans (a3.trans a4)))
  have b1 : (topBundleIso s hS d).hom ≫ pullback.fst (terminal.from s.base) (terminal.from
      (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} d)) =
      ((Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).inv ≫
          (Stacks.SymGraded.freeProjectiveBundle (X := s.base) d).chart ⊤ hS ≫
          (Stacks.SymGraded.projectiveBundleIsoProjectiveSpace (X := s.base) d).hom) ≫
          pullback.fst (terminal.from s.base) (terminal.from
          (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} d)) :=
    congrArg (fun m => m ≫ pullback.fst (terminal.from s.base) (terminal.from
        (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} d))) (topBundleIso_hom s hS d)
  have b2 : ((Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).inv ≫
      (Stacks.SymGraded.freeProjectiveBundle (X := s.base) d).chart ⊤ hS ≫
      (Stacks.SymGraded.projectiveBundleIsoProjectiveSpace (X := s.base) d).hom) ≫ pullback.fst
      (terminal.from s.base) (terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} d)) =
      (Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).inv ≫
          ((Stacks.SymGraded.freeProjectiveBundle (X := s.base) d).chart ⊤ hS ≫
          (Stacks.SymGraded.projectiveBundleIsoProjectiveSpace (X := s.base) d).hom) ≫
          pullback.fst (terminal.from s.base) (terminal.from
          (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} d)) := Category.assoc _ _ _
  have b3 : (Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).inv ≫
      ((Stacks.SymGraded.freeProjectiveBundle (X := s.base) d).chart ⊤ hS ≫
      (Stacks.SymGraded.projectiveBundleIsoProjectiveSpace (X := s.base) d).hom) ≫ pullback.fst
      (terminal.from s.base) (terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} d)) =
      (Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).inv ≫
          (Stacks.SymGraded.freeProjectiveBundle (X := s.base) d).chart ⊤ hS ≫
          (Stacks.SymGraded.projectiveBundleIsoProjectiveSpace (X := s.base) d).hom ≫ pullback.fst
          (terminal.from s.base) (terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u}
          d)) :=
    congrArg (fun m => (Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).inv ≫ m)
        (Category.assoc _ _ _)
  have b4 : (Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).inv ≫
      (Stacks.SymGraded.freeProjectiveBundle (X := s.base) d).chart ⊤ hS ≫
      (Stacks.SymGraded.projectiveBundleIsoProjectiveSpace (X := s.base) d).hom ≫ pullback.fst
      (terminal.from s.base) (terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} d)) =
      (Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).inv ≫
          (Stacks.SymGraded.freeProjectiveBundle (X := s.base) d).chart ⊤ hS ≫
          (Stacks.SymGraded.freeProjectiveBundle (X := s.base) d).toBase :=
    congrArg (fun m => (Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).inv ≫
        (Stacks.SymGraded.freeProjectiveBundle (X := s.base) d).chart ⊤ hS ≫ m)
      (Stacks.SymGraded.projectiveBundleIsoProjectiveSpace_hom_comp_fst d)
  have b5 : (Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).inv ≫
      (Stacks.SymGraded.freeProjectiveBundle (X := s.base) d).chart ⊤ hS ≫
      (Stacks.SymGraded.freeProjectiveBundle (X := s.base) d).toBase =
      (Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).inv ≫
          Stacks.AlgebraicGeometry.RelativeProj.projInclusionToOpen
          (Stacks.SymGraded.freeSymGradedAlgebra (X := s.base) (Stacks.SymGraded.coordIndex.{u}
          d)) ⊤ hS ≫ (⊤ : s.base.Opens).ι :=
    congrArg (fun m => (Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).inv ≫ m)
        ((Stacks.SymGraded.freeProjectiveBundle (X := s.base) d).chart_isPullback ⊤ hS).w
  have b6 : (Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).inv ≫
      Stacks.AlgebraicGeometry.RelativeProj.projInclusionToOpen
      (Stacks.SymGraded.freeSymGradedAlgebra (X := s.base) (Stacks.SymGraded.coordIndex.{u} d)) ⊤
      hS ≫ (⊤ : s.base.Opens).ι = ((Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).inv ≫
      Stacks.AlgebraicGeometry.RelativeProj.projInclusionToOpen
      (Stacks.SymGraded.freeSymGradedAlgebra (X := s.base) (Stacks.SymGraded.coordIndex.{u} d)) ⊤
      hS) ≫ (⊤ : s.base.Opens).ι :=
    (Category.assoc _ _ _).symm
  have b7 : ((Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).inv ≫
      Stacks.AlgebraicGeometry.RelativeProj.projInclusionToOpen
      (Stacks.SymGraded.freeSymGradedAlgebra (X := s.base) (Stacks.SymGraded.coordIndex.{u} d)) ⊤
      hS) ≫ (⊤ : s.base.Opens).ι = (projToSpecCoeff ↥(Stacks.SymGraded.siteRing s.base (op (⊤ :
      s.base.Opens))) d ≫ hS.isoSpec.inv) ≫ (⊤ : s.base.Opens).ι :=
    congrArg (fun m => m ≫ (⊤ : s.base.Opens).ι) h3
  have b8 : (projToSpecCoeff ↥(Stacks.SymGraded.siteRing s.base (op (⊤ : s.base.Opens))) d ≫
      hS.isoSpec.inv) ≫ (⊤ : s.base.Opens).ι = projToSpecCoeff ↥(Stacks.SymGraded.siteRing s.base
      (op (⊤ : s.base.Opens))) d ≫ hS.isoSpec.inv ≫ (⊤ : s.base.Opens).ι :=
    Category.assoc _ _ _
  exact b1.trans (b2.trans (b3.trans (b4.trans (b5.trans (b6.trans (b7.trans b8))))))

/-- The hyperplane sheaf of `ℙ^d_S` corresponds to the degree-one twisting sheaf of
`Proj Γ(S, ⊤)[T₀, …, T_d]` across `Stacks.RelativeProj.Situation.topBundleIso`. -/
theorem nonempty_pullback_topBundleIso_hom_twistingSheaf
    (hS : IsAffineOpen (⊤ : s.base.Opens)) (d : ℕ) :
    Nonempty ((Scheme.Modules.pullback (topBundleIso s hS d).hom).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf d s.base) ≅
      AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
        (polyGrading ↥(Stacks.SymGraded.siteRing s.base (op (⊤ : s.base.Opens))) d) 1) := by
  have := isIso_freeBundleChart_top s hS d
  obtain ⟨e₅⟩ := Stacks.SymGraded.nonempty_pullback_projectiveSpaceTwistingSheaf_iso_twistOne
    d (Stacks.SymGraded.hasFreeBundleTwistOne s.base d)
  have e₄ : (Scheme.Modules.pullback
        ((Stacks.SymGraded.freeProjectiveBundle (X := s.base) d).chart ⊤ hS)).obj
        (Stacks.Tag01VMVeryAmple.twistOne (Stacks.SymGraded.freeModule (X := s.base)
          (Stacks.SymGraded.coordIndex.{u} d))) ≅
      AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
        ((Stacks.SymGraded.freeSymGradedAlgebra (X := s.base)
          (Stacks.SymGraded.coordIndex.{u} d)).grading ⊤) 1 :=
    ((Scheme.Modules.restrictFunctorIsoPullback
        ((Stacks.SymGraded.freeProjectiveBundle (X := s.base) d).chart ⊤ hS)).app _).symm ≪≫
      Stacks.Tag01VMVeryAmple.twistOneChartIso (Stacks.SymGraded.freeModule (X := s.base)
        (Stacks.SymGraded.coordIndex.{u} d)) ⊤ hS
  obtain ⟨e₃⟩ := Stacks.SymGraded.nonempty_pullback_chartIsoProjPoly_inv_twistingSheaf
    (X := s.base) d ⊤ 1
  refine ⟨?_⟩
  rw [topBundleIso]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom]
  exact ((Scheme.Modules.pullbackComp
      (Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).inv _).app _).symm ≪≫
    (Scheme.Modules.pullback
        (Stacks.SymGraded.chartIsoProjPoly d (⊤ : s.base.Opens)).inv).mapIso
      (((Scheme.Modules.pullbackComp
          ((Stacks.SymGraded.freeProjectiveBundle (X := s.base) d).chart ⊤ hS) _).app _).symm ≪≫
        (Scheme.Modules.pullback
          ((Stacks.SymGraded.freeProjectiveBundle (X := s.base) d).chart ⊤ hS)).mapIso e₅ ≪≫
          e₄) ≪≫ e₃

/-! ### The closed immersion into projective space -/

variable (hgen : s.algebra.IsGeneratedInDegreeOne (op ⊤))
  (hg : Submodule.span (s.base.ringCatSheaf.obj.obj (op ⊤))
    (g : Set (s.sectionPieces ⊤ 1)) = ⊤)
  (hzero : Function.Surjective (sectionRingZeroMap s ⊤).hom)

/-- **The morphism `Proj_S(s) ⟶ ℙ^{g.card}_S`.** -/
def topImmersion :
    relativeProj s ⟶ AlgebraicGeometry.projectiveSpaceOver.{u} g.card s.base :=
  (relativeProjChartTopIso s (isAffineOpen_top s.base)).inv ≫
    topProjHom s g hgen hg hzero ≫
      (topBundleIso s (isAffineOpen_top s.base) g.card).hom

/-- Postcomposing an immersion with an isomorphism gives an immersion. Stated at arbitrary
schemes, where no transparency question arises. -/
private theorem isImmersion_comp_iso {X Y Z : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f]
    (e : Y ≅ Z) : IsImmersion (f ≫ e.hom) := by
  have : IsImmersion ((f ≫ e.hom) ≫ e.inv) := by
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    infer_instance
  exact IsImmersion.of_comp (f ≫ e.hom) e.inv

/-- **The morphism is an immersion**: the presentation is a closed immersion, the chart over `⊤`
an isomorphism, and `Stacks.RelativeProj.Situation.topBundleIso` an isomorphism. -/
theorem isImmersion_topImmersion : IsImmersion (topImmersion s g hgen hg hzero) := by
  have : IsClosedImmersion (topProjHom s g hgen hg hzero) :=
    isClosedImmersion_topProjHom s g hgen hg hzero
  have : IsImmersion ((relativeProjChartTopIso s (isAffineOpen_top s.base)).inv ≫
      topProjHom s g hgen hg hzero) := inferInstance
  have heq : topImmersion s g hgen hg hzero =
      ((relativeProjChartTopIso s (isAffineOpen_top s.base)).inv ≫
          topProjHom s g hgen hg hzero) ≫
        (topBundleIso s (isAffineOpen_top s.base) g.card).hom :=
    (Category.assoc _ _ _).symm
  rw [heq]
  exact isImmersion_comp_iso _ _

/-- **The morphism lies over `S`.** -/
theorem topImmersion_comp_fst :
    topImmersion s g hgen hg hzero ≫ pullback.fst (terminal.from s.base) (terminal.from
        (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} g.card)) = relativeProjToBase s := by
  have hS : IsAffineOpen (⊤ : s.base.Opens) := isAffineOpen_top s.base
  have hbase := relativeProjChartTopIso_hom_comp_toBase s hS
  have c1 : topImmersion s g hgen hg hzero ≫ pullback.fst (terminal.from s.base) (terminal.from
      (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} g.card)) =
      (relativeProjChartTopIso s hS).inv ≫ (topProjHom s g hgen hg hzero ≫ (topBundleIso s hS
          g.card).hom) ≫ pullback.fst (terminal.from s.base) (terminal.from
          (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} g.card)) := Category.assoc _ _ _
  have c2 : (relativeProjChartTopIso s hS).inv ≫ (topProjHom s g hgen hg hzero ≫ (topBundleIso s
      hS g.card).hom) ≫ pullback.fst (terminal.from s.base) (terminal.from
      (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} g.card)) =
      (relativeProjChartTopIso s hS).inv ≫ topProjHom s g hgen hg hzero ≫ (topBundleIso s hS
          g.card).hom ≫ pullback.fst (terminal.from s.base) (terminal.from
          (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} g.card)) :=
    congrArg (fun m => (relativeProjChartTopIso s hS).inv ≫ m) (Category.assoc _ _ _)
  have c3 : (relativeProjChartTopIso s hS).inv ≫ topProjHom s g hgen hg hzero ≫ (topBundleIso s hS
      g.card).hom ≫ pullback.fst (terminal.from s.base) (terminal.from
      (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} g.card)) =
      (relativeProjChartTopIso s hS).inv ≫ topProjHom s g hgen hg hzero ≫ projToSpecCoeff
          ↥(Stacks.SymGraded.siteRing s.base (op (⊤ : s.base.Opens))) g.card ≫ hS.isoSpec.inv ≫ (⊤
          : s.base.Opens).ι :=
    congrArg (fun m => (relativeProjChartTopIso s hS).inv ≫ topProjHom s g hgen hg hzero ≫ m)
        (topBundleIso_hom_comp_fst s hS g.card)
  have c4 : (relativeProjChartTopIso s hS).inv ≫ topProjHom s g hgen hg hzero ≫ projToSpecCoeff
      ↥(Stacks.SymGraded.siteRing s.base (op (⊤ : s.base.Opens))) g.card ≫ hS.isoSpec.inv ≫ (⊤ :
      s.base.Opens).ι =
      (relativeProjChartTopIso s hS).inv ≫ (topProjHom s g hgen hg hzero ≫ projToSpecCoeff
          ↥(Stacks.SymGraded.siteRing s.base (op (⊤ : s.base.Opens))) g.card) ≫ hS.isoSpec.inv ≫
          (⊤ : s.base.Opens).ι :=
    congrArg (fun m => (relativeProjChartTopIso s hS).inv ≫ m) (Category.assoc _ _ _).symm
  have c5 : (relativeProjChartTopIso s hS).inv ≫ (topProjHom s g hgen hg hzero ≫ projToSpecCoeff
      ↥(Stacks.SymGraded.siteRing s.base (op (⊤ : s.base.Opens))) g.card) ≫ hS.isoSpec.inv ≫ (⊤ :
      s.base.Opens).ι =
      (relativeProjChartTopIso s hS).inv ≫ (AlgebraicGeometry.Proj.toSpecZero
          (s.sectionRingGrading ⊤) ≫ Spec.map (sectionRingZeroMap s ⊤)) ≫ hS.isoSpec.inv ≫ (⊤ :
          s.base.Opens).ι :=
    congrArg (fun m => (relativeProjChartTopIso s hS).inv ≫ m ≫ hS.isoSpec.inv ≫ (⊤ :
        s.base.Opens).ι)
      (topProjHom_comp_projToSpecCoeff s g hgen hg hzero)
  have c6 : (relativeProjChartTopIso s hS).inv ≫ (AlgebraicGeometry.Proj.toSpecZero
      (s.sectionRingGrading ⊤) ≫ Spec.map (sectionRingZeroMap s ⊤)) ≫ hS.isoSpec.inv ≫ (⊤ :
      s.base.Opens).ι =
      (relativeProjChartTopIso s hS).inv ≫ AlgebraicGeometry.Proj.toSpecZero (s.sectionRingGrading
          ⊤) ≫ Spec.map (sectionRingZeroMap s ⊤) ≫ hS.isoSpec.inv ≫ (⊤ : s.base.Opens).ι :=
    congrArg (fun m => (relativeProjChartTopIso s hS).inv ≫ m) (Category.assoc _ _ _)
  have c7 : (relativeProjChartTopIso s hS).inv ≫ AlgebraicGeometry.Proj.toSpecZero
      (s.sectionRingGrading ⊤) ≫ Spec.map (sectionRingZeroMap s ⊤) ≫ hS.isoSpec.inv ≫ (⊤ :
      s.base.Opens).ι =
      (relativeProjChartTopIso s hS).inv ≫ (AlgebraicGeometry.Proj.toSpecZero
          (s.sectionRingGrading ⊤) ≫ Spec.map (sectionRingZeroMap s ⊤) ≫ hS.isoSpec.inv) ≫ (⊤ :
          s.base.Opens).ι :=
    congrArg (fun m => (relativeProjChartTopIso s hS).inv ≫ m) (Category.assoc _ _ _).symm
  have c8 : (relativeProjChartTopIso s hS).inv ≫ (AlgebraicGeometry.Proj.toSpecZero
      (s.sectionRingGrading ⊤) ≫ Spec.map (sectionRingZeroMap s ⊤) ≫ hS.isoSpec.inv) ≫ (⊤ :
      s.base.Opens).ι =
      (relativeProjChartTopIso s hS).inv ≫ (relativeProjChartTopIso s hS).hom ≫ relativeProjToBase
          s :=
    congrArg (fun m => (relativeProjChartTopIso s hS).inv ≫ m) hbase.symm
  have c9 : (relativeProjChartTopIso s hS).inv ≫ (relativeProjChartTopIso s hS).hom ≫
      relativeProjToBase s =
      relativeProjToBase s := Iso.inv_hom_id_assoc _ _
  exact c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans c9)))))))

/-- **The hyperplane sheaf of `ℙ^{g.card}_S` pulls back to the degree-one twisting sheaf of
`Proj_S(s)`.** -/
theorem nonempty_twistSheaf_iso_pullback_topImmersion :
    Nonempty (twistSheaf s 1 ≅ (Scheme.Modules.pullback (topImmersion s g hgen hg hzero)).obj
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf g.card s.base)) := by
  set hS := isAffineOpen_top s.base with hSdef
  obtain ⟨e₃⟩ := nonempty_pullback_topBundleIso_hom_twistingSheaf s hS g.card
  obtain ⟨e₂⟩ := nonempty_pullback_topProjHom_twistingSheaf s g hgen hg hzero 1
  have e₁hom : (Scheme.Modules.pullback (relativeProjChartTopIso s hS).hom).obj
        (twistSheaf s 1) ≅
      AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf (s.sectionRingGrading ⊤) 1 := by
    rw [relativeProjChartTopIso_hom]
    exact ((Scheme.Modules.restrictFunctorIsoPullback
        (relativeProjChart s ⟨⊤, hS⟩)).app (twistSheaf s 1)).symm ≪≫
      twistSheafChartIso s 1 ⟨⊤, hS⟩
  obtain ⟨e₁⟩ := Stacks.SymGraded.nonempty_pullback_inv_of_pullback_hom
    (relativeProjChartTopIso s hS) (twistSheaf s 1)
    (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf (s.sectionRingGrading ⊤) 1) ⟨e₁hom⟩
  have c3 : (Scheme.Modules.pullback (topProjHom s g hgen hg hzero ≫
        (topBundleIso s hS g.card).hom)).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf g.card s.base) ≅
      AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf (s.sectionRingGrading ⊤) 1 :=
    ((Scheme.Modules.pullbackComp (topProjHom s g hgen hg hzero)
        (topBundleIso s hS g.card).hom).app _).symm ≪≫
      (Scheme.Modules.pullback (topProjHom s g hgen hg hzero)).mapIso e₃ ≪≫ e₂
  have c2 : (Scheme.Modules.pullback ((relativeProjChartTopIso s hS).inv ≫
        topProjHom s g hgen hg hzero ≫ (topBundleIso s hS g.card).hom)).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf g.card s.base) ≅
      twistSheaf s 1 :=
    ((Scheme.Modules.pullbackComp (relativeProjChartTopIso s hS).inv
        (topProjHom s g hgen hg hzero ≫ (topBundleIso s hS g.card).hom)).app _).symm ≪≫
      (Scheme.Modules.pullback (relativeProjChartTopIso s hS).inv).mapIso c3 ≪≫ e₁
  refine ⟨?_⟩
  rw [topImmersion]
  exact c2.symm

end Stacks.RelativeProj.Situation

end
