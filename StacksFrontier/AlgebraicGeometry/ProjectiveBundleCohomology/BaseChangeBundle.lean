module

public import StacksFrontier.AlgebraicGeometry.ProjPresentationCompare.Basic
public import StacksFrontier.AlgebraicGeometry.ProjPresentationCompare.SymSectionRing
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.ProjectiveBundleBaseChange

/-!
# The projective bundle of a pullback is the base change of the projective bundle

Let `g : X' ⟶ X` be a morphism of schemes, `E` a quasi-coherent `𝒪_X`-module and `E'` a
quasi-coherent `𝒪_{X'}`-module identified with `g^*E`. The projective bundle
`𝐏(E') = Proj_{X'}(Sym E')` of this framework is the fibre product `X' ×_X 𝐏(E)`: there is a
morphism `𝐏(E') ⟶ 𝐏(E)` over `g` making the square of projections cartesian, and over a pair of
affine opens `W' ⊆ g⁻¹U` it is `Proj` of the base-change map
`Γ(U, Sym E) ⟶ Γ(W', Sym E') = Γ(W', 𝒪) ⊗ Γ(U, Sym E)` on the charts.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.presentationIso`: the projective bundle
  of `E` is the relative `Proj` of the situation of `E`, over the base.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.bundleChartRingHom`: the base-change
  map of graded rings of sections over a pair of affine opens.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.bundleBaseChange`: the morphism
  `𝐏(E') ⟶ 𝐏(E)`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.isPullback_bundleBaseChange`: the square
  of projections is cartesian.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.chart_comp_bundleBaseChange`: the
  description on charts.

## References

* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SymGraded

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

section Presentation

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] (hqc : IsQuasicoherentPieces E)

/-- The inverse of the identification of the graded rings of sections of the two presentations of
`Sym(E)` over an affine open. -/
public abbrev situationGradedInv (U : X.AffineZariskiSite) :=
  Stacks.AlgebraicGeometry.ProjPresentation.gradedRingHomInverse
    (situationGradedHom E hqc U.toOpens) (situationSectionRingHomInv E hqc U.toOpens)
    (situationSectionRingHomInv_hom E hqc U.toOpens) (situationSectionRingHom_inv E hqc U.toOpens)
    (situationSectionRingHomInv_mem E hqc U.toOpens)

/-- The charts of the relative `Proj` of the situation of `E`, read as a chart family of the
projective bundle of `E`. -/
public def situationChartFamily :
    Stacks.AlgebraicGeometry.RelativeProjDescent.ChartFamily
      (situationSheafGradedAlgebra E hqc).toGradedAlgebra
      (Stacks.RelativeProj.Situation.chartData (symSituation E)).relativeProj
      (Stacks.RelativeProj.Situation.chartData (symSituation E)).toBase :=
  Stacks.AlgebraicGeometry.ProjPresentation.chartFamily
    (Stacks.RelativeProj.Situation.chartData (symSituation E))
    (situationSheafGradedAlgebra E hqc).toGradedAlgebra
    (fun U => situationGradedHom E hqc U.toOpens) (situationGradedInv E hqc)
    (fun U => GradedRingHom.ext fun x => situationSectionRingHomInv_hom E hqc U.toOpens x)
    (fun U => GradedRingHom.ext fun y => situationSectionRingHom_inv E hqc U.toOpens y)
    (fun U V h => situationGradedHom_res E hqc U.toOpens V.toOpens h)
    (fun U => by
      refine CommRingCat.hom_ext (RingHom.ext fun r => Subtype.ext ?_)
      exact (congrArg (situationSectionRingHom E hqc U.toOpens)
          (((situationSheafGradedAlgebra E hqc).toGradedAlgebra).coe_strZero_apply U r)).trans
        ((situationSectionRingHom_strHom E hqc U.toOpens r).trans
          (Stacks.AlgebraicGeometry.RelativeProj.projZeroRingHom'_coe_of_mem _
            (Stacks.RelativeProj.Situation.sectionRingBaseMap_mem_zero
              (symSituation E) U.toOpens r)).symm))

/-- **The projective bundle of `E` is the relative `Proj` of the situation of `E`**, by an
isomorphism over the base carrying charts to charts. -/
public def presentationIso :
    (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (schemeSheafGradedAlgebra E hqc)).scheme ≅
      Stacks.RelativeProj.Situation.relativeProj (symSituation E) :=
  (situationChartFamily E hqc).iso

/-- The isomorphism of the two presentations is over the base. -/
@[reassoc]
public theorem presentationIso_hom_toBase :
    (presentationIso E hqc).hom ≫
        Stacks.RelativeProj.Situation.relativeProjToBase (symSituation E) =
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
        (schemeSheafGradedAlgebra E hqc)).toBase :=
  (situationChartFamily E hqc).iso_hom_comp

/-- The inverse of the isomorphism of the two presentations is over the base. -/
@[reassoc]
public theorem presentationIso_inv_toBase :
    (presentationIso E hqc).inv ≫
        (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
          (schemeSheafGradedAlgebra E hqc)).toBase =
      Stacks.RelativeProj.Situation.relativeProjToBase (symSituation E) := by
  rw [← presentationIso_hom_toBase, Iso.inv_hom_id_assoc]

/-- The proof that `Proj` of the identification of section rings is defined. -/
public theorem irrelevant_le_situationGradedHom (U : X.Opens) (hU : IsAffineOpen U) :
    HomogeneousIdeal.irrelevant ((symSituation E).sectionRingGrading U) ≤
      (HomogeneousIdeal.irrelevant ((situationSheafGradedAlgebra E hqc).grading U)).map
        (situationGradedHom E hqc U) :=
  Stacks.AlgebraicGeometry.ProjPresentation.irrelevant_le_hm
    (B := fun W : X.affineOpens => (symSituation E).sectionRing W.1)
    (τ := fun W : X.affineOpens => AddSubgroup ((symSituation E).sectionRing W.1))
    (ℬ := fun W : X.affineOpens => (symSituation E).sectionRingGrading W.1)
    (situationSheafGradedAlgebra E hqc).toGradedAlgebra
    (fun U => situationGradedHom E hqc U.toOpens) (situationGradedInv E hqc)
    (fun U => GradedRingHom.ext fun y => situationSectionRingHom_inv E hqc U.toOpens y) ⟨U, hU⟩

/-- The inverse of the isomorphism of the two presentations carries the chart of the situation
over an affine open to `Proj` of the identification of section rings followed by the chart of the
projective bundle. -/
@[reassoc]
public theorem relativeProjChart_presentationIso_inv (U : X.Opens) (hU : IsAffineOpen U) :
    Stacks.RelativeProj.Situation.relativeProjChart (symSituation E) ⟨U, hU⟩ ≫
        (presentationIso E hqc).inv =
      Proj.map (situationGradedHom E hqc U) (irrelevant_le_situationGradedHom E hqc U hU) ≫
        (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (schemeSheafGradedAlgebra E hqc)).chart
          U hU := by
  have h := (situationChartFamily E hqc).chart_iso_hom ⟨U, hU⟩
  refine (Iso.comp_inv_eq _).mpr ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (Proj.map (situationGradedHom E hqc U)
    (irrelevant_le_situationGradedHom E hqc U hU) ≫ ·) h.symm)
  exact (Iso.inv_hom_id_assoc (Stacks.AlgebraicGeometry.ProjPresentation.projIso
    (B := fun W : X.affineOpens => (symSituation E).sectionRing W.1)
    (τ := fun W : X.affineOpens => AddSubgroup ((symSituation E).sectionRing W.1))
    (ℬ := fun W : X.affineOpens => (symSituation E).sectionRingGrading W.1)
    (situationSheafGradedAlgebra E hqc).toGradedAlgebra
    (fun U => situationGradedHom E hqc U.toOpens) (situationGradedInv E hqc)
    (fun U => GradedRingHom.ext fun x => situationSectionRingHomInv_hom E hqc U.toOpens x)
    (fun U => GradedRingHom.ext fun y => situationSectionRingHom_inv E hqc U.toOpens y)
    ⟨U, hU⟩) _).symm

end Presentation

section BaseChange

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (E : X.Modules) [E.IsQuasicoherent]
  (hqc : IsQuasicoherentPieces E) (E' : X'.Modules) [E'.IsQuasicoherent]
  (hqc' : IsQuasicoherentPieces E') (hE : E' ≅ (Scheme.Modules.pullback g).obj E)

/-- **The morphism of projective bundles `𝐏(E') ⟶ 𝐏(E)` over `g`**, for `E' ≅ g^*E`. -/
public def bundleBaseChange :
    (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
        (schemeSheafGradedAlgebra E' hqc')).scheme ⟶
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
        (schemeSheafGradedAlgebra E hqc)).scheme :=
  (presentationIso E' hqc').hom ≫ Stacks.RelativeProj.projectiveBundleBaseChange g E E' hE ≫
    (presentationIso E hqc).inv

/-- **`𝐏(g^*E)` is the fibre product `X' ×_X 𝐏(E)`**: the square formed by the two projections,
`g` and the morphism of projective bundles is cartesian. -/
public theorem isPullback_bundleBaseChange :
    IsPullback
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase
      (bundleBaseChange g E hqc E' hqc' hE) g
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
        (schemeSheafGradedAlgebra E hqc)).toBase := by
  refine (Stacks.RelativeProj.isPullback_projectiveBundleToBase_baseChange g E E' hE).of_iso
    (presentationIso E' hqc').symm (Iso.refl _) (presentationIso E hqc).symm (Iso.refl _)
    ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans (presentationIso_inv_toBase E' hqc').symm
  · exact (Iso.inv_hom_id_assoc (presentationIso E' hqc') _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (presentationIso_inv_toBase E hqc).symm

/-- The morphism of projective bundles is a morphism over `g`. -/
@[reassoc]
public theorem bundleBaseChange_toBase :
    bundleBaseChange g E hqc E' hqc' hE ≫
        (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
          (schemeSheafGradedAlgebra E hqc)).toBase =
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
          (schemeSheafGradedAlgebra E' hqc')).toBase ≫ g :=
  (isPullback_bundleBaseChange g E hqc E' hqc' hE).w.symm

/-- **The base-change map of graded rings of sections** `Γ(U, Sym E) ⟶ Γ(W', Sym E')` over a pair
of affine opens `W' ⊆ g⁻¹U`. -/
public def bundleChartRingHom (U : X.Opens) (W' : X'.Opens) (hW' : IsAffineOpen W')
    (h : W' ≤ g ⁻¹ᵁ U) :
    (situationSheafGradedAlgebra E hqc).grading U →+*ᵍ
      (situationSheafGradedAlgebra E' hqc').grading W' :=
  ((situationGradedInv E' hqc' ⟨W', hW'⟩).comp
    (Stacks.RelativeProj.Situation.gradedBaseChange (s := symSituation E) (s' := symSituation E') g
      (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE) U W' h)).comp
    (situationGradedHom E hqc U)

/-- `Proj` of the base-change map of graded rings of sections is defined everywhere. -/
public theorem irrelevant_le_bundleChartRingHom (U : X.Opens) (hU : IsAffineOpen U) (W' : X'.Opens)
    (hW' : IsAffineOpen W') (h : W' ≤ g ⁻¹ᵁ U) :
    HomogeneousIdeal.irrelevant ((situationSheafGradedAlgebra E' hqc').grading W') ≤
      (HomogeneousIdeal.irrelevant ((situationSheafGradedAlgebra E hqc).grading U)).map
        (bundleChartRingHom g E hqc E' hqc' hE U W' hW' h) :=
  HomogeneousIdeal.irrelevant_le_map_comp (irrelevant_le_situationGradedHom E hqc U hU)
    (HomogeneousIdeal.irrelevant_le_map_comp
      (Stacks.RelativeProj.Situation.irrelevant_le_gradedBaseChange (s := symSituation E)
        (s' := symSituation E') g (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE)
        ⟨U, hU⟩ ⟨W', hW'⟩ h
        (fun m => Stacks.RelativeProj.isIso_symmetricSituationPullbackHom_app g E E' hE (m : ℤ)))
      (Stacks.AlgebraicGeometry.ProjPresentation.irrelevant_le_hn
        (B := fun W : X'.affineOpens => (symSituation E').sectionRing W.1)
        (τ := fun W : X'.affineOpens => AddSubgroup ((symSituation E').sectionRing W.1))
        (ℬ := fun W : X'.affineOpens => (symSituation E').sectionRingGrading W.1)
        (situationSheafGradedAlgebra E' hqc').toGradedAlgebra
        (fun U => situationGradedHom E' hqc' U.toOpens) (situationGradedInv E' hqc')
        (fun U => GradedRingHom.ext fun x => situationSectionRingHomInv_hom E' hqc' U.toOpens x)
        ⟨W', hW'⟩))

/-- **The morphism of projective bundles on charts**: over affine opens `W' ⊆ g⁻¹U` it is `Proj` of
the base-change map of graded rings of sections. -/
public theorem chart_comp_bundleBaseChange (U : X.Opens) (hU : IsAffineOpen U) (W' : X'.Opens)
    (hW' : IsAffineOpen W') (h : W' ≤ g ⁻¹ᵁ U) :
    (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (schemeSheafGradedAlgebra E' hqc')).chart
        W' hW' ≫ bundleBaseChange g E hqc E' hqc' hE =
      Proj.map (bundleChartRingHom g E hqc E' hqc' hE U W' hW' h)
          (irrelevant_le_bundleChartRingHom g E hqc E' hqc' hE U hU W' hW' h) ≫
        (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (schemeSheafGradedAlgebra E hqc)).chart
          U hU := by
  have h1 : (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
        (schemeSheafGradedAlgebra E' hqc')).chart W' hW' ≫ (presentationIso E' hqc').hom =
      Proj.map (situationGradedInv E' hqc' ⟨W', hW'⟩) _ ≫
        Stacks.RelativeProj.Situation.relativeProjChart (symSituation E') ⟨W', hW'⟩ :=
    (situationChartFamily E' hqc').chart_iso_hom ⟨W', hW'⟩
  have h2 : Stacks.RelativeProj.Situation.relativeProjChart (symSituation E') ⟨W', hW'⟩ ≫
        Stacks.RelativeProj.projectiveBundleBaseChange g E E' hE =
      Proj.map (Stacks.RelativeProj.Situation.gradedBaseChange (s := symSituation E)
          (s' := symSituation E') g (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE)
          U W' h) _ ≫
        Stacks.RelativeProj.Situation.relativeProjChart (symSituation E) ⟨U, hU⟩ :=
    Stacks.RelativeProj.Situation.relativeProjChart_comp_relativeProjBaseChange
      (s := symSituation E) (s' := symSituation E') g
      (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE)
      (fun m => Stacks.RelativeProj.isIso_symmetricSituationPullbackHom_app g E E' hE (m : ℤ))
      ⟨(⟨W', hW'⟩, ⟨U, hU⟩), h⟩
  have h3 := relativeProjChart_presentationIso_inv E hqc U hU
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h1)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (Proj.map _ _ ≫ ·) ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) h2).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h3))))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (Proj.map_comp _ _ _ _).symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫ _) (Proj.map_comp _ _ _ _).symm

end BaseChange

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
