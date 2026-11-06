module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.SituationTower
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.TwistPullback
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.PullbackExt
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.FreeTower.ProjMapTwist
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjTwistChartComparison

/-!
# The chart descriptions of the two twists `𝒪(1)` of a projective bundle

The projective bundle `𝐏(ℰ) = Proj_X(Sym ℰ)` of a quasi-coherent module is built twice in this
library: as the relative `Proj` of the situation `Stacks.SymGraded.symSituation ℰ`, with its glued
twisting sheaves `Stacks.RelativeProj.Situation.twistSheaf`, and as `Stacks.Chow.bundle`, the
relative `Proj` of `Stacks.SymGraded.schemeSheafGradedAlgebra ℰ`, with the tautological twist
`Stacks.ProjectiveBundleSplitting.tautologicalTwist`. They are compared over `X` by
`Stacks.ProjectiveBundle.presentationIso`, and over each affine open of `X` the two twists are the
absolute twist of `Proj Γ(U, Sym ℰ)` (`Stacks.ProjectiveBundle.presentationChartTwistIso`). This
file supplies the chart descriptions those local comparisons are glued from, and their
compatibility over a nested pair of affine opens, and the glueing of chart descriptions stated at
bare chart data.

## Main results

* `Stacks.ProjectiveBundle.chartFactorTwistHom` and
  `Stacks.ProjectiveBundle.chartFactorTwistHom_tautologicalMap_unitSection`: the chart description
  of the pulled-back tautological twist along a morphism factoring through a chart by `Proj` of a
  graded ring map `φ`, and its value on the pulled-back tautological quotient of a section `x` of
  `ℰ`: the global section of `𝒪(1)` attached to `φ(x)`.
* `Stacks.ProjectiveBundle.nonempty_glueTwistIso`: a module on the target of a morphism out of a
  relative `Proj` given chartwise, described on charts as the absolute twists, pulls back to
  `𝒪_{Proj(s)}(n)` as soon as the chart descriptions do not depend on the chart they are read
  through (`Stacks.ProjectiveBundle.GlueTargetLe`). This is
  `Stacks.RelativeProj.Situation.twistChartComparisonIso` with the target an arbitrary module
  described on charts, rather than the twisting sheaf of a second situation.
* `Stacks.ProjectiveBundle.chartFactorTwistHom_eq_of_le`: for the inverse comparison of
  presentations, the chart descriptions do not depend on the chart they are read through: both are
  determined by their values on the tautological quotient, which agree because the comparison of
  graded rings of sections commutes with restriction.

## Implementation notes

The graded ring homomorphisms are typed through `Stacks.ProjectiveBundle.SituationGradedHom` and
composed through `Stacks.ProjectiveBundle.mixedGradedHom`, and the affine opens of the base of the
situation are read as affine opens of `X` through `Stacks.ProjectiveBundle.toBaseAffine`, so that
the glueing, which is stated at bare chart data, instantiates to the same terms, instance arguments
included, as the statements here: otherwise the kernel has to identify two spellings of the ring
structures on the sections, which exhausts its budget.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjDegreeOne Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.ProjTwistSections Stacks.SymGraded
open Stacks.Chow.GenuineChern

universe u

namespace Stacks.ProjectiveBundle

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- Homomorphisms from the graded ring of sections of a sheaf of graded algebras over `U` to the
graded ring of sections of a relative `Proj` situation over `V`, with the ring structures read off
the two graded algebras once and for all. -/
abbrev SituationGradedHom {s : Stacks.RelativeProj.Situation.{u}} {X : Scheme.{u}}
    (A : Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra X) (U : X.Opens)
    (V : s.base.Opens) : Type u :=
  A.grading U →+*ᵍ s.sectionRingGrading V

/-- A homomorphism into the graded ring of sections of a situation over `V`, followed by the
restriction to a smaller open `V'`. -/
abbrev mixedGradedHom {s : Stacks.RelativeProj.Situation.{u}} {X : Scheme.{u}}
    (A : Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra X) (U : X.Opens)
    {V V' : s.base.Opens} (h : V' ≤ V) (φ : SituationGradedHom (s := s) A U V) :
    SituationGradedHom (s := s) A U V' :=
  (Stacks.RelativeProj.Situation.gradedSectionRestriction s V' V h).comp φ

section SquareComparison

variable {Z' P' P Z : Scheme.{u}} (c' : Z' ⟶ P') (h : P' ⟶ P) (pm : Z' ⟶ Z) (c : Z ⟶ P)
  [IsOpenImmersion c] (hc : c' ≫ h = pm ≫ c)

/-- The comparison along a composite followed by the chart description of a pulled-back module is
the square comparison followed by the chart identification. -/
theorem pullbackComp_hom_pullbackIsoOfRestrictIso_hom (M : P.Modules) {N : Z.Modules}
    (e : M.restrict c ≅ N) :
    (Scheme.Modules.pullbackComp c' h).hom.app M ≫
        (Scheme.Modules.pullbackIsoOfRestrictIso c e pm hc).hom =
      squarePullbackRestrict c' h pm c hc M ≫ (Scheme.Modules.pullback pm).map e.hom := by
  simp only [squarePullbackRestrict, Scheme.Modules.pullbackIsoOfRestrictIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.map_comp, Category.assoc]

/-- The comparison along a composite followed by the chart description of a pulled-back module,
on a twice pulled-back section. -/
theorem pullbackIsoOfRestrictIso_hom_pullbackComp_unitSection (M : P.Modules) {N : Z.Modules}
    (e : M.restrict c ≅ N) (V : P.Opens) (s : Γ(M, V))
    (h₁ : ⊤ ≤ c' ⁻¹ᵁ (h ⁻¹ᵁ V)) (h₂ : ⊤ ≤ c ⁻¹ᵁ V) :
    (Scheme.Modules.pullbackIsoOfRestrictIso c e pm hc).hom.val.app (op ⊤)
        (((Scheme.Modules.pullbackComp c' h).hom.app M).val.app (op ⊤)
          (resTop _ h₁ (Stacks.AlgebraicGeometry.RelativeProjDegreeOne.unitSection c'
            ((Scheme.Modules.pullback h).obj M) (h ⁻¹ᵁ V)
            (Stacks.AlgebraicGeometry.RelativeProjDegreeOne.unitSection h M V s)))) =
      Stacks.AlgebraicGeometry.RelativeProjDegreeOne.unitSection pm N ⊤ (e.hom.val.app (op ⊤)
        (resTop ((Scheme.Modules.restrictFunctor c).obj M) h₂
          (M.val.map (homOfLE (c.image_preimage_le V)).op s))) := by
  have sq := congrArg (fun φ => φ.val.app (op ⊤)
      (resTop _ h₁ (Stacks.AlgebraicGeometry.RelativeProjDegreeOne.unitSection c'
        ((Scheme.Modules.pullback h).obj M) (h ⁻¹ᵁ V)
        (Stacks.AlgebraicGeometry.RelativeProjDegreeOne.unitSection h M V s))))
    (pullbackComp_hom_pullbackIsoOfRestrictIso_hom c' h pm c hc M e)
  refine (comp_app_apply _ _ _ _).symm.trans (sq.trans ?_)
  refine (comp_app_apply _ _ _ _).trans ?_
  exact (congrArg (fun z => ((Scheme.Modules.pullback pm).map e.hom).val.app (op ⊤) z)
    (squarePullbackRestrict_unitSection c' h pm c hc M V s h₁ h₂)).trans
      (unitSection_pullback_map pm e.hom ⊤ _)

end SquareComparison

/-- The chart of the other model over an affine open lands over that open. -/
private theorem top_le_preimage_chart_aux {X : Scheme.{u}} {E : X.Modules}
    (hqc : IsQuasicoherentPieces E) (U : X.Opens) (hU : IsAffineOpen U) :
    ⊤ ≤ ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU) ⁻¹ᵁ
      ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U) := fun y _ => by
  change (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase
    (((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU) y) ∈ U
  rw [Stacks.AlgebraicGeometry.RelativeProjMapDomain.toBase_chart_apply]
  exact (projInclusionToOpen _ U hU y).2

section Key

variable {X : Scheme.{u}} {E : X.Modules} (hqc : IsQuasicoherentPieces E)
  {s : Stacks.RelativeProj.Situation.{u}} {W : s.base.affineOpens}
  {P' : Scheme.{u}} (c' : AlgebraicGeometry.Proj (s.sectionRingGrading W.1) ⟶ P')
  (h : P' ⟶ (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme)
  {U : X.Opens} (hU : IsAffineOpen U)
  (φ : SituationGradedHom (s := s) (schemeSheafGradedAlgebra E hqc) U W.1)
  (hφ : HomogeneousIdeal.irrelevant (s.sectionRingGrading W.1) ≤
    (HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra E hqc).grading U)).map φ)
  (hc : c' ≫ h = AlgebraicGeometry.Proj.map φ hφ ≫
    (relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)

/-- The chart description of the pulled-back degree-one twist: the comparison of the square
`c' ≫ h = Proj.map φ ≫ chart`, the chart identification of the twist datum, and the twist
comparison of Tag 01MY for `φ`. -/
def chartFactorTwistHom :
    (Scheme.Modules.pullback c').obj ((Scheme.Modules.pullback h).obj
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)) ⟶
      twistingSheafModule (s.sectionRingGrading W.1) ((1 : ℕ) : ℤ) :=
  (Scheme.Modules.pullbackComp c' h).hom.app
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc) ≫
    (Scheme.Modules.pullbackIsoOfRestrictIso
      ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)
      (Stacks.Chow.GenuineChern.chartTwistIso E hqc U hU)
      (AlgebraicGeometry.Proj.map φ hφ) hc).hom ≫
    Stacks.ProjTwistComparison.twistMap φ hφ ((1 : ℕ) : ℤ)

/-- The chart description, on the pulled-back tautological quotient of a section over `U`: the
global section of `𝒪(1)` attached to the image of the degree-one element of the section. -/
theorem chartFactorTwistHom_unitSection (x : Γ(E, U))
    (h₁ : ⊤ ≤ c' ⁻¹ᵁ (h ⁻¹ᵁ ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U))) :
    (chartFactorTwistHom hqc c' h hU φ hφ hc).val.app (op ⊤)
        (resTop _ h₁ (unitSection c' ((Scheme.Modules.pullback h).obj
            (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc))
          (h ⁻¹ᵁ ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U))
          (unitSection h (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
            ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U)
            (((projectiveBundleTwistData E hqc).ψ 1).val.app (op U)
              ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) x))))) =
      degreeSection (s.sectionRingGrading W.1) 1
        ⟨φ (DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces U) 1
            ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) x)),
          φ.map_mem ((schemeSheafGradedAlgebra E hqc).of_mem_grading U _)⟩ := by
  have h₂ := top_le_preimage_chart_aux hqc U hU
  have hch : (relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU ''ᵁ ⊤ ≤
      (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U :=
    (Scheme.Hom.image_mono _ h₂).trans (Scheme.Hom.image_preimage_le _ _)
  have e1 := pullbackIsoOfRestrictIso_hom_pullbackComp_unitSection c' h
    (AlgebraicGeometry.Proj.map φ hφ)
    ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU) hc
    (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
    (Stacks.Chow.GenuineChern.chartTwistIso E hqc U hU)
    ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U)
    (((projectiveBundleTwistData E hqc).ψ 1).val.app (op U)
      ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) x)) h₁ h₂
  have hy1 := restrict_map_apply ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)
    (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc) h₂
    ((Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc).val.map
      (homOfLE (((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU).image_preimage_le
        _)).op (((projectiveBundleTwistData E hqc).ψ 1).val.app (op U)
          ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) x)))
  have hy2 := map_map_homOfLE (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
    (Scheme.Hom.image_mono _ h₂) (Scheme.Hom.image_preimage_le _ _)
    (((projectiveBundleTwistData E hqc).ψ 1).val.app (op U)
      ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) x))
  have hy3 := chartIso_inv_degreeSection U hU
    ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) x) hch
  have hinv := congrArg (fun ρ => ρ.val.app (op ⊤)
      (degreeSection ((schemeSheafGradedAlgebra E hqc).grading U) 1
          ⟨DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces U) 1
            ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) x),
            (schemeSheafGradedAlgebra E hqc).of_mem_grading U _⟩))
    ((projectiveBundleTwistData E hqc).chartData.chartIso U hU ((1 : ℕ) : ℤ)).inv_hom_id
  have hy : resTop ((Scheme.Modules.restrictFunctor
      ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)).obj
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)) h₂
      ((Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc).val.map
        (homOfLE (((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU).image_preimage_le
          _)).op (((projectiveBundleTwistData E hqc).ψ 1).val.app (op U)
            ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) x))) =
      ((projectiveBundleTwistData E hqc).chartData.chartIso U hU ((1 : ℕ) : ℤ)).inv.val.app
        (op ⊤) (degreeSection ((schemeSheafGradedAlgebra E hqc).grading U) 1
          ⟨DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces U) 1
            ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) x),
            (schemeSheafGradedAlgebra E hqc).of_mem_grading U _⟩) :=
    hy1.trans (hy2.trans hy3.symm)
  unfold chartFactorTwistHom
  refine (comp_app_apply _ _ _ _).trans ?_
  refine (comp_app_apply _ _ _ _).trans ?_
  refine (congrArg (fun z => (Stacks.ProjTwistComparison.twistMap φ hφ ((1 : ℕ) : ℤ)).val.app
    (op ⊤) z) e1).trans ?_
  refine (congrArg (fun z => (Stacks.ProjTwistComparison.twistMap φ hφ ((1 : ℕ) : ℤ)).val.app
    (op ⊤) (unitSection (AlgebraicGeometry.Proj.map φ hφ) _ ⊤ z))
    ((congrArg _ hy).trans hinv)).trans ?_
  refine (congrArg (fun z => (Stacks.ProjTwistComparison.twistMap φ hφ ((1 : ℕ) : ℤ)).val.app
    (op ⊤) z) (Stacks.Chow.FreeTower.pullbackGlobalSections_eq_unitSection _ _ _).symm).trans ?_
  exact Stacks.Chow.FreeTower.twistMap_degreeSection φ hφ _

/-- The chart description on the pulled-back tautological quotient of `ℰ`, at the pullback of a
section of `ℰ` over `U` along `c' ≫ h ≫ π`. -/
theorem chartFactorTwistHom_tautologicalMap_unitSection (x : Γ(E, U))
    (hT : ⊤ ≤ (c' ≫ h ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase) ⁻¹ᵁ U) :
    resTop (twistingSheafModule (s.sectionRingGrading W.1) ((1 : ℕ) : ℤ)) hT
      (((Scheme.Modules.pullbackComp c'
            (h ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase)).inv.app E ≫
          (Scheme.Modules.pullback c').map
            ((Scheme.Modules.pullbackComp h
                (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).inv.app E ≫
              (Scheme.Modules.pullback h).map
                (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc)) ≫
          chartFactorTwistHom hqc c' h hU φ hφ hc).val.app
        (op ((c' ≫ h ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase) ⁻¹ᵁ U))
        (unitSection (c' ≫ h ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase) E U x)) =
      degreeSection (s.sectionRingGrading W.1) 1
        ⟨φ (DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces U) 1
            ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) x)),
          φ.map_mem ((schemeSheafGradedAlgebra E hqc).of_mem_grading U _)⟩ := by
  have s1 := pullbackComp_inv_unitSection c'
    (h ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase) E U x
  have s2 := pullbackComp_inv_unitSection h
    (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase E U x
  have s3 := unitSection_pullback_map h (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc)
    ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U)
    (unitSection (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase E U x)
  have s4 := tautologicalMap_unitSection E hqc U x
  have sg : ((Scheme.Modules.pullbackComp h
        (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).inv.app E ≫
      (Scheme.Modules.pullback h).map
        (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc)).val.app
        (op ((h ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase) ⁻¹ᵁ U))
        (unitSection (h ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase) E U x) =
      unitSection h (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
        ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U)
        (((projectiveBundleTwistData E hqc).ψ 1).val.app (op U)
          ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) x)) :=
    (comp_app_apply _ _ _ _).trans ((congrArg _ s2).trans (s3.trans (congrArg _ s4)))
  have s5 := unitSection_pullback_map c'
    ((Scheme.Modules.pullbackComp h
        (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).inv.app E ≫
      (Scheme.Modules.pullback h).map
        (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc))
    ((h ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase) ⁻¹ᵁ U)
    (unitSection (h ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase) E U x)
  have t2 : ((Scheme.Modules.pullback c').map
        ((Scheme.Modules.pullbackComp h
            (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).inv.app E ≫
          (Scheme.Modules.pullback h).map
            (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc))).val.app
        (op ((c' ≫ h ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase) ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackComp c'
            (h ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase)).inv.app E).val.app
          (op ((c' ≫ h ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase) ⁻¹ᵁ U))
          (unitSection (c' ≫ h ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase) E U x)) =
      unitSection c' ((Scheme.Modules.pullback h).obj
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc))
        (h ⁻¹ᵁ ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U))
        (unitSection h (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
          ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U)
          (((projectiveBundleTwistData E hqc).ψ 1).val.app (op U)
            ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) x))) := by
    refine (congrArg (fun z => ((Scheme.Modules.pullback c').map
        ((Scheme.Modules.pullbackComp h
            (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).inv.app E ≫
          (Scheme.Modules.pullback h).map
            (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc))).val.app
        (op ((c' ≫ h ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase) ⁻¹ᵁ U)) z)
      s1).trans ?_
    exact s5.trans (congrArg (unitSection c' _ _) sg)
  have t3 := congrArg (fun z =>
    resTop (twistingSheafModule (s.sectionRingGrading W.1) ((1 : ℕ) : ℤ)) hT
    ((chartFactorTwistHom hqc c' h hU φ hφ hc).val.app
      (op ((c' ≫ h ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase) ⁻¹ᵁ U)) z)) t2
  refine t3.trans ?_
  refine (app_resTop _ hT _).symm.trans ?_
  exact chartFactorTwistHom_unitSection hqc c' h hU φ hφ hc x hT

end Key


/-! ### Glueing chart descriptions of a pulled-back module, at bare chart data -/

section Glue

open Stacks.RelativeProj.Situation (relativeProjChart gradedSectionRestriction
  irrelevant_le_map_gradedSectionRestriction projMap_comp_relativeProjChart twistSheaf
  twistSheafChartIso)

variable {s : Stacks.RelativeProj.Situation.{u}} {G : Scheme.{u}}
  (c : Stacks.RelativeProj.Situation.relativeProj s ⟶ G) (M₀ : G.Modules)
  {X : Scheme.{u}} (A : Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra X)
  (κ : s.base.affineOpens → X.affineOpens)
  (d : ∀ W, AlgebraicGeometry.Proj (A.grading (κ W).1) ⟶ G) [∀ W, IsOpenImmersion (d W)] (n : ℤ)
  (eB : ∀ W, M₀.restrict (d W) ≅ twistingSheaf (A.grading (κ W).1) n)
  (ι : ∀ W : s.base.affineOpens, SituationGradedHom (s := s) A (κ W).1 W.1)
  (hι : ∀ W : s.base.affineOpens, HomogeneousIdeal.irrelevant (s.sectionRingGrading W.1) ≤
    (HomogeneousIdeal.irrelevant (A.grading (κ W).1)).map (ι W))
  (hfac : ∀ W : s.base.affineOpens, relativeProjChart s W ≫ c =
    AlgebraicGeometry.Proj.map (ι W) (hι W) ≫ d W)

/-- The chart component over an affine open `W` of the base of `s` of a comparison
`c^*ℳ₀ ⟶ 𝒪_{Proj(s)}(n)`, for `ℳ₀` described on charts `d W` as the absolute twists of graded rings
`Γ(κ W, A)` mapping to the graded rings of sections of `s`: the chart description of the
pulled-back module, the twist comparison of Tag 01MY across `ι W`, and the chart description of
`𝒪_{Proj(s)}(n)` read backwards. -/
def glueTwistChartHom (W : s.base.affineOpens) :
    (Scheme.Modules.pullback (relativeProjChart s W)).obj ((Scheme.Modules.pullback c).obj M₀)
      ⟶ (Scheme.Modules.pullback (relativeProjChart s W)).obj (twistSheaf s n) :=
  (Scheme.Modules.pullbackComp (relativeProjChart s W) c).hom.app M₀
    ≫ (Scheme.Modules.pullbackIsoOfRestrictIso (d W) (eB W)
        (AlgebraicGeometry.Proj.map (ι W) (hι W)) (hfac W)).hom
    ≫ Stacks.ProjTwistComparison.twistMap (ι W) (hι W) n
    ≫ (((Scheme.Modules.restrictFunctorIsoPullback (relativeProjChart s W)).app
        (twistSheaf s n)).symm ≪≫ twistSheafChartIso s n W).inv

/-- The chart component `glueTwistChartHom` over `W` is an isomorphism as soon as the twist
comparison across `ι W` is. -/
theorem isIso_glueTwistChartHom
    (hinv : ∀ W, IsIso (Stacks.ProjTwistComparison.twistMap (ι W) (hι W) n))
    (W : s.base.affineOpens) : IsIso (glueTwistChartHom c M₀ A κ d n eB ι hι hfac W) := by
  have := hinv W
  unfold glueTwistChartHom
  infer_instance

include hι in
/-- For a nested pair `W' ⊆ W`, the irrelevant ideal of the graded ring of sections over `W'` is
contained in the ideal generated by the image of the irrelevant ideal of `Γ(κ W, A)` under `ι W`
followed by restriction to `W'`. -/
theorem irrelevant_le_glue_comp {W W' : s.base.affineOpens} (h : W' ≤ W) :
    HomogeneousIdeal.irrelevant (s.sectionRingGrading W'.1) ≤
      (HomogeneousIdeal.irrelevant (A.grading (κ W).1)).map
        (mixedGradedHom A (κ W).1 h (ι W)) :=
  HomogeneousIdeal.irrelevant_le_map_comp (hι W)
    (irrelevant_le_map_gradedSectionRestriction s W'.1 W.1 h W'.2 W.2)

omit [∀ W, IsOpenImmersion (d W)] in
include hfac in
/-- For a nested pair `W' ⊆ W`, the chart over `W'` followed by `c` is `Proj` of `ι W` followed
by restriction to `W'`, composed with the chart `d W`. -/
theorem relativeProjChart_comp_eq_glue_comp {W W' : s.base.affineOpens} (h : W' ≤ W) :
    relativeProjChart s W' ≫ c =
      AlgebraicGeometry.Proj.map (mixedGradedHom A (κ W).1 h (ι W))
          (irrelevant_le_glue_comp A κ ι hι h) ≫ d W := by
  rw [← projMap_comp_relativeProjChart (t := s) h, Category.assoc, hfac W, ← Category.assoc,
    Stacks.ProjModuleComparison.projMapComp (ι W) (hι W) (gradedSectionRestriction s W'.1 W.1 h)
      (irrelevant_le_map_gradedSectionRestriction s W'.1 W.1 h W'.2 W.2) _
      (irrelevant_le_glue_comp A κ ι hι h) rfl]

/-- The chart description through the larger chart of a nested pair. -/
def glueTargetLeLHS {W W' : s.base.affineOpens} (h : W' ≤ W) :=
  (Scheme.Modules.pullbackComp (relativeProjChart s W') c).hom.app M₀ ≫
    (Scheme.Modules.pullbackIsoOfRestrictIso (d W) (eB W)
        (AlgebraicGeometry.Proj.map (mixedGradedHom A (κ W).1 h (ι W))
          (irrelevant_le_glue_comp A κ ι hι h))
        (relativeProjChart_comp_eq_glue_comp c A κ d ι hι hfac h)).hom ≫
      Stacks.ProjTwistComparison.twistMap (mixedGradedHom A (κ W).1 h (ι W))
        (irrelevant_le_glue_comp A κ ι hι h) n

/-- The chart description through the smaller chart of a nested pair. -/
def glueTargetLeRHS (W' : s.base.affineOpens) :=
  (Scheme.Modules.pullbackComp (relativeProjChart s W') c).hom.app M₀ ≫
    (Scheme.Modules.pullbackIsoOfRestrictIso (d W') (eB W')
        (AlgebraicGeometry.Proj.map (ι W') (hι W')) (hfac W')).hom ≫
      Stacks.ProjTwistComparison.twistMap (ι W') (hι W') n

/-- The hypothesis that the chart description does not depend on the chart `d` it is read
through, for a nested pair of affine opens of the base of `s`. -/
def GlueTargetLe : Prop :=
  ∀ {W W' : s.base.affineOpens} (h : W' ≤ W),
    glueTargetLeLHS c M₀ A κ d n eB ι hι hfac h = glueTargetLeRHS c M₀ A κ d n eB ι hι hfac W'

section Nested

variable (htarget : GlueTargetLe c M₀ A κ d n eB ι hι hfac) {W W' : s.base.affineOpens} (h : W' ≤ W)

include htarget in
/-- Under `GlueTargetLe`, the chart description through the larger chart of a nested pair
`W' ⊆ W`, followed by the chart description of `𝒪_{Proj(s)}(n)` read backwards, is the chart
component `glueTwistChartHom` over `W'`. -/
theorem glueTwistChartHom_eq_of_target_le :
    (Scheme.Modules.pullbackComp (relativeProjChart s W') c).hom.app M₀
        ≫ (Scheme.Modules.pullbackIsoOfRestrictIso (d W) (eB W)
            (AlgebraicGeometry.Proj.map (mixedGradedHom A (κ W).1 h (ι W))
              (irrelevant_le_glue_comp A κ ι hι h))
            (relativeProjChart_comp_eq_glue_comp c A κ d ι hι hfac h)).hom
        ≫ Stacks.ProjTwistComparison.twistMap (mixedGradedHom A (κ W).1 h (ι W))
            (irrelevant_le_glue_comp A κ ι hι h) n
        ≫ (((Scheme.Modules.restrictFunctorIsoPullback (relativeProjChart s W')).app
            (twistSheaf s n)).symm ≪≫ twistSheafChartIso s n W').inv
      = glueTwistChartHom c M₀ A κ d n eB ι hι hfac W' := by
  have e := congrArg (· ≫ (((Scheme.Modules.restrictFunctorIsoPullback (relativeProjChart s W')).app
    (twistSheaf s n)).symm ≪≫ twistSheafChartIso s n W').inv) (htarget h)
  unfold glueTargetLeLHS glueTargetLeRHS at e
  simp only [Category.assoc] at e
  exact e

/-- For a nested pair `W' ⊆ W`, the pullback of the chart component over `W` along the inclusion
of charts is the chart description through the larger chart, followed by the chart description of
`𝒪_{Proj(s)}(n)` over `W'` read backwards. -/
theorem glueTwistChartHom_source_le :
    (Scheme.Modules.pullbackCongr (projMap_comp_relativeProjChart (t := s) h)).inv.app
          ((Scheme.Modules.pullback c).obj M₀)
        ≫ (Scheme.Modules.pullbackComp
              (AlgebraicGeometry.Proj.map (gradedSectionRestriction s W'.1 W.1 h)
                (irrelevant_le_map_gradedSectionRestriction s W'.1 W.1 h W'.2 W.2))
              (relativeProjChart s W)).inv.app ((Scheme.Modules.pullback c).obj M₀)
        ≫ (Scheme.Modules.pullback
              (AlgebraicGeometry.Proj.map (gradedSectionRestriction s W'.1 W.1 h)
                (irrelevant_le_map_gradedSectionRestriction s W'.1 W.1 h W'.2 W.2))).map
            (glueTwistChartHom c M₀ A κ d n eB ι hι hfac W)
        ≫ (Scheme.Modules.pullbackComp
              (AlgebraicGeometry.Proj.map (gradedSectionRestriction s W'.1 W.1 h)
                (irrelevant_le_map_gradedSectionRestriction s W'.1 W.1 h W'.2 W.2))
              (relativeProjChart s W)).hom.app (twistSheaf s n)
        ≫ (Scheme.Modules.pullbackCongr
            (projMap_comp_relativeProjChart (t := s) h)).hom.app (twistSheaf s n)
      = (Scheme.Modules.pullbackComp (relativeProjChart s W') c).hom.app M₀
        ≫ (Scheme.Modules.pullbackIsoOfRestrictIso (d W) (eB W)
            (AlgebraicGeometry.Proj.map (mixedGradedHom A (κ W).1 h (ι W))
              (irrelevant_le_glue_comp A κ ι hι h))
            (relativeProjChart_comp_eq_glue_comp c A κ d ι hι hfac h)).hom
        ≫ Stacks.ProjTwistComparison.twistMap (mixedGradedHom A (κ W).1 h (ι W))
            (irrelevant_le_glue_comp A κ ι hι h) n
        ≫ (((Scheme.Modules.restrictFunctorIsoPullback (relativeProjChart s W')).app
            (twistSheaf s n)).symm ≪≫ twistSheafChartIso s n W').inv :=
  Stacks.ProjTwistComparison.twistMap_chartMember_pullback_eq (ι W) (hι W)
    (gradedSectionRestriction s W'.1 W.1 h)
    (irrelevant_le_map_gradedSectionRestriction s W'.1 W.1 h W'.2 W.2)
    (irrelevant_le_glue_comp A κ ι hι h) n c (d W) (eB W) (relativeProjChart s W)
    (twistSheafChartIso s n W) (projMap_comp_relativeProjChart (t := s) h)
    (twistSheafChartIso s n W') (hfac W)
    (relativeProjChart_comp_eq_glue_comp c A κ d ι hι hfac h)
    (Stacks.RelativeProj.Situation.pullbackIsoOfRestrictIso_comp_twistMap_projMap s n h) rfl

include htarget h in
/-- Under `GlueTargetLe`, the chart components over a nested pair `W' ⊆ W` agree on an open of
the relative `Proj` lying in the images of both charts. -/
theorem localApp_glueTwistChartHom_eq_of_nested
    {V : (Stacks.RelativeProj.Situation.relativeProj s).Opens}
    {U₁ : (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).Opens}
    {U₂ : (AlgebraicGeometry.Proj (s.sectionRingGrading W'.1)).Opens}
    (e₁ : relativeProjChart s W ''ᵁ U₁ = V) (e₂ : relativeProjChart s W' ''ᵁ U₂ = V) :
    Stacks.AlgebraicGeometry.ModuleHomGlue.localApp (relativeProjChart s W)
        (Stacks.AlgebraicGeometry.ModuleHomGlue.ofPullback (relativeProjChart s W)
          (glueTwistChartHom c M₀ A κ d n eB ι hι hfac W)) e₁
      = Stacks.AlgebraicGeometry.ModuleHomGlue.localApp (relativeProjChart s W')
        (Stacks.AlgebraicGeometry.ModuleHomGlue.ofPullback (relativeProjChart s W')
          (glueTwistChartHom c M₀ A κ d n eB ι hι hfac W')) e₂ := by
  have : IsOpenImmersion (AlgebraicGeometry.Proj.map (gradedSectionRestriction s W'.1 W.1 h)
      (irrelevant_le_map_gradedSectionRestriction s W'.1 W.1 h W'.2 W.2)) :=
    Stacks.RelativeProj.Situation.projInclusionMap_eq_projMap h ▸
      Stacks.RelativeProj.Situation.isOpenImmersion_projInclusionMap s h W'.2 W.2
  exact Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_ofPullback_eq _ _
    (projMap_comp_relativeProjChart (t := s) h) _ _
    ((glueTwistChartHom_source_le c M₀ A κ d n eB ι hι hfac h).trans
      (glueTwistChartHom_eq_of_target_le c M₀ A κ d n eB ι hι hfac htarget h)) e₁ e₂

end Nested

/-- Under `GlueTargetLe`, there is a unique morphism `c^*ℳ₀ ⟶ 𝒪_{Proj(s)}(n)` whose restriction
to each chart over an affine open `W` of the base is the chart component `glueTwistChartHom`. -/
theorem existsUnique_glueTwistHom (htarget : GlueTargetLe c M₀ A κ d n eB ι hι hfac) :
    ∃! α : (Scheme.Modules.pullback c).obj M₀ ⟶ twistSheaf s n,
      ∀ W : s.base.affineOpens,
        (Scheme.Modules.restrictFunctor (relativeProjChart s W)).map α
          = Stacks.AlgebraicGeometry.ModuleHomGlue.ofPullback (relativeProjChart s W)
            (glueTwistChartHom c M₀ A κ d n eB ι hι hfac W) :=
  Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover (relativeProjChart s)
    (by simpa only [Scheme.Hom.image_top_eq_opensRange]
      using Stacks.RelativeProj.Situation.iSup_opensRange_relativeProjChart s)
    (fun W => Stacks.AlgebraicGeometry.ModuleHomGlue.ofPullback (relativeProjChart s W)
      (glueTwistChartHom c M₀ A κ d n eB ι hι hfac W))
    (fun W W' U₁ U₂ V e₁ e₂ =>
      Stacks.RelativeProj.Situation.localApp_relativeProjChart_eq_of_nested
        (fun W => Stacks.AlgebraicGeometry.ModuleHomGlue.ofPullback (relativeProjChart s W)
          (glueTwistChartHom c M₀ A κ d n eB ι hι hfac W))
        (fun _ _ hle _ _ _ f₁ f₂ =>
          localApp_glueTwistChartHom_eq_of_nested c M₀ A κ d n eB ι hι hfac htarget hle f₁ f₂)
        W W' U₁ U₂ V e₁ e₂)

/-- **The comparison `c^*ℳ₀ ≅ 𝒪_{Proj(s)}(n)`** glued from the chart components, an isomorphism as
soon as each twist comparison across `ι W` is. -/
theorem nonempty_glueTwistIso (htarget : GlueTargetLe c M₀ A κ d n eB ι hι hfac)
    (hinv : ∀ W, IsIso (Stacks.ProjTwistComparison.twistMap (ι W) (hι W) n)) :
    Nonempty ((Scheme.Modules.pullback c).obj M₀ ≅ twistSheaf s n) := by
  obtain ⟨α, hα, -⟩ := existsUnique_glueTwistHom c M₀ A κ d n eB ι hι hfac htarget
  have : IsIso α := by
    refine Scheme.Modules.isIso_of_isIso_restrictFunctor_map _ (relativeProjChart s)
      (fun x => Stacks.RelativeProj.Situation.exists_relativeProjChart_eq s x) fun W => ?_
    rw [hα W]
    have := isIso_glueTwistChartHom c M₀ A κ d n eB ι hι hfac hinv W
    unfold Stacks.AlgebraicGeometry.ModuleHomGlue.ofPullback
    infer_instance
  exact ⟨asIso α⟩

end Glue

section Presentation

open Stacks.RelativeProj.Situation (relativeProjChart gradedSectionRestriction
  irrelevant_le_map_gradedSectionRestriction projMap_comp_relativeProjChart twistSheaf
  twistSheafChartIso)

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] (hqc : IsQuasicoherentPieces E)

/-- The inverse comparison of the two presentations of the projective bundle, with its source
and target at the spellings the twists are stated at. -/
def presInv : Stacks.RelativeProj.Situation.relativeProj (symSituation E) ⟶
    (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme :=
  (presentationIso E hqc).inv

/-- An affine open of the base of the situation model, read as an affine open of `X`. -/
def toBaseAffine (W : (symSituation E).base.affineOpens) : X.affineOpens := W

/-- The comparison `Stacks.SymGraded.situationGradedHom` of the graded rings of sections of the two
presentations, with its source spelled at `Stacks.SymGraded.schemeSheafGradedAlgebra`, the
spelling the twist datum of `Stacks.Chow.bundle` is stated at. -/
def presGradedHom (W : (symSituation E).base.affineOpens) :
    SituationGradedHom (s := symSituation E) (schemeSheafGradedAlgebra E hqc)
      (toBaseAffine E W).1 W.1 :=
  situationGradedHom E hqc W.1

/-- The comparison of the graded rings of sections over an affine open covers the irrelevant
ideal. -/
theorem irrelevant_le_map_situationGradedHom (W : (symSituation E).base.affineOpens) :
    HomogeneousIdeal.irrelevant ((symSituation E).sectionRingGrading W.1) ≤
      (HomogeneousIdeal.irrelevant
        ((schemeSheafGradedAlgebra E hqc).grading (toBaseAffine E W).1)).map
        (presGradedHom E hqc W) :=
  Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id _ _ (presentation_hmn E hqc ⟨W.1, W.2⟩)

/-- The twist comparison in degree one across the comparison `presGradedHom` of graded rings of
sections is an isomorphism. -/
instance isIso_twistMap_presGradedHom (W : (symSituation E).base.affineOpens) :
    IsIso (Stacks.ProjTwistComparison.twistMap (presGradedHom E hqc W)
      (irrelevant_le_map_situationGradedHom E hqc W) ((1 : ℕ) : ℤ)) :=
  isIso_twistMap_situationGradedHom E hqc ⟨W.1, W.2⟩

/-- The chart of the situation model over `W`, followed by the inverse comparison of
presentations, is `Proj` of the comparison of graded rings followed by the chart of the other
model. -/
theorem relativeProjChart_comp_presentationIso_inv_eq (W : (symSituation E).base.affineOpens) :
    relativeProjChart (symSituation E) W ≫ (presInv E hqc) =
      AlgebraicGeometry.Proj.map (presGradedHom E hqc W)
          (irrelevant_le_map_situationGradedHom E hqc W) ≫
        (relativeProj (schemeSheafGradedAlgebra E hqc)).chart (toBaseAffine E W).1
          (toBaseAffine E W).2 :=
  relativeProjChart_presentationIso_inv E hqc ⟨W.1, W.2⟩

/-- The irrelevant ideal over the smaller affine open is covered by the image of the mixed
homomorphism of a nested pair. -/
theorem irrelevant_le_map_situationGradedHom_comp {W W' : (symSituation E).base.affineOpens}
    (h : W' ≤ W) :
    HomogeneousIdeal.irrelevant ((symSituation E).sectionRingGrading W'.1) ≤
      (HomogeneousIdeal.irrelevant
        ((schemeSheafGradedAlgebra E hqc).grading (toBaseAffine E W).1)).map
        (mixedGradedHom (schemeSheafGradedAlgebra E hqc) (toBaseAffine E W).1 h
          (presGradedHom E hqc W)) :=
  irrelevant_le_glue_comp _ (toBaseAffine E) (presGradedHom E hqc)
    (irrelevant_le_map_situationGradedHom E hqc) h

/-- The chart of the situation model over the smaller open of a nested pair, followed by the
inverse comparison of presentations, factors through the chart over the larger open. -/
theorem relativeProjChart_comp_presentationIso_inv_eq_of_le
    {W W' : (symSituation E).base.affineOpens} (h : W' ≤ W) :
    relativeProjChart (symSituation E) W' ≫ (presInv E hqc) =
      AlgebraicGeometry.Proj.map
          (mixedGradedHom (schemeSheafGradedAlgebra E hqc) (toBaseAffine E W).1 h
            (presGradedHom E hqc W))
          (irrelevant_le_map_situationGradedHom_comp E hqc h) ≫
        (relativeProj (schemeSheafGradedAlgebra E hqc)).chart (toBaseAffine E W).1
          (toBaseAffine E W).2 :=
  relativeProjChart_comp_eq_glue_comp (presInv E hqc) (schemeSheafGradedAlgebra E hqc)
    (toBaseAffine E)
    (fun W => (relativeProj (schemeSheafGradedAlgebra E hqc)).chart (toBaseAffine E W).1
      (toBaseAffine E W).2)
    (presGradedHom E hqc) (irrelevant_le_map_situationGradedHom E hqc)
    (relativeProjChart_comp_presentationIso_inv_eq E hqc) h

omit [SheafOfModules.IsQuasicoherent E] in
/-- The chart of the other model over an affine open lands over that open. -/
theorem top_le_preimage_chart (U : X.Opens) (hU : IsAffineOpen U) :
    ⊤ ≤ ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU) ⁻¹ᵁ
      ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U) :=
  top_le_preimage_chart_aux hqc U hU

/-- A morphism out of a pullback, on a pulled-back section restricted to a smaller open, both
read on the whole space. -/
theorem resTop_app_unitSection_restrict {Y Z : Scheme.{u}} (f : Y ⟶ Z) (E : Z.Modules)
    {N : Y.Modules} (Ψ : (Scheme.Modules.pullback f).obj E ⟶ N) {U U' : Z.Opens} (h : U' ≤ U)
    (hT : ⊤ ≤ f ⁻¹ᵁ U) (hT' : ⊤ ≤ f ⁻¹ᵁ U') (x : Γ(E, U)) :
    resTop N hT (Ψ.val.app (op (f ⁻¹ᵁ U)) (unitSection f E U x)) =
      resTop N hT'
        (Ψ.val.app (op (f ⁻¹ᵁ U')) (unitSection f E U' (E.val.map (homOfLE h).op x))) := by
  rw [unitSection_restrict f E h x, resTop_app_map Ψ hT' (Scheme.Hom.preimage_mono _ h)]
  exact (app_resTop Ψ hT _).symm

/-- The comparison of graded rings commutes with restriction, on the degree-one element of a
section of `ℰ`. -/
theorem situationGradedHom_comp_of_symmetricAlgebraGen
    {W W' : (symSituation E).base.affineOpens} (h : W' ≤ W) (x : Γ(E, (toBaseAffine E W).1)) :
    (mixedGradedHom (schemeSheafGradedAlgebra E hqc) (toBaseAffine E W).1 h
        (presGradedHom E hqc W))
        (DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces (toBaseAffine E W).1) 1
          ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op (toBaseAffine E W).1) x)) =
      presGradedHom E hqc W'
        (DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces (toBaseAffine E W').1) 1
          ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op (toBaseAffine E W').1)
            (E.val.map
              (homOfLE (show (toBaseAffine E W').1 ≤ (toBaseAffine E W).1 from h)).op x))) := by
  have hres := DFunLike.congr_fun (situationGradedHom_res E hqc W'.1 W.1 h)
    (DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces (toBaseAffine E W).1) 1
        ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op (toBaseAffine E W).1) x))
  refine hres.symm.trans ((GradedRingHom.comp_apply _ _ _).trans ?_)
  refine congrArg (situationGradedHom E hqc W'.1) ?_
  refine ((situationSheafGradedAlgebra E hqc).resRingHom_of h _).trans ?_
  exact congrArg
    (DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces (toBaseAffine E W').1) 1)
    (PresheafOfModules.naturality_apply (Scheme.Modules.symmetricAlgebraGen X E).val
      (homOfLE (show (toBaseAffine E W').1 ≤ (toBaseAffine E W).1 from h)).op x).symm

/-- **The chart description of the pulled-back twist does not depend on the chart of the other
model it is read through.** For a nested pair `W' ⊆ W`, the inverse image of `𝒪(1)` along the
chart of the situation model over `W'` and the inverse comparison of presentations, read through
the chart over `W` by the mixed homomorphism, is the same as read through the chart over `W'`.

Both are determined by their values on the tautological quotient at the pulled-back sections of
`ℰ` over `W`, and both send such a section to the global section of `𝒪(1)` attached to the image
of its degree-one element, the two images agreeing because the comparison of graded rings
commutes with restriction. -/
theorem chartFactorTwistHom_eq_of_le {W W' : (symSituation E).base.affineOpens} (h : W' ≤ W) :
    chartFactorTwistHom hqc (relativeProjChart (symSituation E) W') (presInv E hqc)
        (toBaseAffine E W).2
        (mixedGradedHom (schemeSheafGradedAlgebra E hqc) (toBaseAffine E W).1 h
          (presGradedHom E hqc W))
        (irrelevant_le_map_situationGradedHom_comp E hqc h)
        (relativeProjChart_comp_presentationIso_inv_eq_of_le E hqc h) =
      chartFactorTwistHom hqc (relativeProjChart (symSituation E) W') (presInv E hqc)
        (toBaseAffine E W').2 (presGradedHom E hqc W')
        (irrelevant_le_map_situationGradedHom E hqc W')
        (relativeProjChart_comp_presentationIso_inv_eq E hqc W') := by
  have hTW' : ⊤ ≤ (relativeProjChart (symSituation E) W' ≫ (presInv E hqc) ≫
      (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase) ⁻¹ᵁ (toBaseAffine E W').1 := by
    have e : relativeProjChart (symSituation E) W' ≫ (presInv E hqc) ≫
        (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase =
        AlgebraicGeometry.Proj.map (presGradedHom E hqc W')
          (irrelevant_le_map_situationGradedHom E hqc W') ≫
          (relativeProj (schemeSheafGradedAlgebra E hqc)).chart (toBaseAffine E W').1
            (toBaseAffine E W').2 ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫
        (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase)
        (relativeProjChart_comp_presentationIso_inv_eq E hqc W')).trans (Category.assoc _ _ _))
    rw [e, Scheme.Hom.comp_preimage, ← Scheme.Hom.preimage_top
      (AlgebraicGeometry.Proj.map (presGradedHom E hqc W')
        (irrelevant_le_map_situationGradedHom E hqc W'))]
    exact Scheme.Hom.preimage_mono _
      ((top_le_preimage_chart E hqc (toBaseAffine E W').1 (toBaseAffine E W').2).trans
        (Scheme.Hom.comp_preimage _ _ _).ge)
  have hTW : ⊤ ≤ (relativeProjChart (symSituation E) W' ≫ (presInv E hqc) ≫
      (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase) ⁻¹ᵁ (toBaseAffine E W).1 :=
    hTW'.trans (Scheme.Hom.preimage_mono _ h)
  have hep : Epi ((Scheme.Modules.pullbackComp (relativeProjChart (symSituation E) W')
        (presInv E hqc ≫
          (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase)).inv.app E ≫
      (Scheme.Modules.pullback (relativeProjChart (symSituation E) W')).map
        ((Scheme.Modules.pullbackComp (presInv E hqc)
            (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).inv.app E ≫
          (Scheme.Modules.pullback (presInv E hqc)).map
            (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc))) := by
    have h1 := Stacks.ProjectiveBundleSplitting.epi_tautologicalMap E hqc
    have h2 := Functor.preservesEpimorphisms_of_adjunction
      (Scheme.Modules.pullbackPushforwardAdjunction (presInv E hqc))
    have h3 := Functor.preservesEpimorphisms_of_adjunction
      (Scheme.Modules.pullbackPushforwardAdjunction (relativeProjChart (symSituation E) W'))
    have h4 : Epi ((Scheme.Modules.pullbackComp (presInv E hqc)
            (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).inv.app E ≫
          (Scheme.Modules.pullback (presInv E hqc)).map
            (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc)) :=
      epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (NatIso.inv_app_isIso _ _)) (Functor.map_epi _ _)
    exact epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (NatIso.inv_app_isIso _ _)) (Functor.map_epi _ _)
  refine hep.left_cancellation _ _ ?_
  rw [Category.assoc, Category.assoc]
  refine pullback_hom_ext_of_isAffineOpen _ (toBaseAffine E W).2 (top_le_iff.mp hTW) E fun x => ?_
  apply resTop_injective (twistingSheafModule ((symSituation E).sectionRingGrading W'.1)
    ((1 : ℕ) : ℤ)) hTW
  refine (chartFactorTwistHom_tautologicalMap_unitSection hqc _ _ (toBaseAffine E W).2 _ _ _ x
    hTW).trans ?_
  refine Eq.trans ?_ (resTop_app_unitSection_restrict _ E _
    (show (toBaseAffine E W').1 ≤ (toBaseAffine E W).1 from h) hTW hTW' x).symm
  exact (congrArg (degreeSection ((symSituation E).sectionRingGrading W'.1) 1)
    (Subtype.ext (situationGradedHom_comp_of_symmetricAlgebraGen E hqc h x))).trans
    (chartFactorTwistHom_tautologicalMap_unitSection hqc
      (relativeProjChart (symSituation E) W') (presInv E hqc) (toBaseAffine E W').2
      (presGradedHom E hqc W')
      (irrelevant_le_map_situationGradedHom E hqc W')
      (relativeProjChart_comp_presentationIso_inv_eq E hqc W')
      (E.val.map (homOfLE (show (toBaseAffine E W').1 ≤ (toBaseAffine E W).1 from h)).op x)
      hTW').symm

end Presentation

end Stacks.ProjectiveBundle

end
