module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaClauseOne

/-!
# The relative `θ` of Stacks Tag 01O9 preserves the unit

On the image of a standard open `D₊(g)` of a chart, `θ(1) · ψ(g) = θ(ψ(g)) = ψ(g) = 1 · ψ(g)` and
`ψ(g)` cancels, so `θ(1) = 1` there; these opens cover `Proj_S(𝒜)`.

## Main results

* `…GradedPowerMap.thetaPush_one`, `…GradedPowerMap.theta_map_one`: `θ` preserves the unit.
* `…GradedPowerMap.thetaUnital`: `θ` as a unital map of `ℤ`-graded `𝒪_{U(ψ)}`-algebras.

## References

* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.ModuleHomGlue

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

namespace GradedPowerMap

attribute [local irreducible] GradedPowerMap.globalMorphism
  Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.glued

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P : GradedPowerMap A f)

/-- The unit of the target of the pushforward form of `θ`, over an open of `Proj_S(𝒜)`. -/
abbrev oneK (O : (relativeProj A).scheme.Opens) : Γ(P.pushK 0, O) :=
  (Stacks.RingedSpace.pushforwardAlgebra (P.globalMorphism (relativeProj A)).toLRSHom.toShHom
    (Stacks.AlgebraicGeometry.ProjChartGradedTriple.laurentOn P.L P.coveringOpen)).one.eval (op O)

/-- **The local datum carries the unit to the unit**, on a standard open of a chart. -/
theorem localApp_thetaLoc_one (V : S.Opens) (hV : IsAffineOpen V) {e : ℕ} {g : A.sectionRing V}
    (hg : g ∈ A.grading V e) (he : 0 < e) :
    localApp ((relativeProj A).chart V hV) (P.thetaLoc V hV 0) rfl
        ((twD A).algebra.one.eval
          (op ((relativeProj A).chart V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading V) g)))
      = P.oneK _ := by
  have := Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.isInvertible_of_isInvertibleModule
    (L := P.L)
  have hO := chart_image_le V hV (AlgebraicGeometry.Proj.basicOpen (A.grading V) g)
  let p : A.grading V (1 * e) := ⟨g ^ 1, Stacks.MorphismToProj.HomogeneousRatios.pow_mem hg 1⟩
  let Pg := (Otw A (1 * e : ℕ)).presheaf.map (homOfLE hO).op
    (psiU A (1 * e) V (A.componentEquiv V (1 * e) p))
  have k₁ := heq_family
    (F := fun k => ↑Γ(Otw A k, (relativeProj A).chart V hV ''ᵁ
      AlgebraicGeometry.Proj.basicOpen (A.grading V) g))
    (G := fun k => ↑Γ(tensorPowerModule T P.L k,
      P.targetOpen V hV (AlgebraicGeometry.Proj.basicOpen (A.grading V) g)))
    (fun k => localApp ((relativeProj A).chart V hV) (P.thetaLoc V hV k) rfl) (add_zero _)
    ((twD A).algebra.mul_one ((1 * e : ℕ) : ℤ) (op _) Pg)
  simp only at k₁
  have k₃ := P.localApp_thetaLoc_psiU V hV (1 * e) rfl hO (P.targetOpen_le V hV _)
    (A.componentEquiv V (1 * e) p)
  have k₀ := (P.localApp_thetaLoc_mul V hV ((1 * e : ℕ) : ℤ) 0 rfl Pg
    ((twD A).algebra.one.eval _)).trans
    (congrArg (fun z => Stacks.TensorPowerDivision.localMul P.L z
      (localApp ((relativeProj A).chart V hV) (P.thetaLoc V hV 0) rfl
        ((twD A).algebra.one.eval _))) k₃)
  have k₂ := (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurent P.L).mul_one
    ((1 * e : ℕ) : ℤ) (op (P.targetOpen V hV (AlgebraicGeometry.Proj.basicOpen (A.grading V) g)))
    (P.psiVal V hV (1 * e) _ p)
  have key := (heq_of_eq k₀.symm).trans (k₁.trans ((heq_of_eq k₃).trans k₂.symm))
  exact P.psiVal_cancel V hV hg he 1 0 _ _ (eq_of_heq key)

/-- **The pushforward form of `θ` preserves the unit**, on every open of `Proj_S(𝒜)`. -/
theorem thetaPush_one (O : (relativeProj A).scheme.Opens) :
    (P.thetaPush 0).app O ((twD A).algebra.one.eval (op O)) = P.oneK O := by
  let ι := {q : (m : S.affineOpens) × Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.Idx
      (A.grading m.1) // (relativeProj A).chart q.1.1 q.1.2 ''ᵁ
        AlgebraicGeometry.Proj.basicOpen (A.grading q.1.1) (q.2.1.2 : A.sectionRing q.1.1) ≤ O}
  let U : ι → (relativeProj A).scheme.Opens := fun q =>
    (relativeProj A).chart q.1.1.1 q.1.1.2 ''ᵁ
      AlgebraicGeometry.Proj.basicOpen (A.grading q.1.1.1) (q.1.2.1.2 : A.sectionRing q.1.1.1)
  have hU : ∀ q, U q ≤ O := fun q => q.2
  have hcov : O ≤ ⨆ q, U q := by
    intro x hx
    have hx' := iSup_inf_preimage O hx
    obtain ⟨m, hxm⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
    rw [← chart_image_preimage m.1 m.2 O] at hxm
    obtain ⟨z, hz, rfl⟩ := hxm
    obtain ⟨d, g, hd, hg, hzg, hgO⟩ :=
      Stacks.AlgebraicGeometry.ProjShared.exists_basicOpen_homogeneous_le (A.grading m.1) hz
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨m, ⟨⟨d, ⟨g, hg⟩⟩, hd⟩⟩, ?_⟩, ⟨z, hzg, rfl⟩⟩
    refine (Scheme.Hom.image_mono _ hgO).trans ?_
    rw [chart_image_preimage m.1 m.2 O]
    exact inf_le_left
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf (P.pushK 0).isSheaf U hU hcov
    fun q => ?_
  have e1 := Stacks.AlgebraicGeometry.ModuleLimits.Hom_app_presheaf_map (P.thetaPush 0) (hU q)
    ((twD A).algebra.one.eval (op O))
  have e2 : (Otw A 0).presheaf.map (homOfLE (hU q)).op ((twD A).algebra.one.eval (op O)) =
      (twD A).algebra.one.eval (op (U q)) :=
    PresheafOfModules.sections_property (twD A).algebra.one (homOfLE (hU q)).op
  have e3 := P.thetaPush_app_eq_localApp q.1.1.1 q.1.1.2 0 (rfl : U q = U q)
    ((twD A).algebra.one.eval (op (U q)))
  have e4 := P.localApp_thetaLoc_one q.1.1.1 q.1.1.2 q.1.2.1.2.2 q.1.2.2
  have e5 : (P.pushK 0).presheaf.map (homOfLE (hU q)).op (P.oneK O) = P.oneK (U q) :=
    PresheafOfModules.sections_property (Stacks.RingedSpace.pushforwardAlgebra
      (P.globalMorphism (relativeProj A)).toLRSHom.toShHom
      (Stacks.AlgebraicGeometry.ProjChartGradedTriple.laurentOn P.L P.coveringOpen)).one
      (homOfLE (hU q)).op
  exact e1.trans ((congrArg ((P.thetaPush 0).app (U q)) e2).trans (e3.trans (e4.trans e5.symm)))

/-- **`θ` preserves the unit**: it is a map of graded algebras in the unital sense. -/
theorem theta_map_one :
    SheafOfModules.sectionsMap (P.theta.app 0)
        (Stacks.Conormal.gradedPullback (P.globalMorphism (relativeProj A)) (twD A).algebra).one =
      (Stacks.AlgebraicGeometry.ProjChartGradedTriple.laurentOn P.L P.coveringOpen).one := by
  refine (SheafOfModules.GradedAlgebra.UnitalHom.map_one_iff _).1 fun W => ?_
  obtain ⟨W⟩ := W
  have hWt : W ≤ P.globalMorphism (relativeProj A) ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have hsrc : (Stacks.Conormal.gradedPullback (P.globalMorphism (relativeProj A))
        (twD A).algebra).one.eval (op W) =
      ((Scheme.Modules.pullback (P.globalMorphism (relativeProj A))).obj (Otw A 0)).presheaf.map
        (homOfLE hWt).op
        (Scheme.Modules.pullbackSection (P.globalMorphism (relativeProj A)) (Otw A 0) ⊤
          (P.globalMorphism (relativeProj A) ⁻¹ᵁ ⊤) le_rfl ((twD A).algebra.one.eval (op ⊤))) :=
    (PresheafOfModules.sections_property (Stacks.Conormal.gradedPullback
        (P.globalMorphism (relativeProj A)) (twD A).algebra).one (homOfLE hWt).op).symm.trans
      (congrArg _ (Stacks.Conormal.gradedPullback_one_eval (P.globalMorphism (relativeProj A))
        (twD A).algebra ⊤))
  have hθ : (P.theta.app 0).val.app (op (P.globalMorphism (relativeProj A) ⁻¹ᵁ ⊤))
      (Scheme.Modules.pullbackSection (P.globalMorphism (relativeProj A)) (Otw A 0) ⊤
          (P.globalMorphism (relativeProj A) ⁻¹ᵁ ⊤) le_rfl ((twD A).algebra.one.eval (op ⊤))) =
      (P.thetaPush 0).app ⊤ ((twD A).algebra.one.eval (op ⊤)) :=
    (congrArg (fun z => (P.theta.app 0).val.app
        (op (P.globalMorphism (relativeProj A) ⁻¹ᵁ ⊤)) z)
      (Stacks.Conormal.pullbackSection_self (P.globalMorphism (relativeProj A)) (Otw A 0) ⊤
        ((twD A).algebra.one.eval (op ⊤)))).trans
    (Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.transposeAppHom_pullbackUnit
      (P.globalMorphism (relativeProj A)).toLRSHom.toShHom P.thetaPushHom 0 ⊤
      ((twD A).algebra.one.eval (op ⊤)))
  refine (congrArg (fun z => (P.theta.app 0).val.app (op W) z) hsrc).trans ?_
  refine (Stacks.AlgebraicGeometry.ProjChartRatioPullback.app_map (P.theta.app 0)
    (homOfLE hWt) _).trans ?_
  refine (congrArg (fun z => (P.powK 0).presheaf.map (homOfLE hWt).op z)
    (hθ.trans (P.thetaPush_one ⊤))).trans ?_
  exact PresheafOfModules.sections_property
    (Stacks.AlgebraicGeometry.ProjChartGradedTriple.laurentOn P.L P.coveringOpen).one
    (homOfLE hWt).op

/-- **`θ` of [Stacks, Tag 01O9] as a unital map of `ℤ`-graded `𝒪_{U(ψ)}`-algebras.** -/
def thetaUnital : SheafOfModules.GradedAlgebra.UnitalHom
    (Stacks.Conormal.gradedPullback (P.globalMorphism (relativeProj A)) (twD A).algebra)
    (Stacks.AlgebraicGeometry.ProjChartGradedTriple.laurentOn P.L P.coveringOpen) :=
  SheafOfModules.GradedAlgebra.UnitalHom.ofHom P.theta P.theta_map_one

end GradedPowerMap

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
