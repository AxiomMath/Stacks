module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaClauseOne

/-!
# The relative `θ` of Stacks Tag 01O9 is determined by clause (1)

A map of graded algebras `θ' : r_{ℒ,ψ}^*(⨁_{d ∈ ℤ} 𝒪(d)) ⟶ ⨁_{d ∈ ℤ} ℒ^{⊗ d}|_{U(ψ)}` satisfying
clause (1) of [Stacks, Tag 01O9] is `θ`. Its adjoint transpose is multiplicative and carries `ψ(a)`
to `ψ(a)`; on the image of a standard open `D₊(g)` of a chart every section is `ψ(x)/ψ(g)^j`, and
`ψ(g)^j` cancels, so the transpose agrees with the local datum of `θ` on every chart.

## Main results

* `…GradedPowerMap.eq_localApp_of_laws`: a multiplicative family reading `ψ` is the local datum on
  a standard open of a chart.
* `…GradedPowerMap.eq_thetaPush_of_laws`: a multiplicative family of morphisms reading `ψ` is
  `thetaPush`.
* `…GradedPowerMap.eq_theta_of_clauseOne`: **a map of graded algebras with clause (1) is `θ`.**

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

/-- **A multiplicative family reading `ψ` is the local datum** on the image of a standard open of
the chart over `V`. -/
theorem eq_localApp_of_laws (V : S.Opens) (hV : IsAffineOpen V) {e : ℕ} {g : A.sectionRing V}
    (hg : g ∈ A.grading V e) (he : 0 < e)
    (F : ∀ k : ℤ, Γ(Otw A k, (relativeProj A).chart V hV ''ᵁ
        AlgebraicGeometry.Proj.basicOpen (A.grading V) g) →
      Γ(tensorPowerModule T P.L k,
        P.targetOpen V hV (AlgebraicGeometry.Proj.basicOpen (A.grading V) g)))
    (hM : ∀ (i j : ℤ) (s t), F (i + j) (((twD A).algebra.mul i j).app
        (op ((relativeProj A).chart V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading V) g))
          s t) = Stacks.TensorPowerDivision.localMul P.L (F i s) (F j t))
    (hP : ∀ (d : ℕ) (p : A.grading V d),
      F d ((Otw A d).presheaf.map (homOfLE (chart_image_le V hV
          (AlgebraicGeometry.Proj.basicOpen (A.grading V) g))).op
        (psiU A d V (A.componentEquiv V d p))) =
          P.psiVal V hV d (AlgebraicGeometry.Proj.basicOpen (A.grading V) g) p)
    (n : ℤ) (t : Γ(Otw A n, (relativeProj A).chart V hV ''ᵁ
        AlgebraicGeometry.Proj.basicOpen (A.grading V) g)) :
    F n t = localApp ((relativeProj A).chart V hV) (P.thetaLoc V hV n) rfl t := by
  have hO : (relativeProj A).chart V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading V) g ≤
      (relativeProj A).toBase ⁻¹ᵁ V := chart_image_le V hV _
  obtain ⟨j, N, x, hN, hH⟩ := exists_psiU_mul_eq V hV hg he n t
  have k₁ := heq_family
    (F := fun k => ↑Γ(Otw A k, (relativeProj A).chart V hV ''ᵁ
      AlgebraicGeometry.Proj.basicOpen (A.grading V) g))
    (G := fun k => ↑Γ(tensorPowerModule T P.L k,
      P.targetOpen V hV (AlgebraicGeometry.Proj.basicOpen (A.grading V) g)))
    (fun k => localApp ((relativeProj A).chart V hV) (P.thetaLoc V hV k) rfl) hN hH
  have k₂ := heq_family
    (F := fun k => ↑Γ(Otw A k, (relativeProj A).chart V hV ''ᵁ
      AlgebraicGeometry.Proj.basicOpen (A.grading V) g))
    (G := fun k => ↑Γ(tensorPowerModule T P.L k,
      P.targetOpen V hV (AlgebraicGeometry.Proj.basicOpen (A.grading V) g))) F hN hH
  simp only at k₁ k₂
  rw [P.localApp_thetaLoc_mul V hV _ _ rfl] at k₁
  rw [P.localApp_thetaLoc_psiU V hV _ rfl hO (P.targetOpen_le V hV _),
    P.localApp_thetaLoc_psiU V hV _ rfl hO (P.targetOpen_le V hV _)] at k₁
  have k₃ := (heq_of_eq ((hM _ _ _ t).trans
    (congrArg (fun z => Stacks.TensorPowerDivision.localMul P.L z (F n t)) (hP _ _)))).symm.trans
    (k₂.trans (heq_of_eq (hP _ _)))
  exact P.psiVal_cancel V hV hg he j n _ _ (eq_of_heq (k₃.trans k₁.symm))

/-- **A multiplicative family of morphisms reading `ψ` is `thetaPush`.** -/
theorem eq_thetaPush_of_laws (φ : ∀ n : ℤ, Otw A n ⟶ P.pushK n)
    (hM : ∀ (i j : ℤ) (O : (relativeProj A).scheme.Opens) (s : Γ(Otw A i, O)) (t : Γ(Otw A j, O)),
      (φ (i + j)).app O (((twD A).algebra.mul i j).app (op O) s t) =
        Stacks.TensorPowerDivision.localMul P.L ((φ i).app O s) ((φ j).app O t))
    (hP : ∀ (V : S.Opens) (d : ℕ) (a : Γ(A.piece (d : ℤ), V)),
      (φ d).app ((relativeProj A).toBase ⁻¹ᵁ V) (psiU A d V a) =
        (tensorPowerModule T P.L d).presheaf.map (homOfLE (P.image_preimage_preimage_le V)).op
          ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare P.L d).hom.app (f ⁻¹ᵁ V)
            (P.value d V a)))
    (n : ℤ) : φ n = P.thetaPush n := by
  refine P.eq_thetaPush n fun V hV => ?_
  refine Scheme.Modules.hom_ext _ _ fun W₁ => ?_
  refine ConcreteCategory.hom_ext _ _ fun s => ?_
  change (φ n).app ((relativeProj A).chart V hV ''ᵁ W₁) s =
    localApp ((relativeProj A).chart V hV) (P.thetaLoc V hV n) rfl s
  let ι := {p : Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.Idx (A.grading V) //
    AlgebraicGeometry.Proj.basicOpen (A.grading V) (p.1.2 : A.sectionRing V) ≤ W₁}
  let U : ι → (relativeProj A).scheme.Opens := fun k =>
    (relativeProj A).chart V hV ''ᵁ
      AlgebraicGeometry.Proj.basicOpen (A.grading V) (k.1.1.2 : A.sectionRing V)
  have hUO : ∀ k, U k ≤ (relativeProj A).chart V hV ''ᵁ W₁ := fun k =>
    Scheme.Hom.image_mono _ k.2
  have hcov : (relativeProj A).chart V hV ''ᵁ W₁ ≤ ⨆ k, U k := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨d, g, hd, hg, hzg, hgW⟩ :=
      Stacks.AlgebraicGeometry.ProjShared.exists_basicOpen_homogeneous_le (A.grading V) hz
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨⟨d, ⟨g, hg⟩⟩, hd⟩, hgW⟩, ⟨z, hzg, rfl⟩⟩
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf (P.pushK n).isSheaf U hUO hcov
    fun k => ?_
  refine (Stacks.AlgebraicGeometry.ModuleLimits.Hom_app_presheaf_map (φ n) (hUO k) s).trans ?_
  refine Eq.trans ?_ (localApp_map _ _ rfl rfl (hUO k) s)
  refine P.eq_localApp_of_laws V hV k.1.1.2.2 k.1.2 (fun m => (φ m).app (U k))
    (fun i j s t => hM i j (U k) s t) (fun d p => ?_) n _
  have hle : U k ≤ (relativeProj A).toBase ⁻¹ᵁ V := chart_image_le V hV _
  refine (Stacks.AlgebraicGeometry.ModuleLimits.Hom_app_presheaf_map (φ d) hle _).symm.trans ?_
  refine (congrArg ((P.pushK d).presheaf.map (homOfLE hle).op) (hP V d _)).trans ?_
  refine (pushforward_restrict_map P.coveringOpen.ι (P.globalMorphism (relativeProj A))
    (tensorPowerModule T P.L d) (homOfLE hle) _).trans ?_
  exact map_map _ _ _ _ _

/-- The product of `⨁_{d ∈ ℤ} ℒ^{⊗ d}|_{U(ψ)}` on sections is the product of local sections of
the tensor powers. -/
theorem laurentOn_mul (i j : ℤ) (W : P.coveringOpen.toScheme.Opens)
    (a : Γ(P.powK i, W)) (b : Γ(P.powK j, W)) :
    ((Stacks.AlgebraicGeometry.ProjChartGradedTriple.laurentOn P.L P.coveringOpen).mul i j).app
        (op W) a b = Stacks.TensorPowerDivision.localMul P.L a b := rfl

/-- **`θ` is the only map of graded algebras
`r_{ℒ,ψ}^*(⨁_{d ∈ ℤ} 𝒪(d)) ⟶ ⨁_{d ∈ ℤ} ℒ^{⊗ d}|_{U(ψ)}` with clause (1) of [Stacks, Tag 01O9]**,
in exactly the form `…GradedPowerMap.theta_clauseOne` states it. -/
theorem eq_theta_of_clauseOne {θ' : SheafOfModules.GradedAlgebra.Hom
      (Stacks.Conormal.gradedPullback (P.globalMorphism (relativeProj A)) (twD A).algebra)
      (Stacks.AlgebraicGeometry.ProjChartGradedTriple.laurentOn P.L P.coveringOpen)}
    (h : ∀ (V : S.Opens) (d : ℕ) (a : Γ(A.piece (d : ℤ), V)),
      (P.powK d).presheaf.map (eqToHom (P.toBase_preimage_eq V)).op
          ((θ'.app d).val.app
            (op (P.globalMorphism (relativeProj A) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
            (Stacks.RingedSpace.pullbackUnit (P.globalMorphism (relativeProj A)).toLRSHom.toShHom
              (Otw A d) (op ((relativeProj A).toBase ⁻¹ᵁ V)) (psiU A d V a))) =
        (tensorPowerModule T P.L d).presheaf.map
          (homOfLE (P.coveringOpen.ι.image_preimage_le (f ⁻¹ᵁ V))).op
          ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare P.L d).hom.app (f ⁻¹ᵁ V)
            (P.value d V a))) :
    θ' = P.theta := by
  let r := (P.globalMorphism (relativeProj A)).toLRSHom.toShHom
  let φ : ∀ n : ℤ, Otw A n ⟶ P.pushK n := fun n =>
    ((Stacks.RingedSpace.pullbackAdjunction r).homEquiv _ _) (θ'.app n)
  have hφ : ∀ (n : ℤ) (O : (relativeProj A).scheme.Opens) (s : Γ(Otw A n, O)),
      (φ n).app O s = (θ'.app n).val.app (op (P.globalMorphism (relativeProj A) ⁻¹ᵁ O))
        (Stacks.RingedSpace.pullbackUnit r (Otw A n) (op O) s) := fun n O s =>
    SheafOfModules.GradedAlgebra.homEquiv_val_app r (θ'.app n) (op O) s
  have key : ∀ n, φ n = P.thetaPush n := by
    refine P.eq_thetaPush_of_laws φ (fun i j O s t => ?_) (fun V d a => ?_)
    · refine (hφ (i + j) O (((twD A).algebra.mul i j).app (op O) s t)).trans ?_
      rw [hφ, hφ]
      refine (congrArg ((θ'.app (i + j)).val.app (op (P.globalMorphism (relativeProj A) ⁻¹ᵁ O)))
        (Stacks.RingedSpace.pullbackGradedAlgebra_mul_pullbackUnit r (twD A).algebra
          i j O s t).symm).trans ?_
      exact (θ'.map_mul i j _ _ _).trans (P.laurentOn_mul i j _ _ _)
    · rw [hφ]
      have e : (θ'.app d).val.app
            (op (P.globalMorphism (relativeProj A) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
            (Stacks.RingedSpace.pullbackUnit r (Otw A d) (op ((relativeProj A).toBase ⁻¹ᵁ V))
              (psiU A d V a)) =
          (P.powK d).presheaf.map (eqToHom (P.toBase_preimage_eq V).symm).op
            ((P.powK d).presheaf.map (eqToHom (P.toBase_preimage_eq V)).op
              ((θ'.app d).val.app
                (op (P.globalMorphism (relativeProj A) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
                (Stacks.RingedSpace.pullbackUnit r (Otw A d) (op ((relativeProj A).toBase ⁻¹ᵁ V))
                  (psiU A d V a)))) :=
        ((map_map (P.powK d) (eqToHom (P.toBase_preimage_eq V)).op
          (eqToHom (P.toBase_preimage_eq V).symm).op (𝟙 _) _).trans
          (map_id_apply (P.powK d) _ _)).symm
      refine e.trans ((congrArg _ (h V d a)).trans ?_)
      have e2 : ∀ y : Γ(tensorPowerModule T P.L d, P.coveringOpen.ι ''ᵁ (P.toBase ⁻¹ᵁ V)),
          (P.powK d).presheaf.map (eqToHom (P.toBase_preimage_eq V).symm).op y =
          (tensorPowerModule T P.L d).presheaf.map
            (P.coveringOpen.ι.opensFunctor.map (eqToHom (P.toBase_preimage_eq V).symm)).op y :=
        fun y => rfl
      exact (e2 _).trans (map_map _ _ _ _ _)
  refine SheafOfModules.GradedAlgebra.Hom.ext fun n => ?_
  rw [theta_app, ← key n]
  exact (((Stacks.RingedSpace.pullbackAdjunction r).homEquiv _ _).symm_apply_apply _).symm

end GradedPowerMap

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
