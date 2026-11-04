module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.DegreeZero.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjBaseChangeGlobal
public import StacksFrontier.AlgebraicGeometry.Blowup.RelativeProj
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.FlatAndRelativeDimension
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.SectionRings
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Charts.Descent
public import StacksFrontier.AlgebraicGeometry.RelativeProj.LocalAtBase
public import StacksFrontier.AlgebraicGeometry.RelativeProjBundle.Basic
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.FreeSituationChart

/-!
# The projection of `𝐏(𝒪_X^{n+1})` is flat, for the relative-`Proj`-situation presentation

`Stacks.RelativeProj.projectiveBundleToBase X E` is the projection of the projective bundle built
by glueing the `Proj` of the graded rings of homogeneous sections of `Sym E` over the affine opens
of `X`. **This file proves it flat for `E = 𝒪_X^{n+1}`.**

## Main results

* `Stacks.SymGraded.isIso_sectionRingZeroMap_freeSituation`: the degree-zero identification of
  each chart is an isomorphism.
* `Stacks.SymGraded.flat_toSpecZero_freeSituationGrading`: **the chart is flat over `Spec` of its
  degree-zero part.**
* `Stacks.SymGraded.flat_relativeProjToBase_freeSituation` and
  `Stacks.SymGraded.flat_projectiveBundleToBase_freeModule`: **the projection of
  `𝐏(𝒪_X^{n+1}) = Proj_X(Sym 𝒪_X^{n+1})` is flat.**

## References

* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.SymGraded

universe u

variable {X : Scheme.{u}} (n : ℕ)

/-! ### The section ring as a graded ring, indexed by the opens of `X` -/

/-- The internal grading of the section ring over an open `U` of `X` is a graded ring. -/
instance freeSituationGradedRing (U : X.Opens) :
    GradedRing ((freeSituation X n).sectionRingGrading U) :=
  RelativeProj.Situation.sectionRingGradingGradedRing (freeSituation X n) U

/-- **The degree-zero identification of each chart is an isomorphism.** -/
theorem isIso_sectionRingZeroMap_freeSituation (U : X.Opens) :
    IsIso (RelativeProj.Situation.sectionRingZeroMap (freeSituation X n) U) :=
  RelativeProj.Situation.isIso_sectionRingZeroMap (freeSituation X n) U
    (AlgebraicGeometry.Scheme.Modules.bijective_smul_one_symmetricAlgebra X
      (freeModule (X := X) (coordIndex n)) U)

/-! ### Transporting flatness along the chart comparison -/

/-- A graded ring homomorphism with a one-sided inverse satisfies the hypothesis of
`AlgebraicGeometry.Proj.map`. -/
theorem irrelevant_le_map_of_graded_comp_eq_id {R S σ τ : Type u} [CommRing R] [CommRing S]
    [SetLike σ R] [AddSubgroupClass σ R] [SetLike τ S] [AddSubgroupClass τ S]
    {𝒟 : ℕ → σ} {ℰ : ℕ → τ} [GradedRing 𝒟] [GradedRing ℰ] (f : 𝒟 →+*ᵍ ℰ) (g : ℰ →+*ᵍ 𝒟)
    (hfg : f.comp g = GradedRingHom.id ℰ) :
    HomogeneousIdeal.irrelevant ℰ ≤ (HomogeneousIdeal.irrelevant 𝒟).map f := by
  refine (HomogeneousIdeal.irrelevant_le _).2 fun k hk x hx => ?_
  have hxy : f (g x) = x := by
    show (f.comp g) x = x
    rw [hfg]; rfl
  rw [← hxy]
  exact Ideal.mem_map_of_mem f (HomogeneousIdeal.mem_irrelevant_of_mem _ hk (g.map_mem hx))

/-- The irrelevant ideal of the polynomial ring is reached by the comparison. -/
theorem irrelevant_le_map_freeSituationGradedInv (U : X.Opens) :
    HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U))) ≤
      (HomogeneousIdeal.irrelevant ((freeSituation X n).sectionRingGrading U)).map
        (freeSituationGradedInv n U) :=
  irrelevant_le_map_of_graded_comp_eq_id (freeSituationGradedInv n U)
    (freeSituationGradedHom n U) (freeSituationGradedInv_comp_hom n U)

/-- The irrelevant ideal of the section ring is reached by the comparison. -/
theorem irrelevant_le_map_freeSituationGradedHom (U : X.Opens) :
    HomogeneousIdeal.irrelevant ((freeSituation X n).sectionRingGrading U) ≤
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U)))).map
          (freeSituationGradedHom n U) :=
  irrelevant_le_map_of_graded_comp_eq_id (freeSituationGradedHom n U)
    (freeSituationGradedInv n U) (freeSituationGradedHom_comp_inv n U)

/-- The comparison in degree zero, read in the section ring. -/
theorem coe_gradedZeroRingHom_freeSituationGradedInv (U : X.Opens)
    (a : (freeSituation X n).sectionRingGrading U 0) :
    (((freeSituationGradedInv n U).gradedZeroRingHom a :
        MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U)) 0) :
      MvPolynomial (coordIndex n) ↥(siteRing X (op U))) =
      (freeSituationSectionsRingEquiv n U).symm
        (a : (freeSituation X n).sectionRing U) := rfl

/-- The inverse comparison in degree zero, read in the polynomial ring. -/
theorem coe_freeSituationGradedHom_zero (U : X.Opens)
    (z : MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U)) 0) :
    ((freeSituationGradedHom n U (z : MvPolynomial (coordIndex n) ↥(siteRing X (op U)))) :
        (freeSituation X n).sectionRing U) =
      freeSituationSectionsRingEquiv n U
        (z : MvPolynomial (coordIndex n) ↥(siteRing X (op U))) := rfl

/-- **The comparison is bijective in degree zero.** -/
theorem bijective_gradedZeroRingHom_freeSituationGradedInv (U : X.Opens) :
    Function.Bijective (freeSituationGradedInv n U).gradedZeroRingHom := by
  refine ⟨fun a b hab => Subtype.ext ?_, fun z => ?_⟩
  · refine (freeSituationSectionsRingEquiv n U).symm.injective ?_
    rw [← coe_gradedZeroRingHom_freeSituationGradedInv n U a,
      ← coe_gradedZeroRingHom_freeSituationGradedInv n U b, hab]
  · refine ⟨⟨freeSituationGradedHom n U (z : MvPolynomial (coordIndex n) ↥(siteRing X (op U))),
      (freeSituationGradedHom n U).map_mem z.2⟩, Subtype.ext ?_⟩
    exact (freeSituationSectionsRingEquiv n U).symm_apply_apply
      (z : MvPolynomial (coordIndex n) ↥(siteRing X (op U)))

/-- Flatness is local on the target. -/
private instance isZariskiLocalAtTarget_flat : IsZariskiLocalAtTarget @Flat :=
  HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat)

/-- **The chart over an open is flat over `Spec` of its degree-zero part.** -/
theorem flat_toSpecZero_freeSituationGrading (U : X.Opens) :
    Flat (Proj.toSpecZero ((freeSituation X n).sectionRingGrading U)) := by
  have := isZariskiLocalAtTarget_flat.toRespects
  have hf := irrelevant_le_map_freeSituationGradedInv n U
  have hg := irrelevant_le_map_freeSituationGradedHom n U
  have hiso : IsIso (Proj.map (freeSituationGradedInv n U) hf) :=
    Proj.isIso_map hf hg (freeSituationGradedHom_comp_inv n U)
      (freeSituationGradedInv_comp_hom n U)
  have hz : IsIso (CommRingCat.ofHom (freeSituationGradedInv n U).gradedZeroRingHom) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_gradedZeroRingHom_freeSituationGradedInv n U
  have key : Flat (Proj.map (freeSituationGradedInv n U) hf ≫
      Proj.toSpecZero ((freeSituation X n).sectionRingGrading U)) := by
    rw [Proj.map_toSpecZero]
    exact (MorphismProperty.cancel_right_of_respectsIso (P := @Flat) _ _).mpr
      (Proj.flat_toSpecZero_mvPolynomial ↥(siteRing X (op U)) (coordIndex n))
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @Flat) _ _).mp key

/-! ### Flatness of the projection -/

/-- **The structure morphism of the relative `Proj` of `Sym(𝒪_X^{n+1})` is flat.** -/
theorem flat_relativeProjToBase_freeSituation :
    Flat (RelativeProj.Situation.relativeProjToBase (freeSituation X n)) := by
  exact (RelativeProj.Situation.chartData (freeSituation X n)).prop_toBase_of_toSpecZero @Flat
    (fun U => isIso_sectionRingZeroMap_freeSituation n U.1)
    (fun U => flat_toSpecZero_freeSituationGrading n U.1)

/-- **The projection of the projective bundle of `𝒪_X^{n+1}` is flat**, for the relative-`Proj`
situation presentation of the bundle. -/
theorem flat_projectiveBundleToBase_freeModule :
    Flat (RelativeProj.projectiveBundleToBase X (freeModule (X := X) (coordIndex n))) :=
  flat_relativeProjToBase_freeSituation n

end Stacks.SymGraded

end
