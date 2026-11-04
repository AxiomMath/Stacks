module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjClosedSubspaceFibre
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.TwistKerBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.DegreeSandwichPresentation

/-!
# The equations of a closed subspace of the constructed relative Proj, on the fibres

Let `π : P = Proj_X(𝒜) ⟶ X` be the relative homogeneous spectrum of Situation 0849 constructed in
Stacks 084A–084B and `i : Z ⟶ P` a closed immersion.  Over a scheme point `f : T ⟶ X` the closed
subscheme `Z_T ⊆ Proj_T(f^*𝒜)` of
`AlgebraicGeometry.Space.RelativeProjSituation.fibreClosedImmersion` has its graded ideal of
equations (Tag 0801).  This file records how the fibres of `Z` over two scheme points `f` and
`f ∘ τ` compare: the closed subscheme over `f ∘ τ` is the base change of the one over `f` along
the comparison morphism of Stacks 084B (3), which is the restriction identification followed by
the base-change morphism of Tag 01O3.  These are the squares along which the equations of `Z`
are transported by
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.mem_span_of_twistEquationSection_eq_zero` and
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.twistEquationSection_eq_zero_of_cover`, the
input for the quasi-coherence of the graded ideal `ℐ ⊆ 𝒜` of Stacks 085L.  It also records the
chart case of Stacks 0803 in the form the proof of Stacks 085N consumes it.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.toScheme_map_projComparison`: the comparison
  morphism of Stacks 084B (3) on schemes, in the form the transport of equations consumes.
* `AlgebraicGeometry.Space.RelativeProjSituation.exists_isPullback_fibreClosedImmersion`: **the
  closed subscheme over `f ∘ τ` is the base change of the one over `f`** along that comparison.
* `AlgebraicGeometry.Space.RelativeProjSituation.exists_chart_finiteType_cutsOut_supp`: the chart
  case of Stacks 0803 from the hypotheses of Stacks 085N, with the submodule recorded as cutting
  the fibre of `Z` out on the charts of Tag 0801's presentation, so that every quasi-coherent
  submodule between it and the graded ideal of the fibre presents the fibre
  (`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.degreeQuotientPresentation_of_le_twistKer`).

## References

* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 085L](https://stacks.math.columbia.edu/tag/085L)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

universe u

namespace AlgebraicGeometry.Space.RelativeProjSituation

variable (s : RelativeProjSituation.{u, u})
    {Z : (BigFppfOver s.site s.base s.containsBase)ᵒᵖ ⥤ Type u} {i : Z ⟶ s.relativeProjFunctor}
    (hi : IsClosedImmersion s.site s.base s.containsBase i)

/-- **The comparison morphism of Stacks 084B (3) on schemes**: along `τ : T' ⟶ T`, the
morphism `Proj_{T'}((f ∘ τ)^*𝒜) ⟶ Proj_T(f^*𝒜)` is the identification of the two restrictions
by the restriction datum of Stacks 084A followed by the base-change morphism of Tag 01O3. -/
theorem toScheme_map_projComparison {T T' : BigFppfOver s.site s.base s.containsBase}
    (f : yoneda.obj T ⟶ s.space.1) (τ : T' ⟶ T) :
    (BigFppfOver.toScheme s.site s.base s.containsBase).map
        (s.quadrupleRestriction.projComparison s.shrink.contains_relativeProj_pointAlgebra f τ) =
      (s.quadrupleRestriction.restrictProjIso f τ).hom ≫
        baseChangeHom (s.shrink.pointAlgebra T f)
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map τ) :=
  (s.isPullback_projComparison f τ).2.2

/-- **The closed subscheme over `f ∘ τ` is the base change of the one over `f`.**  Along the
comparison morphism of Stacks 084B (3), `Z_{T'} ⊆ Proj_{T'}((f ∘ τ)^*𝒜)` is the pullback of
`Z_T ⊆ Proj_T(f^*𝒜)`: both are base changes of `i`, and the comparison exhibits the fibre over
`f ∘ τ` as a base change of the fibre over `f`. -/
theorem exists_isPullback_fibreClosedImmersion {T T' : BigFppfOver s.site s.base s.containsBase}
    (f : yoneda.obj T ⟶ s.space.1) (τ : T' ⟶ T) :
    ∃ z : (BigFppfOver.toScheme s.site s.base s.containsBase).obj
        (s.fibreClosedSubspace hi T' (yoneda.map τ ≫ f)) ⟶
        (BigFppfOver.toScheme s.site s.base s.containsBase).obj (s.fibreClosedSubspace hi T f),
      IsPullback z (s.fibreClosedImmersion hi T' (yoneda.map τ ≫ f))
        (s.fibreClosedImmersion hi T f)
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map
          (s.quadrupleRestriction.projComparison s.shrink.contains_relativeProj_pointAlgebra f
            τ)) := by
  set pcS := s.quadrupleRestriction.projComparison s.shrink.contains_relativeProj_pointAlgebra f τ
  have hpcS : yoneda.map pcS ≫ s.relativeProjPoints.fibreToSpace T f =
      s.relativeProjPoints.fibreToSpace T' (yoneda.map τ ≫ f) :=
    (s.isPullback_projComparison f τ).2.1
  -- the square of presheaves
  have hbig : IsPullback (s.fibreClosedSubspaceToSpace hi T' (yoneda.map τ ≫ f))
      (yoneda.map (s.fibreClosedSubspaceHom hi T' (yoneda.map τ ≫ f))) i
      (yoneda.map pcS ≫ s.relativeProjPoints.fibreToSpace T f) := by
    have h := s.isPullback_fibreClosedSubspace hi T' (yoneda.map τ ≫ f)
    rwa [← hpcS] at h
  have hright := s.isPullback_fibreClosedSubspace hi T f
  obtain ⟨zS, hzS⟩ := yoneda.map_surjective (hright.lift
    (s.fibreClosedSubspaceToSpace hi T' (yoneda.map τ ≫ f))
    (yoneda.map (s.fibreClosedSubspaceHom hi T' (yoneda.map τ ≫ f)) ≫ yoneda.map pcS)
    (hbig.w.trans (Category.assoc _ _ _).symm))
  have hsite : IsPullback zS (s.fibreClosedSubspaceHom hi T' (yoneda.map τ ≫ f))
      (s.fibreClosedSubspaceHom hi T f) pcS :=
    IsPullback.of_map_of_faithful yoneda <| by
      rw [hzS]
      exact IsPullback.of_right' hbig.flip.flip hright
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme s.site s.base s.containsBase) :=
    comp_preservesLimitsOfShape _ _
  exact ⟨_, hsite.map (BigFppfOver.toScheme s.site s.base s.containsBase)⟩

attribute [local instance] pointTopology in
variable {T : BigFppfOver s.site s.base s.containsBase} {f : yoneda.obj T ⟶ s.space.1} in
include hi in
/-- **The chart case of Stacks 0803 from the hypotheses of Stacks 085N, with the cutting
property.**  As `exists_chart_finiteType_presentation_supp`, for an affine étale chart `f` of `X`
surjective on points (`Proj_T(f^*𝒜) ⟶ T` is quasi-compact when `π` is,
`quasiCompact_fibre_toBase`): a quasi-compact open `V` of the chart lying over `U` and covering
it, `d > 0` and a quasi-coherent finite type `ℱ' ⊆ (f^*𝒜)_d` with support of the quotient
disjoint from `V`, consisting of equations for the fibre `Z_T` and cutting it out on the charts of
Tag 0801's presentation. -/
theorem exists_chart_finiteType_cutsOut_supp
    (hT : _root_.AlgebraicGeometry.IsAffine
      ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T))
    (hf : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf f)
    (hsurj : Function.Surjective (pointsMap s.site s.base s.containsBase (yoneda.obj T) f))
    [QuasiCompact (relativeProj (s.shrink.pointAlgebra T f)).toBase]
    (hfp : IsFinitePresentation s.site s.base s.containsBase i)
    {U : Set (points s.site s.base s.containsBase s.space.1)}
    (hZU : Disjoint U (Set.range fun z ↦
      pointsMap s.site s.base s.containsBase s.relativeProjFunctor s.relativeProjπ
        (pointsMap s.site s.base s.containsBase Z i z)))
    (hU : IsOpen U) (hUc : IsCompact U)
    (hA : ∀ n : ℤ, SheafOfModules.IsFiniteType (s.algebra.piece n)) :
    ∃ V : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens,
      (∀ t ∈ V, pointsMap s.site s.base s.containsBase (yoneda.obj T) f
          ((schemePointsHomeomorph s.site s.base s.containsBase T).symm t) ∈ U) ∧
        U ⊆ (fun t ↦ pointsMap s.site s.base s.containsBase (yoneda.obj T) f
          ((schemePointsHomeomorph s.site s.base s.containsBase T).symm t)) '' V ∧
        ∃ d : ℕ, 0 < d ∧ ∃ ℱ : ((s.shrink.pointAlgebra T f).piece (d : ℤ)).Submodule,
          ℱ.toSheafOfModules.IsQuasicoherent ∧
            SheafOfModules.IsFiniteType.{u, u, u} ℱ.toSheafOfModules ∧
              (V : Set ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T)) ∩
                  (⟨(cokernel ℱ.ι).val, (cokernel ℱ.ι).isSheaf⟩ :
                    RingedSpace.ModuleSheaf.{u}
                      ((BigFppfOver.toScheme s.site s.base s.containsBase).obj
                        T).toRingedSpace).supp = ∅ ∧
                Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.IsEquationSubmodule
                  (s.shrink.pointAlgebra T f) ℱ
                  (Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.quotHom
                    (s.shrink.pointAlgebra T f)
                    (Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.twistKerGradedIdeal
                      (s.shrink.pointAlgebra T f)
                      (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
                      (s.fibreClosedImmersion hi T f))) ∧
                Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.CutsOutOnCharts
                  (s.shrink.pointAlgebra T f) ℱ
                  (Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.quotHom
                    (s.shrink.pointAlgebra T f)
                    (Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.twistKerGradedIdeal
                      (s.shrink.pointAlgebra T f)
                      (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
                      (s.fibreClosedImmersion hi T f))) := by
  obtain ⟨V, hVc, hVU, hUV⟩ := s.exists_isCompact_opens_image_cover T f hf hsurj hU hUc
  have _ : _root_.AlgebraicGeometry.IsAffine
      ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T) := hT
  exact ⟨V, hVU, hUV,
    Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.exists_finiteType_presentation_supp_cutsOut
      (s.shrink.pointAlgebra T f) (s.fibreClosedImmersion hi T f) V
      (s.finitePresentation_fibreClosedImmersion hi hf hfp)
      (s.inter_range_fibreClosedImmersion_eq_empty hi T f hZU hVU) hVc
      (fun n => s.isFiniteType_pointAlgebra_piece T f hA n)⟩

end AlgebraicGeometry.Space.RelativeProjSituation

end
