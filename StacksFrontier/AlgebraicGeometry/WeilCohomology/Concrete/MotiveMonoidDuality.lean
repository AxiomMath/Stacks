module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GraphFundamentalPairing
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotiveDuality
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotiveMonoid
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiMonObjDuality
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The duality of a motive through its multiplication

Let `X` be a smooth projective scheme over a field `k`, equidimensional of dimension `d`. By
Stacks 0FGI the motive `h(X)` has `h(X)(d) = h(X) ⊗ 𝟏(d)` as a left dual, with unit and counit the
class `[Δ]` of the diagonal. In the proof of Stacks 0FH1 it is observed that the counit is the
composite of the multiplication `[Γ_Δ] : h(X) ⊗ h(X) ⟶ h(X)` with the fundamental class
`[X] : h(X) ⊗ 𝟏(d) ⟶ 𝟏`; this identifies the induced pairing on a realization `G(h(X))` with
cup product followed by the trace.

## Main results

* `Stacks.WeilCohomology.dualityCounit_eq_diagonalGraphHom_comp`: in the category of
  correspondences, `ε = [Δ] = [X] ∘ [Γ_Δ]`, on cycles `x ↦ ((x, x), ⋆)`; in monoid form
  `Stacks.WeilCohomology.evaluation_correspondenceExactPairing`.
* `Stacks.WeilCohomology.ChowMotiveCat.exactPairingMotive`: `h(X) ⊗ 𝟏(d)` is a left dual of
  `h(X)`, with unit `[Δ]` (Stacks 0FGI).
* `Stacks.WeilCohomology.ChowMotiveCat.evaluation_exactPairingMotive`: the counit is
  `α ≫ (h(X) ◁ β) ≫ α⁻¹ ≫ (μ ▷ 𝟏(d)) ≫ [X]`, with `[X] : h(X) ⊗ 𝟏(d) ⟶ 𝟏` the fundamental class
  (`CategoryTheory.GradedCategory.TwistedKaroubi.unitTwistTrace`).

## References

* [Stacks Project, Tag 0FGI](https://stacks.math.columbia.edu/tag/0FGI)
* [Stacks Project, Tag 0FH1](https://stacks.math.columbia.edu/tag/0FH1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj Stacks.Chow

universe u

namespace Stacks.WeilCohomology

open CorrespondenceCategory ChowMotiveCat

variable {k : Type u} [Field k]

local notation "𝐏" => 𝟙_ (CategoryTheory.ObjectProperty.FullSubcategory (SmoothProjectiveScheme k))

local notation "𝐎" => (GradedCompositionData.Obj.mk :
  CategoryTheory.ObjectProperty.FullSubcategory (SmoothProjectiveScheme _) →
    CorrespondenceCategory _)

variable {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ}
  (hX : RelativeDimension X.obj.hom d)

/-- The diagonal `x ↦ ((x, x), ⋆)` of `(X × X) × Spec k` is the point pairing of the identity. -/
theorem counitDiagonal_eq_pointPairingMap :
    counitDiagonal X =
      pointPairingMap X.obj.hom X.obj.hom 𝐏.obj.hom (𝟙 _) (Category.id_comp _) := by
  simp only [counitDiagonal, pointPairingMap, graphMorphism, pullback.diagonal]
  congr 1
  simp

attribute [local instance] isClosedImmersion_counitDiagonal isClosedImmersion_pointPairingMap

include hX in
/-- **`ε = [X] ∘ [Γ_Δ]`**: the counit of the self-duality of `X` in the category of
correspondences (the class of the diagonal in `Corr^{-d}(X × X, Spec k)`) is the graph of the
diagonal `X ⟶ X × X` followed by the fundamental class `[X] ∈ Corr^{-d}(X, Spec k)`. -/
theorem dualityCounit_eq_diagonalGraphHom_comp :
    dualityCounit X hX = diagonalGraphHom X ≫ fundamentalClassHom hX := by
  have hXX : RelativeDimension (prodBase X.obj.hom X.obj.hom) (d + d) :=
    relativeDimension_prodBase k X.obj.hom X.obj.hom hX hX
  have key : correspondenceCongr k (X ⊗ X).obj.hom 𝐏.obj.hom
      (show -(d : ℤ) = (0 + 0) + 0 + -(d : ℤ) by ring)
      (corrEquivCorrespondence k (X ⊗ X).obj.hom 𝐏.obj.hom hXX relativeDimension_tensorUnit_hom
        (-(d : ℤ)) (SmoothProjectiveCorr.toCorr (X ⊗ X) 𝐏 _ (dualityCounitCorr X hX))) =
      corrEquivCorrespondence k (X ⊗ X).obj.hom 𝐏.obj.hom hXX relativeDimension_tensorUnit_hom
        ((0 + 0) + 0 + -(d : ℤ))
        (SmoothProjectiveCorr.toCorr (X ⊗ X) 𝐏 _ ((canonicalCorrespondenceCompositionData k).comp
          ((canonicalCorrespondenceCompositionData k).comp
            (tensorCorr 0 0 (graphCorrespondenceSP (𝟙 X)) (correspondenceDiagonal k X))
            (graphCorrespondenceSP (P := X ⊗ X) (SmoothProjectiveScheme.diag X)))
          (fundamentalClassCorr hX))) := by
    rw [corrEquivCorrespondence_topComposite hX hX hXX hXX (𝟙 X), dualityCounitCorr,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, correspondenceCongr_tmul,
      chowGroupDegreeEquiv_mk_cycleAssociatedToClosedSubscheme]
    congr 1
    · norm_num
    · exact congrArg QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _
        (Iso.refl _) ((Category.id_comp _).trans counitDiagonal_eq_pointPairingMap.symm) _)
  have h₁ : diagonalGraphHom X ≫ fundamentalClassHom hX =
      CorrespondenceCategory.tensorHom (graphHom (𝟙 X) : 𝐎 X ⟶ 𝐎 X) (𝟙 (𝐎 X)) ≫
        diagonalGraphHom X ≫ fundamentalClassHom hX := by
    rw [show (graphHom (𝟙 X) : 𝐎 X ⟶ 𝐎 X) = 𝟙 _ from graphHom_id X,
      CorrespondenceCategory.id_tensorHom_id, Category.id_comp]
  rw [h₁, GradedCompositionData.id_eq,
    show (canonicalCorrespondenceCompositionData k).diagonal X =
      correspondenceDiagonal k X from rfl,
    diagonalGraphHom, fundamentalClassHom, dualityCounit]
  simp only [graphHom]
  rw [tensorHom_of_of, ← Category.assoc, GradedCompositionData.of_comp_of,
    GradedCompositionData.of_comp_of]
  dsimp only
  exact of_eq_of_corrEquivCorrespondence hXX relativeDimension_tensorUnit_hom _ _ _ key

/-- The graph of the diagonal is the multiplication of the monoid `X` of correspondences. -/
theorem mul_eq_diagonalGraphHom (X : (SmoothProjectiveScheme k).FullSubcategory) :
    μ[𝐎 X] = diagonalGraphHom X :=
  rfl

/-- The fundamental class `[X] ∈ Corr^{-d}(X, Spec k)` has degree `-d`. -/
theorem fundamentalClassHom_mem_grade :
    fundamentalClassHom hX ∈ GradedCategory.grade (R := ℚ) _ _ (-(d : ℤ)) :=
  (GradedCompositionData.mem_grade_iff _).2 ⟨_, rfl⟩

section

/- The unit `𝟙_` of the category of correspondences is taken through
`MonoidalCategory.toMonoidalCategoryStruct`. -/
attribute [-instance] CorrespondenceCategory.monoidalCategoryStruct

include hX in
/-- **The counit of the self-duality of `X` is `[X] ∘ μ`**, for the multiplication `μ = [Γ_Δ]` of
the monoid `X` of correspondences. -/
theorem evaluation_correspondenceExactPairing :
    letI := correspondenceExactPairing X hX
    ε_ (𝐎 X) (𝐎 X) =
      @CategoryStruct.comp _ _ _ _ (𝟙_ _) μ[𝐎 X] (fundamentalClassHom hX) :=
  (dualityCounit_eq_diagonalGraphHom_comp hX).trans (by rw [mul_eq_diagonalGraphHom])

end

namespace ChowMotiveCat

open CategoryTheory.GradedCategory

/- The monoidal structure of `M_k` is taken through the generic instances in this section. -/
attribute [-instance] ChowMotiveCat.monoidalCategory ChowMotiveCat.braidedCategory
  ChowMotiveCat.symmetricCategory TwistedKaroubi.monoidalCategoryStruct
  CorrespondenceCategory.monoidalCategoryStruct TwistedKaroubi.symmetricCategory

/-- **Stacks 0FGI**, in the spelling `h(X) = (X, 1, 0)`: for `X` equidimensional of dimension
`d`, `h(X) ⊗ 𝟏(d)` is a left dual of `h(X)`, with unit `[Δ] : 𝟏 ⟶ h(X) ⊗ (h(X) ⊗ 𝟏(d))` and
counit `[Δ] : (h(X) ⊗ 𝟏(d)) ⊗ h(X) ⟶ 𝟏` (through `X × Spec k = X`). -/
@[instance_reducible]
def exactPairingMotive :=
  letI := correspondenceExactPairing X hX
  TwistedKaroubi.exactPairingOfObjTensorTwist (R := ℚ) (𝐎 X)
    (correspondenceExactPairing_coevaluation_mem_grade X hX)
    (correspondenceExactPairing_evaluation_mem_grade X hX)

/-- **The counit of `h(X) ⊗ 𝟏(d)` as a dual of `h(X)` is the multiplication followed by `[X]`**
(Stacks 0FH1, proof of (A)): `ε = α ≫ (h(X) ◁ β) ≫ α⁻¹ ≫ (μ ▷ 𝟏(d)) ≫ [X]`, where
`[X] : h(X) ⊗ 𝟏(d) ⟶ 𝟏` is the fundamental class `[X] ∈ Corr^{-d}(X, Spec k)`
(`TwistedKaroubi.unitTwistTrace`). -/
theorem evaluation_exactPairingMotive :
    letI := exactPairingMotive hX
    ε_ (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
        (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X) ⊗
          TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) =
      (α_ (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
          (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)
          (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))).hom ≫
        TwistedKaroubi.ofObj (R := ℚ) (𝐎 X) ◁
          (β_ (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)
            (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))).hom ≫
          (α_ (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X)) (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
            (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)).inv ≫
            μ ▷ TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d ≫
              TwistedKaroubi.unitTwistTrace (R := ℚ) (d : ℤ) (fundamentalClassHom hX)
                (fundamentalClassHom_mem_grade hX) :=
  let := correspondenceExactPairing X hX
  let := exactPairingMotive hX
  TwistedKaroubi.evaluation_eq_mul_comp (R := ℚ) (X := 𝐎 X) (d := d) μ[𝐎 X] (ε_ (𝐎 X) (𝐎 X))
    (TwistedKaroubi.exactPairingOfObjTensorTwist_evaluation_val (R := ℚ) (𝐎 X)
      (correspondenceExactPairing_coevaluation_mem_grade X hX)
      (correspondenceExactPairing_evaluation_mem_grade X hX))
    (mul_motive_val X) (fundamentalClassHom hX) (fundamentalClassHom_mem_grade hX)
    (evaluation_correspondenceExactPairing hX)

end ChowMotiveCat

end Stacks.WeilCohomology

end
