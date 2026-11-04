module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Duality
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CorrespondenceMonoidal
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Motives
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiDuality
public import StacksCore.Tactic.StacksAttribute

/-!
# The motive of a smooth projective scheme has a twisted left dual

Let `k` be a field and let `X` be a smooth projective scheme over `k` which is equidimensional of
dimension `d`. **Stacks 0FGI**: `h(X)(d)` is a left dual of `h(X)` in the category `M_k` of Chow
motives. In Mathlib's language (Categories, Definition 0FFP; Mathlib's `ExactPairing X Y`, which
Mathlib phrases as `HasRightDual X`) this is an exact pairing between `h(X)` and
`h(X)(d) = h(X) ⊗ 𝟏(d)`, with unit `η : 𝟏 ⟶ h(X) ⊗ h(X)(d)` and counit
`ε : h(X)(d) ⊗ h(X) ⟶ 𝟏`, both the class of the diagonal.

The proof is the source's. The two triangle identities are proved in the category of
correspondences in `StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Duality`, by computing
the composite of `[Δ] ⊗ 1` and `1 ⊗ [Δ]` as the class of the small diagonal. Since the unit has
degree `d` and the counit degree `-d`, the pairing lifts to `M_k` between `(X, 1, 0) = h(X)` and
`(X, 1, d)` (`CategoryTheory.GradedCategory.TwistedKaroubi.exactPairingOfObj`), and
`(X, 1, d) ≅ h(X) ⊗ 𝟏(d)`.

## Main definitions

* `Stacks.WeilCohomology.correspondenceExactPairing`: `X` is its own left dual in the category of
  correspondences, with `η = ε = [Δ]`.
* `Stacks.WeilCohomology.motiveExactPairingTwist`: `(X, 1, d)` is a left dual of `h(X)` in `M_k`.
* `Stacks.WeilCohomology.motiveExactPairing`: **Stacks 0FGI**, `h(X)(d) = h(X) ⊗ 𝟏(d)` is a left
  dual of `h(X)` in `M_k`.

## References

* [Stacks Project, Tag 0FGI](https://stacks.math.columbia.edu/tag/0FGI)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite CategoryTheory.GradedCategory

universe u

namespace Stacks.WeilCohomology

open CorrespondenceCategory

variable {k : Type u} [Field k] (X : (SmoothProjectiveScheme k).FullSubcategory) {d : ℕ}

/-- **The diagonal is a self-duality in the category of correspondences.** For `X` smooth
projective over `k` and equidimensional of dimension `d`, `X` is a left dual of itself in the
category of correspondences, with unit `η = [Δ] ∈ Corr^d(Spec k, X × X)` and counit
`ε = [Δ] ∈ Corr^{-d}(X × X, Spec k)`; the two triangle identities are
`Stacks.WeilCohomology.tensorHom_dualityUnit_associator_tensorHom_dualityCounit` and
`Stacks.WeilCohomology.dualityUnit_tensorHom_associator_tensorHom_dualityCounit`. -/
@[instance_reducible]
def correspondenceExactPairing (hX : RelativeDimension X.obj.hom d) :
    ExactPairing (GradedCompositionData.Obj.mk X : CorrespondenceCategory k)
      (GradedCompositionData.Obj.mk X) := by
  refine ExactPairing.mk (dualityUnit X hX) (dualityCounit X hX) ?_ ?_
  · rw [rightUnitor_eq, leftUnitor_eq, whiskerLeft_eq, whiskerRight_eq, associator_eq]
    simp only [tensorObj_eq, tensorUnit_eq]
    exact tensorHom_dualityUnit_associator_tensorHom_dualityCounit X hX
  · rw [rightUnitor_eq, leftUnitor_eq, whiskerLeft_eq, whiskerRight_eq, associator_eq]
    simp only [tensorObj_eq, tensorUnit_eq]
    exact dualityUnit_tensorHom_associator_tensorHom_dualityCounit X hX

/-- The unit of `Stacks.WeilCohomology.correspondenceExactPairing` has degree `d`. -/
theorem correspondenceExactPairing_coevaluation_mem_grade (hX : RelativeDimension X.obj.hom d) :
    @ExactPairing.coevaluation _ _ _ _ _ (correspondenceExactPairing X hX) ∈
      GradedCategory.grade (R := ℚ) _ _ (d : ℤ) := by
  simp only [tensorObj_eq, tensorUnit_eq]
  exact dualityUnit_mem_grade X hX

/-- The counit of `Stacks.WeilCohomology.correspondenceExactPairing` has degree `-d`. -/
theorem correspondenceExactPairing_evaluation_mem_grade (hX : RelativeDimension X.obj.hom d) :
    @ExactPairing.evaluation _ _ _ _ _ (correspondenceExactPairing X hX) ∈
      GradedCategory.grade (R := ℚ) _ _ (-(d : ℤ)) := by
  simp only [tensorObj_eq, tensorUnit_eq]
  exact dualityCounit_mem_grade X hX

/-- In `M_k`, the triple `(X, 1, d)` is a left dual of `h(X) = (X, 1, 0)`, with unit and counit
the class of the diagonal. -/
@[instance_reducible]
def motiveExactPairingTwist (hX : RelativeDimension X.obj.hom d) :
    ExactPairing
      ({ TwistedKaroubi.ofObj (R := ℚ)
          (GradedCompositionData.Obj.mk X : CorrespondenceCategory k) with twist := 0 } :
        ChowMotiveCat k)
      { TwistedKaroubi.ofObj (R := ℚ) (GradedCompositionData.Obj.mk X : CorrespondenceCategory k)
          with twist := (d : ℤ) - 0 } :=
  @TwistedKaroubi.exactPairingOfObj ℚ _ _ _ _ _ _ _ (GradedCompositionData.Obj.mk X)
    (GradedCompositionData.Obj.mk X) (correspondenceExactPairing X hX) (d : ℤ)
    (correspondenceExactPairing_coevaluation_mem_grade X hX)
    (correspondenceExactPairing_evaluation_mem_grade X hX) 0

/-- **Stacks Project, Tag 0FGI.** Let `X` be a smooth projective scheme over `k` which is
equidimensional of dimension `d`. Then `h(X)(d) = h(X) ⊗ 𝟏(d)` is a left dual of `h(X)` in the
category `M_k` of Chow motives: there are `η : 𝟏 ⟶ h(X) ⊗ h(X)(d)` and
`ε : h(X)(d) ⊗ h(X) ⟶ 𝟏`, both the class `[Δ]` of the diagonal, satisfying the two triangle
identities (Categories, Definition 0FFP; Mathlib's `ExactPairing`). Equidimensionality of
dimension `d` is `RelativeDimension X.obj.hom d`; `X` may be empty. -/
@[stacks 0FGI, instance_reducible]
def motiveExactPairing (hX : RelativeDimension X.obj.hom d) :
    ExactPairing ((ChowMotiveCat.h k).obj (op X))
      ((ChowMotiveCat.h k).obj (op X) ⊗ ChowMotiveCat.tate k d) :=
  @exactPairingCongrRight _ _ _ _ _ _ (motiveExactPairingTwist X hX)
    (TwistedKaroubi.tensorUnitTwistIso ((ChowMotiveCat.h k).obj (op X)) (d : ℤ) ≪≫
      TwistedKaroubi.twistCongrIso ((ChowMotiveCat.h k).obj (op X))
        (show (0 : ℤ) + (d : ℤ) = (d : ℤ) - 0 by ring))

/-- **Stacks 0FGI**, as a statement: `h(X)` has `h(X)(d)` as a left dual in `M_k`. -/
@[stacks 0FGI]
theorem nonempty_exactPairing_motive (hX : RelativeDimension X.obj.hom d) :
    Nonempty (ExactPairing ((ChowMotiveCat.h k).obj (op X))
      ((ChowMotiveCat.h k).obj (op X) ⊗ ChowMotiveCat.tate k d)) :=
  ⟨motiveExactPairing X hX⟩

end Stacks.WeilCohomology

end
