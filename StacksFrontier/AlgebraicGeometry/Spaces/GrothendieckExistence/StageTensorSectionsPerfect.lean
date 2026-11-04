module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.StageTensorSectionsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceDerivedCategoryPerfect

/-!
# Perfectness of `RΓ(Xₙ, E|_{Xₙ} ⊗^𝐋 Fₙ)` in Situation 0CX4

In Situation [Stacks, Tag 0CX4], for a perfect object `E` of `D(𝒪_X)` the object
`Mₙ = RΓ(Xₙ, Liₙ^*E ⊗^𝐋 Fₙ)` of `D(Aₙ)` is perfect: `Liₙ^*E` is perfect, `Fₙ` is of finite
presentation, flat over `Aₙ` with support proper over `Aₙ`, so `Rfₙ,*(Liₙ^*E ⊗^𝐋 Fₙ)` is perfect
on `Spec Aₙ` ([Stacks, Tag 0A1P]), and the derived sections of a perfect object on an affine
scheme are perfect.

## Main results

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.ringIsPerfect_stageTensorSectionsTarget`:
  `Mₙ` is perfect.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u}) (n : ℕ)
  (E : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)

/-- **`RΓ(Xₙ, Liₙ^*E ⊗^𝐋 Fₙ)` is perfect** for a perfect `E`: Stacks 0A1P for the structure
morphism `Xₙ ⟶ Spec Aₙ`, then the derived sections over the affine `Spec Aₙ`. -/
theorem ringIsPerfect_stageTensorSectionsTarget
    (hE : spaceIsPerfect D.B D.S D.containsLimitBase D.X.left E) :
    StacksDraft.ringIsPerfect (D.stageTensorSectionsTarget n E) := by
  have hEn := isPerfect_smallEtaleDerivedModulePullback (D.closedImmersion n) E hE
  have hY := isPerfect_derivedModulePushforward_derivedTensor_single (D.stageToBase n)
    (isFinitePresentation_spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt
      D.X D.finitePresentation n)
    _ hEn (D.F n)
    (SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite' (D.F n)
      (D.finitelyPresented n))
    (D.flat n) (D.properSupport n)
  exact isPerfect_representedAffineDerivedSections_obj D.B D.S D.containsLimitBase
    (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n) _ hY

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space
