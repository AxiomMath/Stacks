module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSectionsTower
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSectionsLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceTowerConjugate

/-!
# Inputs to the tower step of Situation 0DIK for `RΓ(X, E ⊗^L -)`

Pieces of the tower step of `DerivedExistenceSectionsTower` at the data of Situation 0DIK (the
squares `Xₙ₊₁ → X`, `Xₙ → Xₙ₊₁`, `Xₙ → X` over `Spec Aₙ₊₁ → Spec A`, `Spec Aₙ → Spec Aₙ₊₁`,
`Spec Aₙ → Spec A`): the composition of the ring maps, and the middle factor of `towerMap_eq` in
the small étale spelling.

## Main results

* `AlgebraicGeometry.Space.DerivedExistenceSystem.stageRingHom_comp`.
* `AlgebraicGeometry.Space.DerivedExistenceSystem.stageToposDerivedPushforward_map_homEquiv_eq`:
  the middle factor of `towerMap_eq` in the small étale spelling.

## References

* [Stacks Project, Tag 0DIM](https://stacks.math.columbia.edu/tag/0DIM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Functor
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard

namespace DerivedExistenceSystem

variable (D : DerivedExistenceSystem.{u})

/-- The ring maps `A → Aₙ₊₁ → Aₙ` compose to `A → Aₙ`. -/
theorem stageRingHom_comp (n : ℕ) :
    (representedAffineCommRingCatHom D.B (limitBase D.system) D.containsLimitBase
        (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)).hom =
      (representedAffineCommRingCatHom D.B (limitBase D.system) D.containsLimitBase
          (baseObjectTransition D.system D.B D.containsLimitBase D.containsBaseAt n)).hom.comp
        (representedAffineCommRingCatHom D.B (limitBase D.system) D.containsLimitBase
          (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt
            (n + 1))).hom := by
  rw [← representedAffineRingHom_comp, baseObjectTransition_baseObjectProjection]

include D in
/-- **The transposed `φₙ` pushed forward, in two spellings**: the ringed-topos
`Rjₙ₊₁,*` of the adjoint `Kₙ₊₁ ⟶ Riₙ,* Kₙ` of `φₙ` is `smallEtaleToposPushforward` of its adjoint
under `smallEtaleDerivedModuleAdjunction` (one morphism in two spellings, by `rfl`). -/
theorem stageToposDerivedPushforward_map_homEquiv_eq (n : ℕ) :
    (D.stageToposDerivedPushforward (n + 1)).map
        ((transitionToposDerivedAdjunction D.system D.B D.containsLimitBase D.containsBaseAt D.X
          n).homEquiv _ _ (D.φ n)) =
      (smallEtaleToposPushforward D.B (limitBase D.system) D.containsLimitBase
          (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1))).map
        ((smallEtaleDerivedModuleAdjunction D.B (limitBase D.system) D.containsLimitBase
            (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).homEquiv
          (D.K (n + 1)) (D.K n) (D.φ n)) :=
  rfl

end DerivedExistenceSystem

end AlgebraicGeometry.Space

end
