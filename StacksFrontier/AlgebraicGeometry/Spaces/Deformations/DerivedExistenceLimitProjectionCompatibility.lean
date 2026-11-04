module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceBoundedLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction

/-!
# Compatibility of the maps `τₙ` of Situation 0DIK with the transition maps

In Situation [Stacks, Tag 0DIK], with `K = DQ_X(R lim Kₙ)` and `τₙ : Ljₙ^* K ⟶ Kₙ` the adjoint of
the projection `K ⟶ Rjₙ,* Kₙ`, the maps `τₙ` are compatible with the `φₙ`:

`τₙ = (Ljₙ^* ≅ Liₙ^* Ljₙ₊₁^*) ≫ Liₙ^* τₙ₊₁ ≫ φₙ`.

This holds for any isomorphism `e : Ljₙ₊₁^* ⋙ Liₙ^* ≅ Ljₙ^*` that is conjugate, along
`Ljₙ^* ⊣ Rjₙ,*` and the composite `Ljₙ₊₁^* ⋙ Liₙ^* ⊣ Riₙ,* ⋙ Rjₙ₊₁,*`, to the composition
isomorphism `Riₙ,* ⋙ Rjₙ₊₁,* ≅ Rjₙ,*` of the tower. It is a formal consequence of the
definition of the tower.

## Main results

* `AlgebraicGeometry.Space.homEquiv_symm_comp_conjugateEquiv_app`: for conjugate `α` and `β`,
  `adj₂.homEquiv.symm (f ≫ β) = α ≫ adj₁.homEquiv.symm f`.
* `AlgebraicGeometry.Space.DerivedExistenceSystem.stageAdjoint_comp_towerMap`: the adjoint of
  `f ≫ (Eₙ₊₁ ⟶ Eₙ)` in terms of the adjoint of `f`.
* `AlgebraicGeometry.Space.DerivedExistenceSystem.coheratorLimitPullbackMap_eq`: the compatibility
  of the `τₙ`.

## References

* [Stacks Project, Tag 0DIL](https://stacks.math.columbia.edu/tag/0DIL)
* [Stacks Project, Tag 0DIM](https://stacks.math.columbia.edu/tag/0DIM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GrothendieckExistence (limitBase)

universe u

namespace AlgebraicGeometry.Space

/-- For `α : L₂ ⟶ L₁` conjugate to `β : R₁ ⟶ R₂`, the adjoint along `adj₂` of `f ≫ β` is `α`
followed by the adjoint of `f` along `adj₁`. -/
theorem homEquiv_symm_comp_conjugateEquiv_app {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    {X : C} {Y : D} (f : X ⟶ R₁.obj Y) :
    (adj₂.homEquiv _ _).symm (f ≫ (conjugateEquiv adj₁ adj₂ α).app Y) =
      α.app X ≫ (adj₁.homEquiv _ _).symm f := by
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    conjugateEquiv_counit, ← Category.assoc, α.naturality, Category.assoc]

namespace DerivedExistenceSystem

variable (D : DerivedExistenceSystem.{u})

/-- The composition isomorphism `Ljₙ₊₁^* ⋙ Liₙ^* ≅ Ljₙ^*` (Stacks 0D6D), read through
`iₙ ≫ jₙ₊₁ = jₙ`. -/
def stageDerivedPullbackCompIso (n : ℕ) :
    D.stageDerivedPullback (n + 1) ⋙
        transitionDerivedPullback D.system D.B D.containsLimitBase D.containsBaseAt D.X n ≅
      D.stageDerivedPullback n :=
  smallEtaleDerivedModulePullbackCompIso D.B (limitBase D.system) D.containsLimitBase
      (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1)) ≪≫
    smallEtaleDerivedModulePullbackCongr D.B (limitBase D.system) D.containsLimitBase
      (transitionSpace_spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)

variable {D} in
/-- **The adjoint of `f ≫ (Eₙ₊₁ ⟶ Eₙ)`.** For `e : Ljₙ₊₁^* ⋙ Liₙ^* ≅ Ljₙ^*` conjugate to the
composition isomorphism of the tower, the adjoint of `f ≫ towerMap n` is
`e⁻¹ ≫ Liₙ^*(adjoint of f) ≫ φₙ`. -/
theorem stageAdjoint_comp_towerMap (n : ℕ)
    (e : D.stageDerivedPullback (n + 1) ⋙
        transitionDerivedPullback D.system D.B D.containsLimitBase D.containsBaseAt D.X n ≅
      D.stageDerivedPullback n)
    (he : conjugateEquiv (D.stageAdjunction n)
      ((D.stageAdjunction (n + 1)).comp (D.transitionAdjunction n)) e.hom =
        (D.stagePushforwardCompIso n).inv)
    {E : D.limitDerivedCategory} (f : E ⟶ D.towerObj (n + 1)) :
    D.stageAdjoint n (f ≫ D.towerMap n) =
      e.inv.app E ≫
        (transitionDerivedPullback D.system D.B D.containsLimitBase D.containsBaseAt D.X n).map
          (D.stageAdjoint (n + 1) f) ≫ D.φ n := by
  have key := homEquiv_symm_comp_conjugateEquiv_app (D.stageAdjunction n)
    ((D.stageAdjunction (n + 1)).comp (D.transitionAdjunction n)) e.hom
    (f ≫ D.towerMap n)
  rw [he] at key
  have h1 : f ≫ D.towerMap n ≫ (D.stagePushforwardCompIso n).inv.app (D.K n) =
      f ≫ (D.stagePushforward (n + 1)).map ((D.transitionAdjunction n).homEquiv _ _ (D.φ n)) := by
    simp [towerMap]
  rw [Category.assoc, h1, Adjunction.comp_homEquiv, Equiv.symm_trans_apply,
    Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_naturality_left_symm,
    Equiv.symm_apply_apply] at key
  simp only [stageAdjoint]
  rw [← Iso.inv_hom_id_app_assoc e E ((D.stageAdjunction n).homEquiv _ _ |>.symm _), ← key]

section Coherator

variable (DQ : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left ⥤
    (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).FullSubcategory)
  (adj : (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι ⊣ DQ)

/-- **The compatibility of the `τₙ`**: `τₙ = e⁻¹ ≫ Liₙ^* τₙ₊₁ ≫ φₙ` for any
`e : Ljₙ₊₁^* ⋙ Liₙ^* ≅ Ljₙ^*` conjugate to the composition isomorphism of the tower. -/
theorem coheratorLimitPullbackMap_eq (n : ℕ)
    (e : D.stageDerivedPullback (n + 1) ⋙
        transitionDerivedPullback D.system D.B D.containsLimitBase D.containsBaseAt D.X n ≅
      D.stageDerivedPullback n)
    (he : conjugateEquiv (D.stageAdjunction n)
      ((D.stageAdjunction (n + 1)).comp (D.transitionAdjunction n)) e.hom =
        (D.stagePushforwardCompIso n).inv) :
    D.coheratorLimitPullbackMap DQ adj n =
      e.inv.app _ ≫
        (transitionDerivedPullback D.system D.B D.containsLimitBase D.containsBaseAt D.X n).map
          (D.coheratorLimitPullbackMap DQ adj (n + 1)) ≫ D.φ n := by
  have h := D.coheratorLimitProjection_comp_map DQ adj n
  rw [show D.spaceTower.map (homOfLE (Nat.le_succ n)).op = D.towerMap n from
    D.pushforwardTower_map_succ n] at h
  simp only [coheratorLimitPullbackMap]
  rw [← h]
  exact stageAdjoint_comp_towerMap n e he _

end Coherator

end DerivedExistenceSystem

end AlgebraicGeometry.Space

end
