module

public import Mathlib.CategoryTheory.Shift.CommShiftTwo
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaInvertible.Abstract
public import StacksFrontier.CategoryTheory.Shift.TensorRightOfShiftedUnit

/-!
# Tensoring on the right by a shifted unit, along a functor

For a bifunctor `T : C ⥤ C ⥤ C` commuting with the shift by `ℤ` in both variables, a functor
`G : D ⥤ C` and an object `U` with `G ⋙ (- ⊗ U) ≅ G`, the functor `G ⋙ (- ⊗ U⟦m⟧)` is
isomorphic to `G ⋙ ⟦m⟧`.

## Main definitions

* `CategoryTheory.Functor.whiskerLeftFlipObjShiftIsoOfUnitor`: the isomorphism
  `G ⋙ (- ⊗ U⟦m⟧) ≅ G ⋙ ⟦m⟧` induced by an isomorphism `G ⋙ (- ⊗ U) ≅ G`.
-/

@[expose] public noncomputable section

open scoped CategoryTheory.Prod

namespace CategoryTheory.Functor

universe v u

variable {C : Type u} [Category.{v} C] (T : C ⥤ C ⥤ C)

variable [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [T.CommShift₂Int]

/-- If `G ⋙ (- ⊗ U)` is isomorphic to `G` by `ρ`, then `G ⋙ (- ⊗ U⟦m⟧) ≅ G ⋙ ⟦m⟧`: the
component at `M` is the commutation of `G M ⊗ -` with the shift by `m`, read at `U`, followed by
the shift of `ρ` at `M`. -/
def whiskerLeftFlipObjShiftIsoOfUnitor {D : Type*} [Category D] (G : D ⥤ C) (U : C)
    (ρ : G ⋙ T.flip.obj U ≅ G) (m : ℤ) :
    G ⋙ T.flip.obj (U⟦m⟧) ≅ G ⋙ shiftFunctor C m :=
  NatIso.ofComponents
    (fun M => ((T.obj (G.obj M)).commShiftIso m).app U ≪≫ (shiftFunctor C m).mapIso (ρ.app M))
    (fun {M M'} g => by
      dsimp
      simp only [Category.assoc]
      rw [← NatTrans.shift_app_comm_assoc, ← Functor.map_comp, ← Functor.map_comp]
      congr 2
      simpa using ρ.hom.naturality g)

end CategoryTheory.Functor

end
