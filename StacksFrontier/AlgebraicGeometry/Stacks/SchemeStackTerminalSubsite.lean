module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfTerminalConstantSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSmoothObject
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack

/-!
# The flat-fppf site of the stack of a scheme has a terminal object

For a scheme `U`, the identity of `U` is a flat object of the fppf site of the stack of `U`, and
it is terminal there, as it is in `(Sch/U)` itself. Hence `Lg_! ℤ ⟶ ℤ` of Stacks 0H0Z is an
isomorphism for the stack of a scheme, with no further hypothesis.

## Main definitions

* `CategoryTheory.ObjectProperty.isTerminalFullSubcategory`: a terminal object satisfying `P` is
  terminal in the full subcategory cut out by `P`.
* `AlgebraicGeometry.Stack.isTerminalFlatObjectSchemeStackId`: the identity of `U` is terminal in
  the flat-fppf site of the stack of `U`.

## Main results

* `AlgebraicGeometry.Stack.flatObject_schemeStack_id`: the identity of `U` is a flat object of the
  fppf site of the stack of `U`.
* `FlatFppf.isIso_derivedAbelianLowerShriekAdjunction_counit_constantSheaf_schemeStack`:
  the counit of `Lg_! ⊣ g⁻¹` is invertible at the constant sheaf `ℤ`.

## References

* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
* [Stacks Project, Tag 0H0Z](https://stacks.math.columbia.edu/tag/0H0Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ObjectProperty

universe v u

/-- A terminal object of `C` satisfying `P` is terminal in the full subcategory cut out by `P`. -/
def isTerminalFullSubcategory {C : Type u} [Category.{v} C] (P : ObjectProperty C) {e : C}
    (he : IsTerminal e) (hPe : P e) : IsTerminal (⟨e, hPe⟩ : P.FullSubcategory) :=
  IsTerminal.ofUniqueHom (fun y ↦ homMk (he.from y.obj))
    (fun _ _ ↦ hom_ext _ (he.hom_ext _ _))

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- The identity of `U` is a flat object of the fppf site of the stack of `U`. -/
theorem flatObject_schemeStack_id :
    flatObject B S hS (schemeStack.{u, w} B S hS U).val (Over.mk (𝟙 U)) := by
  have hsm : smoothObject.{u, w} B S hS (schemeStack.{u, w} B S hS U) (Over.mk (𝟙 U)) := by
    rw [smoothObject_schemeStack_iff]
    show Smooth ((BigFppfOver.toScheme B S hS).map (𝟙 U))
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  exact (AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS _).1
    (AlgebraicStacks.isFlat_of_isSmooth B S hS _ hsm)

/-- The identity of `U` is a terminal object of the flat-fppf site of the stack of a scheme `U`. -/
def isTerminalFlatObjectSchemeStackId :
    IsTerminal (⟨Over.mk (𝟙 U), flatObject_schemeStack_id.{u, w} B S hS U⟩ :
      (FlatFppf.objectProperty B S hS (schemeStack.{u, w} B S hS U)).FullSubcategory) :=
  (FlatFppf.objectProperty B S hS (schemeStack.{u, w} B S hS U)).isTerminalFullSubcategory
    Over.mkIdTerminal _

namespace FlatFppf

section Derived

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

/-- For the stack of a scheme `U`, the counit of the derived adjunction `Lg_! ⊣ g⁻¹` is invertible
at the constant sheaf `ℤ` of `(Sch/U)_{fppf}` in degree zero, so the canonical comparison
`Lg_! ℤ ⟶ ℤ` is an isomorphism. -/
@[stacks 0H0Z "for the `Lg_!` of 07AS part (3), the flat-fppf site of the stack of a scheme"]
theorem isIso_derivedAbelianLowerShriekAdjunction_counit_constantSheaf_schemeStack :
    IsIso ((derivedAbelianLowerShriekAdjunction B S hS (schemeStack.{u, w} B S hS U)
          (abelianLowerShriekAcyclic B S hS (schemeStack.{u, w} B S hS U))).counit.app
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (fppfTopology B S hS (schemeStack.{u, w} B S hS U))
            AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))))) :=
  isIso_derivedAbelianLowerShriekAdjunction_counit_constantSheaf_of_isTerminal B S hS
    (schemeStack.{u, w} B S hS U) (isTerminalFlatObjectSchemeStackId.{u, w} B S hS U)
    Over.mkIdTerminal

end Derived

end FlatFppf

end AlgebraicGeometry.Stack

end
