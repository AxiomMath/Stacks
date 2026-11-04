module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Action
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActions
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Free actions of group algebraic spaces and monomorphisms

An action of a group algebraic space `G` on an algebraic space `X` over a base `B` is free
when the induced action of `G(T)` on `X(T)` is free for every *scheme* `T` over `B`
(**Stacks 06P8**).  This file proves that freeness is equivalent to the morphism
`G ×_B X ⟶ X ×_B X`, `(g, x) ↦ (g · x, x)`, being a monomorphism.

## Main results

* `AlgebraicGeometry.Space.isCancelSMul_of_isFreeAction`: a free action is free on the points
  of *every* object of the slice over `B`, not only on the points of the schemes over `B`.
* `AlgebraicGeometry.Space.isFreeAction_iff_mono_leftSMul`: **Stacks 06P9**, an action is free
  exactly when the action–projection morphism `(g, x) ↦ (g · x, x)` is a monomorphism.

## Implementation notes

`AlgebraicGeometry.Space.IsFreeAction` tests freeness on the points of the schemes over `B`
only, as the source definition does, whereas the monomorphism condition is equivalent to
freeness on the points of every object of the slice of presheaves over `B` — that general
equivalence in a cartesian monoidal category is `AlgebraicGeometry.isFreeAction_iff_mono_leftSMul`
of `StacksFrontier/AlgebraicGeometry/GroupScheme/OverField/Action.lean`.  Passing between the two
tests is `AlgebraicGeometry.Space.isCancelSMul_of_isFreeAction`, and it is the only mathematical
content here: a pair of points of `G` over an arbitrary presheaf `T` over `B` that act alike on
a point of `X` agree, because they agree on each section of `T`, and a section of `T` over a
test object is a scheme over `B` together with a point of `G` and a point of `X` over it.  No
algebraicity of `B`, `G` or `X` is used, so the statement is made for arbitrary objects of the
slice.

## References

* [Stacks Project, Tag 06P8](https://stacks.math.columbia.edu/tag/06P8)
* [Stacks Project, Tag 06P9](https://stacks.math.columbia.edu/tag/06P9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}

/-- An action of a group algebraic space that is free on the points of every *scheme* over the
base is free on the points of every object of the slice over the base: freeness may be tested
on representables alone. -/
theorem isCancelSMul_of_isFreeAction {G X : Over B} [GrpObj G] [ModObj G X]
    (hfree : IsFreeAction 𝒞 S hS B G X) (T : Over B) :
    IsCancelSMul (T ⟶ G) (T ⟶ X) := by
  refine ⟨fun m n x hmn => ?_⟩
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  ext Y z
  let p : yoneda.obj Y.unop ⟶ T.left := yonedaEquiv.symm z
  let b : yoneda.obj Y.unop ⟶ B := p ≫ T.hom
  let q : Over.mk b ⟶ T := Over.homMk p
  have hsmul : (q ≫ m) • (q ≫ x) = (q ≫ n) • (q ≫ x) := by
    simpa only [CategoryTheory.ModObj.comp_smul] using
      congrArg (fun f : T ⟶ X => q ≫ f) hmn
  have hp : p ≫ m.left = p ≫ n.left :=
    congrArg CategoryTheory.Over.Hom.left ((hfree Y.unop b).right_cancel _ _ _ hsmul)
  have hval := congrArg yonedaEquiv hp
  rw [CategoryTheory.yonedaEquiv_comp, CategoryTheory.yonedaEquiv_comp] at hval
  simpa [p] using hval

/-- **Stacks 06P9.** An action of a group algebraic space is free exactly when the
action–projection morphism `G ×_B X ⟶ X ×_B X`, `(g, x) ↦ (g · x, x)`, is a monomorphism. -/
@[stacks 06P9, sga "3 IV 3.2.1" "(i), special case"]
theorem isFreeAction_iff_mono_leftSMul (G X : Over B) [GrpObj G] [ModObj G X] :
    IsFreeAction 𝒞 S hS B G X ↔ Mono (ModObj.leftSMul G X) :=
  ⟨fun hfree => (_root_.AlgebraicGeometry.isFreeAction_iff_mono_leftSMul G X).mp
      (isCancelSMul_of_isFreeAction hfree),
    fun hmono _ b =>
      (_root_.AlgebraicGeometry.isFreeAction_iff_mono_leftSMul G X).mpr hmono (Over.mk b)⟩

end AlgebraicGeometry.Space

end
