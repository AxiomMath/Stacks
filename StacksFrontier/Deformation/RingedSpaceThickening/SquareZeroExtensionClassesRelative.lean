module

public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionFromPushout
public import StacksFrontier.Deformation.RingedSpaceThickening.SquareZeroExtensionClasses
import StacksCore.Tactic.StacksAttribute

/-!
# The bijection of Stacks 0GPZ in the group of the tag

`AlgebraicGeometry.RingedSpaceThickening.classesEquivExt` of
`StacksFrontier.Deformation.RingedSpaceThickening.SquareZeroExtensionClasses` is on the
thickening-based encoding `DeformationSolution (𝟙 S) ht f G 0` and takes the four conditions of
`AlgebraicGeometry.RingedSpaceThickening.SolutionObstruction` as inputs, the acting group being
the `Ext¹` of an arbitrary two-term complex fixed before the cocycle.

`AlgebraicGeometry.RingedSpaceThickening.classesEquivExtRelative` is the tag, unconditionally. It
is on `AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension`, the object
**Stacks 0GPZ** counts — an extension `0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_S`-algebras — and the
acting group is `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` itself. What makes the four conditions go away is the
order of the binders: no presentation is fixed, each extension contributes the class of its *own*
presentation, and the differences are taken in the group of `𝖭𝖫_{X/S}`. Then the cocycle is total
and its cocycle identity is group algebra
(`StacksFrontier/Deformation/RingedSpaceThickening/ExtensionClassTorsor.lean`), `rep` has no
counterpart at all because the acting group names no presentation, and the pushout construction
is `StacksFrontier/Deformation/RingedSpaceThickening/ExtensionFromPushout.lean`.

What `classesEquivExtRelative` counts is the classes of extensions under *equality of their
class*. A morphism of extensions forces that equality
(`AlgebraicGeometry.RingedSpaceThickening.extClassDiff_eq_zero_of_hom`), and the equality is read
as the vanishing of an obstruction class over a common refinement
(`...extClassDiff_eq_zero_iff_pairRefinement`); that the converse holds too, so that the relation
*is* isomorphism of extensions, is clause (1) of **Stacks 08U8** and is not reproved here.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.addTorsorExtensionClasses` and
  `...classesEquivExtRelative`: **Stacks 0GPZ** — the classes of square-zero extensions of
  `f⁻¹𝒪_S`-algebras are a principal homogeneous space under `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`, and are
  in bijection with it by sending an extension to its class.

## References

* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 08UB](https://stacks.math.columbia.edu/tag/08UB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

section Relative

attribute [local instance] HasDerivedCategory.standard

variable {X S : RingedSpace.{u, u}} {f : X ⟶ S}
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}

/-- **The classes of square-zero extensions are a principal homogeneous space under
`Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`.** This is the torsor of **Stacks 08UC** for the problem of
**Stacks 0GPZ**, with no hypotheses left: the difference cocycle is
`AlgebraicGeometry.RingedSpaceThickening.extClassDiff`, its cocycle identity is
`...extClassDiff_add`, the realization of a prescribed class as a difference is
`...realizeExtClassDiff`, and the base point is `...nonempty_algebraSquareZeroExtension`. -/
@[instance_reducible]
noncomputable instance addTorsorExtensionClasses :
    AddTorsor
      (PresentedSquareZeroExtension.relativeObj f ⟶
        PresentedSquareZeroExtension.shiftedSingleObj G)
      (ExtensionClasses (realizeExtClassDiff (f := f) (G := G))) :=
  extClassAddTorsor realizeExtClassDiff nonempty_algebraSquareZeroExtension

/-- **Stacks Project, Tag 0GPZ.** The classes of square-zero extensions
`0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_S`-algebras are in bijection with
`Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`, by sending an extension to its class.

Both halves are proved. Injectivity is by construction: the classes are the quotient of the
type of extensions by equality of their class in `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`, a relation which a
morphism of extensions forces by
`AlgebraicGeometry.RingedSpaceThickening.extClassDiff_eq_zero_of_hom` and which is read as the
vanishing of an obstruction class over a common refinement by
`...extClassDiff_eq_zero_iff_pairRefinement`. Surjectivity is
`...exists_extension_extClass_eq`: the square-zero pushout of a presentation along a conormal
homomorphism representing the class, which exists by **Stacks 08UB**.

The acting group is the group of the tag, and the bijection is the one of the torsor
`addTorsorExtensionClasses` read at a base point. -/
@[stacks 0GPZ "the bijection, unconditional, with the acting group of the tag: \
Ext¹(𝖭𝖫_{X/S}, 𝒢) itself. The set counted is the classes of square-zero extensions of \
f⁻¹𝒪_S-algebras under equality of their class in that group; a morphism of extensions forces \
that equality by extClass_eq_extClass_of_hom, and that the converse holds too — so that the \
relation is isomorphism of extensions — is clause (1) of 08U8, a separate tag, not reproved \
here"]
def classesEquivExtRelative :
    ExtensionClasses (realizeExtClassDiff (f := f) (G := G)) ≃
      (PresentedSquareZeroExtension.relativeObj f ⟶
        PresentedSquareZeroExtension.shiftedSingleObj G) where
  toFun := Quotient.lift (fun P : AlgebraSquareZeroExtension f G ↦ P.toPresented.extClass)
    (fun _ _ h ↦ sub_eq_zero.1 h)
  invFun ζ := (extClassObstruction realizeExtClassDiff).isoClass
    (exists_extension_extClass_eq ζ).choose
  left_inv q := by
    refine Quotient.inductionOn q fun P ↦ Quotient.sound ?_
    change extClassDiff (exists_extension_extClass_eq P.toPresented.extClass).choose P = 0
    rw [extClassDiff, (exists_extension_extClass_eq P.toPresented.extClass).choose_spec, sub_self]
  right_inv ζ := (exists_extension_extClass_eq ζ).choose_spec

/-- The bijection of **Stacks 0GPZ** sends the class of a square-zero extension to the class of
that extension in `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`. -/
@[simp]
theorem classesEquivExtRelative_isoClass (P : AlgebraSquareZeroExtension f G) :
    classesEquivExtRelative ((extClassObstruction realizeExtClassDiff).isoClass P) =
      P.toPresented.extClass :=
  rfl

end Relative

end AlgebraicGeometry.RingedSpaceThickening

end
