module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnSpaceMonoidal
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.Meromorphic.IdealTimesModule

/-!
# The left unit constraint of the sheaf tensor product, on sections

Let `O` be a sheaf of commutative rings on a site `(C, J)`. The left unit constraint
`𝒪 ⊗ M ≅ M` of the tensor product sheaf of [Stacks, Tag 05NA] is scalar multiplication on a local
pure tensor, and so is the canonical action of the ideal of denominators of [Stacks, Tag 02P2]:

  `λ_ (r ⊗ₜ m) = r • m`,   `η (d ⊗ₜ n) = ι(d) • n`.

On a ringed space the left unit constraint of `Stacks.SheafOfModules.OnSpace.monoidal` is
`Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor`.

## Main definitions

* `Stacks.SheafOfModules.structureSection`: a section of the monoidal unit on a ringed space, read
  as a section of the structure sheaf.

## Main results

* `Stacks.SheafOfModules.tensorProductLeftUnitor_hom_val_app_tmul`: the displayed identity for
  `Invertible.tensorProductLeftUnitor`, over an arbitrary site, in the `toSheafify` spelling.
* `Stacks.SheafOfModules.monoidal_leftUnitor`: on a ringed space, `λ_` of
  `Stacks.SheafOfModules.OnSpace.monoidal` is `Invertible.tensorProductLeftUnitor`.
* `Stacks.SheafOfModules.tensorProductLeftUnitor_hom_val_app_toTensorSheafSection`: the same
  identity in the `toTensorSheafSection` spelling.
* `Stacks.SheafOfModules.denominatorIdealAction_val_app_toTensorSheafSection`: the canonical
  action of the ideal of denominators on a local pure tensor.

## Implementation notes

The two unitors in `monoidal_leftUnitor` are compared by
`Stacks.SheafOfModules.OnSpace.tensor_hom_ext`: a morphism out of a sheafified tensor product is
determined by its values on local pure tensors.

`Stacks.SheafOfModules.structureSection` is the ascription inverse to
`Stacks.SheafOfModules.OnSpace.unitSection`: the scalar action on sections is found by instance
search only at the `X.presheaf` spelling of the ring of sections.

## References

* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 02P2](https://stacks.math.columbia.edu/tag/02P2)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite

open scoped TensorProduct

universe v u w

namespace Stacks.SheafOfModules

attribute [local instance] monoidalCategoryPresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The left unit constraint of the sheaf tensor product, on a local pure tensor**, is scalar
multiplication: `λ_ (r ⊗ₜ m) = r • m`. -/
theorem tensorProductLeftUnitor_hom_val_app_tmul
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (V : Cᵒᵖ)
    (r : (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj.obj V)
    (m : M.val.obj V) :
    (Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor O hO M).hom.val.app V
        ((Stacks.SheafOfModules.TensorSheafification.toSheafify O hO
          (𝟙_ (PresheafOfModules.{w}
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj) ⊗
              M.val)).app V (r ⊗ₜ m)) = r • m :=
  Stacks.SheafOfModules.tensorSheafLeftUnitor_hom_val_app_tmul O hO M V r m

/-! ### The monoidal structure on a ringed space -/

section RingedSpace

open Stacks.SheafOfModules.TensorStalkRingedSpace Stacks.SheafOfModules.OnSpace

attribute [local instance_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf

attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.sheafify
  _root_.SheafOfModules.forget _root_.PresheafOfModules.restrictScalars

attribute [local instance] Stacks.SheafOfModules.OnSpace.monoidal

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-- A section of the monoidal unit, read as a section of the structure sheaf: the ascription
inverse to `Stacks.SheafOfModules.OnSpace.unitSection`. -/
abbrev structureSection (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ)
    (r : (SheafOfModules.unit (structureSheafRing X)).val.obj U) : X.presheaf.obj U := r

/-- **The left unit constraint of the monoidal structure of [Stacks, Tag 01CA] on a ringed space
is `Invertible.tensorProductLeftUnitor`.** -/
theorem monoidal_leftUnitor (A : SheafOfModules.{u} (structureSheafRing X)) :
    (λ_ A).hom =
      (Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor X.presheaf
        (structureSheafRing X).property A).hom :=
  tensor_hom_ext X fun U r a =>
    (leftUnitor_tmul X A U r a).trans
      (tensorProductLeftUnitor_hom_val_app_tmul X.presheaf (structureSheafRing X).property
        A U r a).symm

/-- **The left unit constraint `Invertible.tensorProductLeftUnitor`, on a local pure tensor in
the `toTensorSheafSection` spelling of a ringed space**, is scalar multiplication:
`λ_ (r ⊗ₜ a) = r • a`. -/
theorem tensorProductLeftUnitor_hom_val_app_toTensorSheafSection
    (A : SheafOfModules.{u} (structureSheafRing X)) (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ)
    (r : X.presheaf.obj U) (a : A.val.obj U) :
    ((Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor X.presheaf
          (structureSheafRing X).property A).hom.val.app U).hom
        (toTensorSheafSection X (SheafOfModules.unit (structureSheafRing X)) A U
          (r ⊗ₜ[X.presheaf.obj U] a)) = r • a :=
  (congrArg (fun f => (f.val.app U).hom
      (toTensorSheafSection X (SheafOfModules.unit (structureSheafRing X)) A U
        (r ⊗ₜ[X.presheaf.obj U] a))) (monoidal_leftUnitor X A)).symm.trans
    (leftUnitor_tmul X A U r a)

/-- **The canonical action of the ideal of denominators of [Stacks, Tag 02P2] on a local pure
tensor** is scalar multiplication through the ideal inclusion `ι`: `η (d ⊗ₜ n) = ι(d) • n`. -/
theorem denominatorIdealAction_val_app_toTensorSheafSection (Y : AlgebraicGeometry.Scheme.{u})
    (L F : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (s : AlgebraicGeometry.MeromorphicSection Y.sheaf L)
    (U : TopologicalSpace.Opens Y.toRingedSpace.carrier)
    (d : (AlgebraicGeometry.denominatorIdeal Y L s).val.obj (op U)) (n : F.val.obj (op U)) :
    ((AlgebraicGeometry.denominatorIdealAction Y L F s).val.app (op U)).hom
        (toTensorSheafSection Y.toRingedSpace (AlgebraicGeometry.denominatorIdeal Y L s) F (op U)
          (d ⊗ₜ[Y.toRingedSpace.presheaf.obj (op U)] n)) =
      structureSection Y.toRingedSpace (op U)
          (((AlgebraicGeometry.denominatorIdealι Y L s).val.app (op U)).hom d) • n :=
  (congrArg (fun z => ((Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor
      Y.toRingedSpace.presheaf (structureSheafRing Y.toRingedSpace).property
      F).hom.val.app (op U)).hom z)
    (tensorSheafMap_app_toTensorSheafSection Y.toRingedSpace
      (AlgebraicGeometry.denominatorIdeal Y L s) F
      (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) F
      (AlgebraicGeometry.denominatorIdealι Y L s) (𝟙 F) U d n)).trans
    (tensorProductLeftUnitor_hom_val_app_toTensorSheafSection Y.toRingedSpace F (op U)
      (((AlgebraicGeometry.denominatorIdealι Y L s).val.app (op U)).hom d) n)

end RingedSpace

end Stacks.SheafOfModules

end
