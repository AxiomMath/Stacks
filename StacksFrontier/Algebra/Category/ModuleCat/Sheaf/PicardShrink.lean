module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Picard

/-!
# The small model of the Picard group is the Picard group

Let `O` be a sheaf of commutative rings on a site `(C, J)`. Its Picard group has two
realizations. The first, `Stacks.SheafOfModules.PicardGroup`, is
`Additive (Skeleton (InvertibleModules O hO))`: the isomorphism classes of invertible sheaves of
`O`-modules, in the universe of the sheaves of modules. The second,
`Stacks.SheafOfModules.Picard.PicardGroup`, is the same type shrunk to `Type (max u v w)` using
essential smallness.

The second is the first transported along `Equiv.shrink`, so the two agree: the isomorphism
sends `Stacks.SheafOfModules.picardClass` to `Stacks.SheafOfModules.Picard.classOf`.

## Main definitions

* `Stacks.SheafOfModules.picardGroupShrinkAddEquiv`: the two Picard groups are isomorphic as
  abelian groups.

## Main results

* `Stacks.SheafOfModules.picardGroupShrinkAddEquiv_picardClass`: the isomorphism carries the
  class of an invertible sheaf of modules to its class.

## Implementation notes

The underlying bijection is the composite of the two identifications of each Picard group with
the skeleton, `Stacks.SheafOfModules.picardClassEquiv` and the `classEquiv` field of
`Stacks.SheafOfModules.Picard.picardGroupData`; on classes it is therefore the identity by
`rfl`, which is what pins it. Additivity is checked on classes, where both sides are the tensor
product sheaf: every element of the unshrunk group is a class
(`Stacks.SheafOfModules.exists_picardClass_eq`), and the two addition laws are
`Stacks.SheafOfModules.picardClass_tensorSheaf` and
`Stacks.SheafOfModules.Picard.classOf_tensor`.

## References

* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 040B](https://stacks.math.columbia.edu/tag/040B)
* [Stacks Project, Tag 040C](https://stacks.math.columbia.edu/tag/040C)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The bijection between the Picard group and its small model: both are the type of
isomorphism classes of invertible sheaves of `O`-modules. -/
def picardGroupShrinkEquiv : PicardGroup O hO ≃ Picard.PicardGroup O hO :=
  (picardClassEquiv O hO).symm.trans (Picard.picardGroupData O hO).classEquiv

/-- The comparison of the two Picard groups sends the class of an invertible sheaf of modules to
its class. -/
theorem picardGroupShrinkEquiv_picardClass
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (hL : IsInvertible O hO L) :
    picardGroupShrinkEquiv O hO (picardClass O hO L hL) = Picard.classOf O hO L hL :=
  rfl

/-- **The Picard group and its small model are isomorphic abelian groups.** The addition of
either is the tensor product sheaf, so the bijection between them is additive. -/
def picardGroupShrinkAddEquiv : PicardGroup O hO ≃+ Picard.PicardGroup O hO where
  toEquiv := picardGroupShrinkEquiv O hO
  map_add' x y := by
    obtain ⟨L, hL, rfl⟩ := exists_picardClass_eq O hO x
    obtain ⟨N, hN, rfl⟩ := exists_picardClass_eq O hO y
    have := hL
    have := hN
    have hLN := isInvertible_tensorSheaf O hO L N
    rw [picardClass_tensorSheaf O hO L N hL hN hLN]
    change Picard.classOf O hO
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj L).obj N)
        hLN = Picard.classOf O hO L hL + Picard.classOf O hO N hN
    exact (Picard.classOf_tensor O hO L N hL hN hLN).symm

/-- The isomorphism of the Picard group with its small model sends the class of an invertible
sheaf of modules to its class. -/
@[simp]
theorem picardGroupShrinkAddEquiv_picardClass
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (hL : IsInvertible O hO L) :
    picardGroupShrinkAddEquiv O hO (picardClass O hO L hL) = Picard.classOf O hO L hL :=
  rfl

end Stacks.SheafOfModules

end
