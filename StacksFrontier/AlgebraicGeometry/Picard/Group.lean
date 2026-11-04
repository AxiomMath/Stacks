module

public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import StacksFrontier.AlgebraicGeometry.Picard.Group.TensorConstraints
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Basic

/-!
# The Picard group as bundled data, and its smallness

Let `O` be a sheaf of commutative rings on a site `(C, J)`. An `O`-module is *invertible* when
tensoring by it is an equivalence of the category of sheaves of `O`-modules
(`Stacks.SheafOfModules.IsInvertible`, Tag 01CS). The tensor product of two invertible modules
is invertible (Tag 01CT) and every invertible module has a tensor inverse, namely its
`(-1)`st tensor power (Tag 01CU), so the isomorphism classes of invertible `O`-modules form an
abelian group under tensor product: the *Picard group* of `(C, J, O)`.

That group is `Stacks.SheafOfModules.PicardGroup` of
`StacksFrontier/AlgebraicGeometry/PicardGroup/Basic.lean`, realized as the skeleton of the full
subcategory of invertible modules, so that equality of classes *is* isomorphism of invertible
modules (`Stacks.SheafOfModules.picardClass_eq_iff`), with the group law transported from the
tensor product (`Stacks.SheafOfModules.picardClass_tensorSheaf`). This file adds two things to
it: a bundling of the carrier, the identification with the categorical classes and the group
law as a single structure, and the refinement of the carrier's universe that essential
smallness of the invertible modules buys.

## Main definitions

* `Stacks.Picard.PicardGroupData` — the Picard group as data: a type of isomorphism classes,
  its identification with the categorical classes, and an abelian group structure whose
  addition is tensor product.
* `Stacks.Picard.picardGroupData` — `Stacks.SheafOfModules.PicardGroup` presented as such data.

## Main results

* `Stacks.Picard.small_picardGroup_of_essentiallySmall` — the Picard group is `max u v w`-small
  as soon as the invertible modules are an essentially small class.

## Implementation notes

**Size.** Stacks Tag 040B (for a ringed site; Tag 01CW for a ringed space) asserts that the
isomorphism classes of invertible modules form a *set*, i.e. that the class of invertible
modules is essentially small relative to `max u v w`. That is a separate tag, and it is proved
in this library — `Stacks.SheafOfModules.essentiallySmall_isInvertible`
(`StacksFrontier/AlgebraicGeometry/Picard/EssentiallySmall/Invertible.lean`), with
`Stacks.Picard.small_picardGroup` alongside it. Its proof needs the dual `SheafHom(L, O)`, which
is available through the internal hom of presheaves of modules (Stacks Tag 01CQ).

`PicardGroupData.carrier` nonetheless still lives in `Type (max u v (w + 1))`, the universe of
the skeleton, rather than in `Type (max u v w)` — not because it must, but because nothing
downstream pins the universe, so shrinking it would be churn. Every consumer of it only forms
`AddEquiv`s, `Set`s and `AddSubgroup`s of it, all universe-polymorphic.
`small_picardGroup_of_essentiallySmall` states the refinement as an implication and its
hypothesis is **dischargeable today**, so a consumer needing `Type (max u v w)` can have it
without touching anything here.

Note that Tag **0B8M** is still left unproved in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleRankOne/`, but for a *different* reason
than the one this paragraph used to give: both of its implications are now proved and
fully proved, and what is missing is its third clause, the **counterexample** showing the
local-ring hypothesis cannot be dropped.

**Why a structure.** `PicardGroupData` bundles the carrier with its identification with the
categorical isomorphism classes, so that consumers never depend on how the carrier is built.
The group structure it carries is in fact unique: `classEquiv` is a bijection onto the
isomorphism classes and `classEquiv_tensor` pins the addition of any two classes, so any two
`PicardGroupData` for the same `O` have the same addition up to the unique compatible bijection.

The site object and morphism universes `u`, `v` are independent of the section universe `w`.

## References

* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 040B](https://stacks.math.columbia.edu/tag/040B)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

open Stacks.SheafOfModules (IsInvertible InvertibleModules PicardGroup picardTensorIso
  picardSkeletonMul picardSkeletonCommGroup)

universe v u w

namespace Stacks.Picard

attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf

attribute [local irreducible] PresheafOfModules.sheafification

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- Data realizing the isomorphism classes of invertible sheaves of modules as an abelian group
whose addition is tensor product. -/
structure PicardGroupData where
  /-- A type of isomorphism classes. -/
  carrier : Type (max u v (w + 1))
  /-- Identification of the carrier with the categorical isomorphism classes. -/
  classEquiv : Skeleton (InvertibleModules O hO) ≃ carrier
  /-- The abelian group structure on the carrier. -/
  addCommGroup : AddCommGroup carrier
  /-- Under `classEquiv`, tensor product represents addition. -/
  classEquiv_tensor :
    letI := addCommGroup
    ∀ (L N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      (hL : IsInvertible O hO L) (hN : IsInvertible O hO N)
      (hLN : IsInvertible O hO ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (L)).obj (N)))),
      classEquiv (toSkeleton (C := InvertibleModules O hO) ⟨L, hL⟩) +
          classEquiv (toSkeleton (C := InvertibleModules O hO) ⟨N, hN⟩) =
        classEquiv (toSkeleton (C := InvertibleModules O hO)
          ⟨(((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
              (L)).obj (N)), hLN⟩)

/-- The canonical abelian group of isomorphism classes of invertible sheaves of modules: the
skeleton of the category of invertible modules, with the group law of
`picardSkeletonCommGroup` written additively. -/
noncomputable def picardGroupData : PicardGroupData O hO := by
  letI : CommGroup (Skeleton (InvertibleModules O hO)) := picardSkeletonCommGroup O hO
  refine
    { carrier := Additive (Skeleton (InvertibleModules O hO))
      classEquiv := Additive.ofMul
      addCommGroup := inferInstance
      classEquiv_tensor := ?_ }
  intro L N hL hN hLN
  have hmul : picardSkeletonMul O hO
      (toSkeleton (C := InvertibleModules O hO) ⟨L, hL⟩)
      (toSkeleton (C := InvertibleModules O hO) ⟨N, hN⟩) =
      toSkeleton (C := InvertibleModules O hO)
        ⟨(((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
            (L)).obj (N)), hLN⟩ :=
    toSkeleton_eq_toSkeleton_iff.2 ⟨picardTensorIso O hO
      (fromSkeletonToSkeletonIso (C := InvertibleModules O hO) ⟨L, hL⟩)
      (fromSkeletonToSkeletonIso (C := InvertibleModules O hO) ⟨N, hN⟩)⟩
  exact Additive.ofMul.congr_arg hmul

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- **Stacks 040B.** Once the invertible sheaves of modules are known to form an essentially
small class — which is the content of Tag 040B, not proved in this development — the Picard
group is `max u v w`-small, i.e. the isomorphism classes of invertible modules form a set of
that size. -/
theorem small_picardGroup_of_essentiallySmall
    [LocallySmall.{max u v w} (SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))]
    [ObjectProperty.EssentiallySmall.{max u v w} (IsInvertible O hO)] :
    Small.{max u v w} (PicardGroup O hO) :=
  (small_congr (Additive.ofMul (α := Skeleton (InvertibleModules O hO)))).1
    (small_skeleton_of_essentiallySmall (InvertibleModules O hO))

end Stacks.Picard
