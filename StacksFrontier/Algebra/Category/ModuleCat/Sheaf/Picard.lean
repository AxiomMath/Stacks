module

public import Mathlib.CategoryTheory.Skeletal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleSmallEncoding
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Picard.EssentiallySmall.Invertible
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Basic

/-!
# The Picard group of a ringed site

Let `O` be a sheaf of commutative rings on a site `(C, J)`. The *Picard group* of `O` is the
abelian group of isomorphism classes of invertible sheaves of `O`-modules (Tag 01CS), with
addition induced by the tensor product sheaf of Tag 01CA. This is the Picard group both of a
ringed space (Tag 01CX) and of a ringed site (Tag 040C): the construction is carried out for an
arbitrary site and sheaf of commutative rings, so the two tags are the same statement here.

The construction has two halves. The categorical half is the commutative group structure on
`Skeleton (Stacks.SheafOfModules.InvertibleModules O hO)`, the type of isomorphism classes of
the full subcategory of invertible modules, `Stacks.SheafOfModules.picardSkeletonCommGroup`:
multiplication is the tensor product sheaf, the unit is the structure sheaf, and the inverse is
the `(-1)`st tensor power of Tag 01CU. The set-theoretic half is this file's contribution and
is Tag 040B: the invertible modules are essentially small at `max u v w`, so that skeleton is
`max u v w`-small and can be replaced by a type in `Type (max u v w)`.

## Main definitions

* `Stacks.SheafOfModules.Picard.PicardGroupData`: a small type of isomorphism classes, identified
  with that skeleton, carrying an abelian group structure whose addition is tensor product.
* `Stacks.SheafOfModules.Picard.picardGroupData`: the canonical such datum.
* `Stacks.SheafOfModules.Picard.PicardGroup`: the Picard group.
* `Stacks.SheafOfModules.Picard.classOf`: the class of an invertible sheaf of modules.

## Main results

* `Stacks.SheafOfModules.Picard.exists_classOf_eq`: every element of the Picard group is the
  class of an invertible sheaf of modules.
* `Stacks.SheafOfModules.Picard.classOf_eq_classOf_iff`: two invertible sheaves of modules have
  the same Picard class exactly when they are isomorphic.
* `Stacks.SheafOfModules.Picard.classOf_tensor` is Tag 01CX: addition of Picard classes is the
  tensor product sheaf.

## Implementation notes

*What is forced.* `Skeleton (Stacks.SheafOfModules.InvertibleModules O hO)` lives in the
universe of the sheaves of `O`-modules, which is larger than `max u v w`; so the Picard group is
taken to be a `max u v w`-small model of it, `Additive (Shrink (Skeleton …))`. The universe
`max u v w` is forced by Tag 040B: `essentiallySmall_isInvertible` produces smallness at
`max u v w` and no smaller, because its invariant is a family of submodules indexed by the
arrows of the site.

*What is chosen.* The group is taken multiplicatively from
`Stacks.SheafOfModules.picardSkeletonCommGroup` on the skeleton and then transported to
`Additive`, because the group axioms arrive there as the monoidal coherences, which read
multiplicatively. Nothing downstream sees that choice: the content of this file is pinned by
`classOf_eq_classOf_iff` and `classOf_tensor` together, which determine the group up to a unique
isomorphism commuting with `classOf`.

*Hypotheses.* Beyond the sheafification hypotheses `[HasWeakSheafify J AddCommGrpCat.{w}]` and
`[J.WEqualsLocallyBijective AddCommGrpCat.{w}]`, which are already needed to form the tensor
product sheaf, the slice-wise family `[∀ V : C, (J.over V).WEqualsLocallyBijective
AddCommGrpCat.{w}]` is needed, and only for Tag 040B: the local embedding of an invertible module
into a finite free module is extracted over the slice sites. It is the hereditary form of a
hypothesis already present, and it is what `Stacks.SheafOfModules.essentiallySmall_isInvertible`
asks for.

## References

* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 040C](https://stacks.math.columbia.edu/tag/040C)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 040B](https://stacks.math.columbia.edu/tag/040B)
-/

@[expose] public section

open CategoryTheory

universe v u w

namespace Stacks.SheafOfModules.Picard

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- Data realizing the isomorphism classes of invertible sheaves of modules as a small abelian
group whose addition is the tensor product sheaf. -/
structure PicardGroupData where
  /-- A small type of isomorphism classes. -/
  carrier : Type (max (max u v) w)
  /-- Identification of the carrier with the categorical isomorphism classes. -/
  classEquiv : Skeleton (InvertibleModules O hO) ≃ carrier
  /-- The abelian group structure on the carrier. -/
  addCommGroup : AddCommGroup carrier
  /-- Under `classEquiv`, the tensor product sheaf represents addition. -/
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

variable [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The canonical small abelian group of isomorphism classes of invertible sheaves of modules:
the skeleton of the category of invertible modules, shrunk to `Type (max u v w)` using Tag 040B
and transported to additive notation. -/
noncomputable def picardGroupData : PicardGroupData O hO := by
  let S := Skeleton (InvertibleModules O hO)
  let _ : CommGroup S := picardSkeletonCommGroup O hO
  have : ObjectProperty.EssentiallySmall.{max (max u v) w}
      (IsInvertible O hO : ObjectProperty (SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))) :=
    essentiallySmall_isInvertible O hO
  have : EssentiallySmall.{max (max u v) w} (InvertibleModules O hO) := inferInstance
  have : Small.{max (max u v) w} S := small_skeleton_of_essentiallySmall (InvertibleModules O hO)
  let eShrink : S ≃ Shrink.{max (max u v) w} S := equivShrink S
  let _ : CommGroup (Shrink.{max (max u v) w} S) := eShrink.symm.commGroup
  refine
    { carrier := Additive (Shrink.{max (max u v) w} S)
      classEquiv :=
        { toFun := fun s => Additive.ofMul (eShrink s)
          invFun := fun s => eShrink.symm (Additive.toMul s)
          left_inv := fun s => by simp
          right_inv := fun s => by simp }
      addCommGroup := inferInstance
      classEquiv_tensor := ?_ }
  intro L N hL hN hLN
  let A : InvertibleModules O hO := ⟨L, hL⟩
  let B : InvertibleModules O hO := ⟨N, hN⟩
  let T : InvertibleModules O hO := ⟨(((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
      (L)).obj (N)), hLN⟩
  change Additive.ofMul (eShrink (toSkeleton A)) + Additive.ofMul (eShrink (toSkeleton B)) =
    Additive.ofMul (eShrink (toSkeleton T))
  refine Additive.ofMul.injective ?_
  calc eShrink (toSkeleton A) * eShrink (toSkeleton B)
      = eShrink (picardSkeletonMul O hO (toSkeleton A) (toSkeleton B)) := by
        have hm (x y : S) : eShrink x * eShrink y = eShrink (x * y) := by
          change eShrink (eShrink.symm (eShrink x) * eShrink.symm (eShrink y)) = _
          simp
        rw [hm]
        rfl
    _ = eShrink (toSkeleton T) := congrArg eShrink (picardSkeletonMul_toSkeleton O hO A B)

/- This carrier is `Type (max u v w)`, obtained from `Skeleton (InvertibleModules O hO)` by
`Shrink`, which costs the essential smallness of Tag 040B and the extra instance
`[∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]` above. It is therefore not
the same object as `Stacks.SheafOfModules.PicardGroup`, whose carrier is the unshrunk
`Additive (Skeleton (InvertibleModules O hO))` in `Type (max u v (w + 1))` and which needs
neither input. Neither statement subsumes the other: stronger hypotheses here, smaller
carrier. -/
/-- The Picard group of `O`: the group of isomorphism classes of
invertible sheaves of `O`-modules, as a small type. -/
@[stacks 01CX "the Picard group",
  stacks 040C "the Picard group",
  ega "IV 21.3.2" "Pic(X) definition", sga "6 X 5.1" "Pic(X) definition"]
noncomputable def PicardGroup : Type (max (max u v) w) :=
  (picardGroupData O hO).carrier

/-- The abelian group structure on the Picard group; its addition is the tensor product sheaf,
by `classOf_tensor`. -/
@[stacks 01CX "abelian group structure", stacks 040C "abelian group structure"]
noncomputable instance instAddCommGroupPicardGroup : AddCommGroup (PicardGroup O hO) :=
  (picardGroupData O hO).addCommGroup

/-- The class in the Picard group of an invertible sheaf of modules. -/
@[stacks 040C "class of an invertible module", ega "IV 21.3.2" "cl(L)"]
noncomputable abbrev classOf (L : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (hL : IsInvertible O hO L) : PicardGroup O hO :=
  (picardGroupData O hO).classEquiv (toSkeleton (C := InvertibleModules O hO) ⟨L, hL⟩)

omit [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Every element of the Picard group is the class of an invertible sheaf of modules. -/
theorem exists_classOf_eq (p : PicardGroup O hO) :
    ∃ (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      (hL : IsInvertible O hO L), classOf O hO L hL = p := by
  obtain ⟨c, rfl⟩ := (picardGroupData O hO).classEquiv.surjective p
  obtain ⟨L, rfl⟩ : ∃ L, toSkeleton L = c := ⟨_, toSkeleton_fromSkeleton_obj c⟩
  exact ⟨L.obj, L.property, rfl⟩

omit [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Two invertible sheaves of modules determine the same Picard class exactly when they are
isomorphic, so the elements of the Picard group are the isomorphism classes. -/
@[stacks 040C "elements are isomorphism classes of invertible modules",
  ega "IV 21.3.2" "cl(L)=cl(L') iff iso"]
theorem classOf_eq_classOf_iff (L N : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (hL : IsInvertible O hO L) (hN : IsInvertible O hO N) :
    classOf O hO L hL = classOf O hO N hN ↔ Nonempty (L ≅ N) := by
  change (picardGroupData O hO).classEquiv _ = (picardGroupData O hO).classEquiv _ ↔ _
  rw [Equiv.apply_eq_iff_eq, toSkeleton_eq_toSkeleton_iff]
  exact ⟨fun ⟨e⟩ => ⟨(ObjectProperty.ι _).mapIso e⟩, fun ⟨e⟩ => ⟨ObjectProperty.isoMk _ e⟩⟩

omit [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Addition in the Picard group is the tensor product sheaf. -/
@[stacks 01CX "addition is tensor product", stacks 040C "addition is tensor product"]
theorem classOf_tensor (L N : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (hL : IsInvertible O hO L) (hN : IsInvertible O hO N)
    (hLN : IsInvertible O hO ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (L)).obj (N)))) :
    classOf O hO L hL + classOf O hO N hN =
      classOf O hO ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (L)).obj (N))) hLN :=
  (picardGroupData O hO).classEquiv_tensor L N hL hN hLN

end Stacks.SheafOfModules.Picard

end
