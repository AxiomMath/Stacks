module

public import Mathlib.CategoryTheory.Skeletal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Picard group

Let `O` be a sheaf of commutative rings on a site `(C, J)` admitting sheafification. The
*Picard group* of `O` is the abelian group whose elements are the isomorphism classes of
invertible sheaves of `O`-modules and whose addition is the tensor product. This file
constructs it.

The elements are realized by Mathlib's `CategoryTheory.Skeleton` of the full subcategory of
invertible sheaves of modules, so that equality of classes is *exactly* isomorphism of sheaves
(`picardClass_eq_iff`). The group law is transported from the tensor product: associativity,
the two unit laws and commutativity are the corresponding constraints of the sheaf tensor
product, and the inverse of the class of `L` is the class of `L^{⊗ -1}`, the inverse law being
the successor comparison `L^{⊗ -1} ⊗ L ≅ L^{⊗ 0} = O` of Tag 01CU at `n = -1`.

## Main definitions

* `Stacks.SheafOfModules.InvertibleModules`: the full subcategory of invertible sheaves of
  `O`-modules.
* `Stacks.SheafOfModules.PicardGroup`: the Picard group, as a type of isomorphism classes.
* `Stacks.SheafOfModules.picardClass`: the class of an invertible sheaf of modules.
* `Stacks.SheafOfModules.picardClassEquiv`: the identification of the Picard group with the
  isomorphism classes.

## Main results

* `Stacks.SheafOfModules.picardClass_eq_iff`: two invertible sheaves have the same class
  exactly when they are isomorphic.
* `Stacks.SheafOfModules.picardClass_tensorSheaf`: addition of classes is the tensor product.
* `Stacks.SheafOfModules.picardClass_zero` and
  `Stacks.SheafOfModules.picardClass_tensorPower_neg_one`: the neutral element is the class of
  the structure sheaf, and the negative of a class is the class of the inverse tensor power.
* `Stacks.SheafOfModules.picardClass_eq_zero_iff`: a class vanishes exactly when the sheaf is
  trivial.
* `Stacks.SheafOfModules.subsingleton_picardGroup`: the Picard group is trivial as soon as
  every invertible sheaf of modules is trivial.
* `Stacks.SheafOfModules.tensorInverseUniqueIso`: a tensor inverse is unique up to
  isomorphism.

## Implementation notes

**Invertibility class.** Everything here is stated for `Stacks.SheafOfModules.IsInvertible` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorInvertible.lean`, which is the class the
consumers of the Picard group use. The repository carries a second, definitionally identical
constant `AlgebraicGeometry.SheafOfModules.IsInvertible`; the bridge between them is
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry` of
`StacksFrontier/AlgebraicGeometry/InvertibleClasses/Basic.lean`, and no new bridge is
introduced here. The four constraints of the sheaf tensor product that the group law needs —
`tensorProductIso`, `tensorProductAssociator` and the two unitors — carry no invertibility
hypothesis at all, so they are reused from `Stacks.SheafOfModules.Invertible` across the class
divide without any comparison being needed.

**Universe level.** `PicardGroup O hO` lives in the universe of
`SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)`, not in `Type
  (max (max u v) w)`. The
Stacks definition (Tag 01CX) asserts only that the isomorphism classes form an abelian group
under tensor product, which is what is proved here; that those classes form a *set* of the size
of the site is the separate statement of
[Stacks, Tag 040B](https://stacks.math.columbia.edu/tag/040B), which is not in the development.
Shrinking the carrier to `Type (max (max u v) w)` needs exactly that essential smallness and
nothing else, so it is a one-step addition once Tag 040B lands: compose `picardClassEquiv`
with `equivShrink`.

## References

* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

open CategoryTheory

universe v u w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The full subcategory of invertible sheaves of `O`-modules. -/
abbrev InvertibleModules :=
  ObjectProperty.FullSubcategory (IsInvertible O hO)

/-- The tensor product of two invertible sheaves of modules, as an invertible sheaf. The
invertibility is Tag 01CT part (1). -/
noncomputable def picardTensorObj (L N : InvertibleModules O hO) : InvertibleModules O hO :=
  haveI := L.property
  haveI := N.property
  ⟨(((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (L.obj)).obj (N.obj)),
    isInvertible_tensorSheaf O hO L.obj N.obj⟩

/-- The structure sheaf, as an invertible sheaf of modules over itself. -/
noncomputable def picardUnitObj : InvertibleModules O hO :=
  ⟨SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO),
    isInvertible_unit O hO⟩

/-- The inverse tensor power `L^{⊗ -1}` of an invertible sheaf of modules, as an invertible
sheaf. The invertibility is Tag 01CU. -/
noncomputable def picardInvObj (L : InvertibleModules O hO) : InvertibleModules O hO :=
  haveI := L.property
  ⟨TensorPower.tensorPower O hO L.obj (-1),
    TensorPower.isInvertible_tensorPower O hO L.obj (-1)⟩

/-- Functoriality of the tensor product of invertible sheaves in both variables. -/
noncomputable def picardTensorIso {L L' N N' : InvertibleModules O hO}
    (e : L ≅ L') (f : N ≅ N') :
    picardTensorObj O hO L N ≅ picardTensorObj O hO L' N' :=
  ObjectProperty.isoMk _ <| Invertible.tensorProductIso O hO
    ((ObjectProperty.ι _).mapIso e) ((ObjectProperty.ι _).mapIso f)

/-- Associativity of the tensor product of invertible sheaves. -/
noncomputable def picardTensorAssoc (L N P : InvertibleModules O hO) :
    picardTensorObj O hO (picardTensorObj O hO L N) P ≅
      picardTensorObj O hO L (picardTensorObj O hO N P) :=
  ObjectProperty.isoMk _ <| Invertible.tensorProductAssociator O hO L.obj N.obj P.obj

/-- The structure sheaf is a left unit for the tensor product of invertible sheaves. -/
noncomputable def picardUnitTensorIso (L : InvertibleModules O hO) :
    picardTensorObj O hO (picardUnitObj O hO) L ≅ L :=
  ObjectProperty.isoMk _ <| Invertible.tensorProductLeftUnitor O hO L.obj

/-- The structure sheaf is a right unit for the tensor product of invertible sheaves. -/
noncomputable def picardTensorUnitIso (L : InvertibleModules O hO) :
    picardTensorObj O hO L (picardUnitObj O hO) ≅ L :=
  ObjectProperty.isoMk _ <| Invertible.tensorProductRightUnitor O hO L.obj

/-- Commutativity of the tensor product of invertible sheaves. -/
noncomputable def picardTensorComm (L N : InvertibleModules O hO) :
    picardTensorObj O hO L N ≅ picardTensorObj O hO N L :=
  ObjectProperty.isoMk _ <| tensorSheafBraiding O hO L.obj N.obj

/-- `L^{⊗ -1} ⊗ L ≅ O`: the inverse law for the tensor product of invertible sheaves. It is the
successor comparison of Tag 01CU at `n = -1`, whose target `L^{⊗ 0}` is the structure sheaf. -/
noncomputable def picardInvTensorIso (L : InvertibleModules O hO) :
    picardTensorObj O hO (picardInvObj O hO L) L ≅ picardUnitObj O hO :=
  haveI := L.property
  ObjectProperty.isoMk _ <|
    TensorPower.tensorPowerSuccIso O hO L.obj (-1) ≪≫
      TensorPower.tensorPowerReindex O hO L.obj (neg_add_cancel (1 : ℤ))

/-- **A tensor inverse is unique up to isomorphism**: if `X ⊗ L` and `Y ⊗ L` are both
isomorphic to the structure sheaf then `X ≅ Y`. -/
noncomputable def tensorInverseUniqueIso {X Y L : InvertibleModules O hO}
    (eX : picardTensorObj O hO X L ≅ picardUnitObj O hO)
    (eY : picardTensorObj O hO Y L ≅ picardUnitObj O hO) : X ≅ Y :=
  (picardTensorUnitIso O hO X).symm ≪≫
    picardTensorIso O hO (Iso.refl X) eY.symm ≪≫
    picardTensorIso O hO (Iso.refl X) (picardTensorComm O hO Y L) ≪≫
    (picardTensorAssoc O hO X L Y).symm ≪≫
    picardTensorIso O hO eX (Iso.refl Y) ≪≫
    picardUnitTensorIso O hO Y

/-- Functoriality of the inverse tensor power in isomorphisms, by uniqueness of tensor
inverses. -/
noncomputable def picardInvObjIso {L L' : InvertibleModules O hO} (e : L ≅ L') :
    picardInvObj O hO L ≅ picardInvObj O hO L' :=
  tensorInverseUniqueIso O hO
    (picardTensorIso O hO (Iso.refl _) e.symm ≪≫ picardInvTensorIso O hO L)
    (picardInvTensorIso O hO L')

section Skeleton

/-- Tensor product on isomorphism classes of invertible sheaves of modules. -/
noncomputable def picardSkeletonMul (a b : Skeleton (InvertibleModules O hO)) :
    Skeleton (InvertibleModules O hO) :=
  toSkeleton <| picardTensorObj O hO
    ((fromSkeleton (InvertibleModules O hO)).obj a)
    ((fromSkeleton (InvertibleModules O hO)).obj b)

/-- The class of the structure sheaf. -/
noncomputable def picardSkeletonOne : Skeleton (InvertibleModules O hO) :=
  toSkeleton (picardUnitObj O hO)

/-- The class of the inverse tensor power. -/
noncomputable def picardSkeletonInv (a : Skeleton (InvertibleModules O hO)) :
    Skeleton (InvertibleModules O hO) :=
  toSkeleton <| picardInvObj O hO ((fromSkeleton (InvertibleModules O hO)).obj a)

/-- The product of the classes of `L` and `N` is the class of `L ⊗ N`. -/
@[simp]
theorem picardSkeletonMul_toSkeleton (L N : InvertibleModules O hO) :
    picardSkeletonMul O hO (toSkeleton L) (toSkeleton N) =
      toSkeleton (picardTensorObj O hO L N) :=
  congr_toSkeleton_of_iso <| picardTensorIso O hO
    (fromSkeletonToSkeletonIso L) (fromSkeletonToSkeletonIso N)

/-- The inverse of the class of `L` is the class of `L^{⊗ -1}`. -/
@[simp]
theorem picardSkeletonInv_toSkeleton (L : InvertibleModules O hO) :
    picardSkeletonInv O hO (toSkeleton L) = toSkeleton (picardInvObj O hO L) :=
  congr_toSkeleton_of_iso <| picardInvObjIso O hO (fromSkeletonToSkeletonIso L)

/-- The product of isomorphism classes of invertible sheaves is associative. -/
theorem picardSkeleton_mul_assoc (a b c : Skeleton (InvertibleModules O hO)) :
    picardSkeletonMul O hO (picardSkeletonMul O hO a b) c =
      picardSkeletonMul O hO a (picardSkeletonMul O hO b c) := by
  obtain ⟨L, rfl⟩ := Quotient.exists_rep a
  obtain ⟨N, rfl⟩ := Quotient.exists_rep b
  obtain ⟨P, rfl⟩ := Quotient.exists_rep c
  rw [picardSkeletonMul_toSkeleton, picardSkeletonMul_toSkeleton,
    picardSkeletonMul_toSkeleton, picardSkeletonMul_toSkeleton]
  exact congr_toSkeleton_of_iso <| picardTensorAssoc O hO L N P

/-- The class of the structure sheaf is a left unit for the product of classes. -/
theorem picardSkeleton_one_mul (a : Skeleton (InvertibleModules O hO)) :
    picardSkeletonMul O hO (picardSkeletonOne O hO) a = a := by
  obtain ⟨L, rfl⟩ := Quotient.exists_rep a
  rw [picardSkeletonOne, picardSkeletonMul_toSkeleton]
  exact congr_toSkeleton_of_iso <| picardUnitTensorIso O hO L

/-- The class of the structure sheaf is a right unit for the product of classes. -/
theorem picardSkeleton_mul_one (a : Skeleton (InvertibleModules O hO)) :
    picardSkeletonMul O hO a (picardSkeletonOne O hO) = a := by
  obtain ⟨L, rfl⟩ := Quotient.exists_rep a
  rw [picardSkeletonOne, picardSkeletonMul_toSkeleton]
  exact congr_toSkeleton_of_iso <| picardTensorUnitIso O hO L

/-- The product of isomorphism classes of invertible sheaves is commutative. -/
theorem picardSkeleton_mul_comm (a b : Skeleton (InvertibleModules O hO)) :
    picardSkeletonMul O hO a b = picardSkeletonMul O hO b a := by
  obtain ⟨L, rfl⟩ := Quotient.exists_rep a
  obtain ⟨N, rfl⟩ := Quotient.exists_rep b
  rw [picardSkeletonMul_toSkeleton, picardSkeletonMul_toSkeleton]
  exact congr_toSkeleton_of_iso <| picardTensorComm O hO L N

/-- The class of `L^{⊗ -1}` times the class of `L` is the class of the structure sheaf. -/
theorem picardSkeleton_inv_mul (a : Skeleton (InvertibleModules O hO)) :
    picardSkeletonMul O hO (picardSkeletonInv O hO a) a = picardSkeletonOne O hO := by
  obtain ⟨L, rfl⟩ := Quotient.exists_rep a
  rw [picardSkeletonInv_toSkeleton, picardSkeletonMul_toSkeleton, picardSkeletonOne]
  exact congr_toSkeleton_of_iso <| picardInvTensorIso O hO L

/-- Isomorphism classes of invertible sheaves of `O`-modules form a commutative group under
tensor product. This is the multiplicative form of the Picard group. -/
@[instance_reducible]
noncomputable def picardSkeletonCommGroup : CommGroup (Skeleton (InvertibleModules O hO)) where
  mul := picardSkeletonMul O hO
  one := picardSkeletonOne O hO
  inv := picardSkeletonInv O hO
  mul_assoc := picardSkeleton_mul_assoc O hO
  one_mul := picardSkeleton_one_mul O hO
  mul_one := picardSkeleton_mul_one O hO
  inv_mul_cancel := picardSkeleton_inv_mul O hO
  mul_comm := picardSkeleton_mul_comm O hO

end Skeleton

/-- The *Picard group* of a sheaf of rings `O` on a site: the abelian group whose elements are
the isomorphism classes of invertible sheaves of `O`-modules and whose addition is the tensor
product. -/
@[stacks 01CX "the Picard group",
  ega "IV 21.3.2" "Pic(X) definition",
  sga "6 X 5.1" "Pic(X) definition"]
noncomputable def PicardGroup : Type _ :=
  Additive (Skeleton (InvertibleModules O hO))

/-- The addition of the Picard group, induced by the tensor product of invertible sheaves of
modules. -/
@[stacks 01CX "abelian group structure", ega "IV 21.3.2" "Pic(X) comm. group"]
noncomputable instance instAddCommGroupPicardGroup : AddCommGroup (PicardGroup O hO) :=
  letI := picardSkeletonCommGroup O hO
  inferInstanceAs (AddCommGroup (Additive (Skeleton (InvertibleModules O hO))))

/-- The Picard group is the type of isomorphism classes of invertible sheaves of modules. -/
noncomputable def picardClassEquiv :
    Skeleton (InvertibleModules O hO) ≃ PicardGroup O hO :=
  Additive.ofMul

/-- The class in the Picard group of an invertible sheaf of modules. -/
noncomputable def picardClass (L : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (hL : IsInvertible O hO L) : PicardGroup O hO :=
  picardClassEquiv O hO (toSkeleton (C := InvertibleModules O hO) ⟨L, hL⟩)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- The image of the isomorphism class of `L` in the Picard group is `picardClass` of `L`. -/
theorem picardClassEquiv_toSkeleton (L : InvertibleModules O hO) :
    picardClassEquiv O hO (toSkeleton L) = picardClass O hO L.obj L.property :=
  rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- Every element of the Picard group is the class of an invertible sheaf of modules. -/
theorem exists_picardClass_eq (x : PicardGroup O hO) :
    ∃ (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) (hL
      : IsInvertible O hO L),
      picardClass O hO L hL = x := by
  obtain ⟨a, rfl⟩ := (picardClassEquiv O hO).surjective x
  obtain ⟨L, rfl⟩ := Quotient.exists_rep a
  exact ⟨L.obj, L.property, rfl⟩

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- **Two invertible sheaves of modules have the same Picard class exactly when they are
isomorphic.** -/
theorem picardClass_eq_iff (L N : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (hL : IsInvertible O hO L) (hN : IsInvertible O hO N) :
    picardClass O hO L hL = picardClass O hO N hN ↔ Nonempty (L ≅ N) := by
  rw [picardClass, picardClass, (picardClassEquiv O hO).apply_eq_iff_eq,
    toSkeleton_eq_toSkeleton_iff]
  exact ⟨fun ⟨e⟩ => ⟨(ObjectProperty.ι _).mapIso e⟩, fun ⟨e⟩ => ⟨ObjectProperty.isoMk _ e⟩⟩

/-- Addition in the Picard group is the tensor product. -/
@[stacks 01CX "addition is tensor product", ega "IV 21.3.2" "cl(L)cl(L')=cl(L⊗L')"]
theorem picardClass_tensorSheaf (L N : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (hL : IsInvertible O hO L) (hN : IsInvertible O hO N)
    (hLN : IsInvertible O hO ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (L)).obj (N)))) :
    picardClass O hO L hL + picardClass O hO N hN =
      picardClass O hO ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (L)).obj (N))) hLN :=
  congrArg (picardClassEquiv O hO)
    (picardSkeletonMul_toSkeleton O hO (⟨L, hL⟩ : InvertibleModules O hO)
      (⟨N, hN⟩ : InvertibleModules O hO))

/-- The neutral element of the Picard group is the class of the structure sheaf. -/
theorem picardClass_zero :
    picardClass O hO (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      O hO))
      (isInvertible_unit O hO) = 0 :=
  rfl

/-- **A Picard class vanishes exactly when the sheaf is trivial.** -/
theorem picardClass_eq_zero_iff (L : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (hL : IsInvertible O hO L) :
    picardClass O hO L hL = 0 ↔ IsTrivial O hO L := by
  rw [← picardClass_zero O hO, picardClass_eq_iff]

/-- **The Picard group is trivial as soon as every invertible sheaf of modules is trivial.**
This is the form in which triviality of a Picard group is proved: produce a trivialization of
an arbitrary invertible sheaf. -/
theorem subsingleton_picardGroup
    (h : ∀ L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO),
      IsInvertible O hO L → IsTrivial O hO L) :
    Subsingleton (PicardGroup O hO) where
  allEq x y := by
    obtain ⟨L, hL, rfl⟩ := exists_picardClass_eq O hO x
    obtain ⟨N, hN, rfl⟩ := exists_picardClass_eq O hO y
    rw [(picardClass_eq_zero_iff O hO L hL).2 (h L hL),
      (picardClass_eq_zero_iff O hO N hN).2 (h N hN)]

/-- The negative of the class of `L` is the class of the inverse tensor power `L^{⊗ -1}`. -/
theorem picardClass_tensorPower_neg_one
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) [hL :
      IsInvertible O hO L] :
    picardClass O hO (TensorPower.tensorPower O hO L (-1))
        (TensorPower.isInvertible_tensorPower O hO L (-1)) = -picardClass O hO L hL :=
  congrArg (picardClassEquiv O hO)
    (picardSkeletonInv_toSkeleton O hO (⟨L, hL⟩ : InvertibleModules O hO)).symm

end Stacks.SheafOfModules

end
