module

public import Mathlib.Algebra.Group.TransferInstance
public import StacksFrontier.AlgebraicGeometry.Picard.EssentiallySmall.Invertible
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback

/-!
# The Picard group at the universe of the isomorphism classes

Let `O` be a sheaf of commutative rings on a site `(C, J)`, with `C : Type u` a category with
morphisms in `Type v` and module sections in `Type w`.
`Stacks.SheafOfModules.PicardGroup` realizes the Picard group of Tag 01CX as the skeleton of the
category of invertible `O`-modules, which places
it in `Type (max u v (w + 1))`: the carrier is a type of *objects* of that category, and those
have sections in `Type w`.

Tag 040B says the isomorphism classes nonetheless form a set of size `max u v w`
(`Stacks.SheafOfModules.essentiallySmall_isInvertible`), so the Picard group *is* `max u v w`-
small (`Stacks.Picard.small_picardGroup`). This file takes the consequence: it transports the
Picard group along `equivShrink` onto `Stacks.Picard.SmallPicardGroup`, a type of the smaller
universe `max u v w`, with the group structure and the identification with the isomorphism
classes carried across.

The essential input is Tag 040B. The point is the *universe* `max u v w` — which, for a ringed
space or a scheme with `u = v = w`, is `Type u` rather than `Type (u + 1)`. The two realizations
are identified by `Stacks.Picard.smallPicardGroupAddEquiv`, an isomorphism of abelian groups, so
every result about `Stacks.SheafOfModules.PicardGroup` transfers, and in particular pullback
descends (`Stacks.Picard.smallPullbackClassHom`, `Stacks.Picard.smallSchemePullbackClassHom`).

## Main definitions

* `Stacks.Picard.SmallPicardGroup` — the Picard group of `(C, J, O)` in `Type (max u v w)`.
* `Stacks.Picard.smallPicardGroupAddEquiv` — its identification with
  `Stacks.SheafOfModules.PicardGroup` as an abelian group.
* `Stacks.Picard.smallClassEquiv` — its identification with the categorical isomorphism classes.
* `Stacks.Picard.smallClassOf` — the class of an invertible sheaf of modules in it.
* `Stacks.Picard.smallOfRingedSpace`, `Stacks.Picard.smallOfScheme` — the same for a ringed
  space and for a scheme, in `Type u`.
* `Stacks.Picard.smallPullbackClassHom`, `Stacks.Picard.smallSchemePullbackClassHom` — pullback
  on the small Picard groups, as a homomorphism of abelian groups.

## Main results

* `Stacks.Picard.smallClassOf_eq_smallClassOf_iff` — two invertible sheaves of modules have the
  same small Picard class exactly when they are isomorphic.
* `Stacks.Picard.smallClassOf_tensor` — addition of small Picard classes is tensor product.
* `Stacks.Picard.smallClassEquiv_tensor` — the same, read through `smallClassEquiv`.
* `Stacks.Picard.smallPullbackClass_classOf` — pullback sends the small class of `L` to the
  small class of `f^*L`.

## Implementation notes

**Why a transport and not a second construction.** The group could instead be built directly as
`Additive (Shrink (Skeleton (InvertibleModules O hO)))`, re-deriving the group law on the shrunk
type. Transporting the finished `Stacks.SheafOfModules.PicardGroup` is strictly better: the
group law is not re-derived, and `smallPicardGroupAddEquiv` makes the whole of the existing
Picard development — `picardClass_eq_iff`, `picardClass_tensorSheaf`, `pullbackClass` and the
Galois action — available at the smaller universe without restating any of it.

**No second bundled structure.** `Stacks.Picard.PicardGroupData` fixes
`carrier : Type (max u v (w + 1))` in its signature, so the small carrier does not inhabit it.
Rather than coin a parallel structure, the four pieces of data that structure bundles are
supplied here as separate declarations — `SmallPicardGroup`, `smallClassEquiv`,
`instAddCommGroupSmallPicardGroup` and `smallClassEquiv_tensor`.

**No `@[stacks]` attribute.** Tag 01CX is carried by `Stacks.SheafOfModules.PicardGroup` and
Tag 040B by `Stacks.SheafOfModules.essentiallySmall_isInvertible`; nothing here is the content
of either.

## References

* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 040B](https://stacks.math.columbia.edu/tag/040B)
* [Stacks Project, Tag 01CW](https://stacks.math.columbia.edu/tag/01CW)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

open Stacks.SheafOfModules (IsInvertible InvertibleModules PicardGroup picardClass
  picardClass_eq_iff picardClass_tensorSheaf)

open Stacks.RingedSpace (structureIsSheaf)

universe v u w

namespace Stacks.Picard

section Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- Tag 040B, as an instance: the Picard group of `(C, J, O)` is `max u v w`-small. -/
instance instSmallPicardGroup : Small.{max u v w} (PicardGroup O hO) :=
  small_picardGroup O hO

/-- The Picard group of `(C, J, O)` in `Type (max u v w)`: the isomorphism classes of invertible
sheaves of `O`-modules, read at the universe of the classes themselves rather than at that of
the sheaves. -/
def SmallPicardGroup : Type (max u v w) := Shrink.{max u v w} (PicardGroup O hO)

/-- The small Picard group is in bijection with the Picard group. -/
def smallPicardGroupEquiv : SmallPicardGroup O hO ≃ PicardGroup O hO :=
  (equivShrink (PicardGroup O hO)).symm

/-- The abelian group structure on the small Picard group transported from the Picard group. -/
noncomputable instance instAddCommGroupSmallPicardGroup :
    AddCommGroup (SmallPicardGroup O hO) :=
  Equiv.addCommGroup (smallPicardGroupEquiv O hO)

/-- The small Picard group is isomorphic to the Picard group as an abelian group. -/
def smallPicardGroupAddEquiv : SmallPicardGroup O hO ≃+ PicardGroup O hO :=
  Equiv.addEquiv (smallPicardGroupEquiv O hO)

/-- The additive equivalence `smallPicardGroupAddEquiv` acts as the bijection
`smallPicardGroupEquiv`. -/
@[simp]
theorem smallPicardGroupAddEquiv_apply (x : SmallPicardGroup O hO) :
    smallPicardGroupAddEquiv O hO x = smallPicardGroupEquiv O hO x :=
  rfl

/-- Identification of the small Picard group with the categorical isomorphism classes of
invertible sheaves of modules: the `classEquiv` of `Stacks.Picard.PicardGroupData`, carried onto
the smaller universe. -/
def smallClassEquiv : Skeleton (InvertibleModules O hO) ≃ SmallPicardGroup O hO :=
  (picardGroupData O hO).classEquiv.trans (smallPicardGroupAddEquiv O hO).symm.toEquiv

/-- The class in the small Picard group of an invertible sheaf of modules. -/
def smallClassOf (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
  O hO))
    (hL : IsInvertible O hO L) : SmallPicardGroup O hO :=
  (smallPicardGroupAddEquiv O hO).symm (picardClass O hO L hL)

/-- The small class of an invertible sheaf of modules corresponds to its Picard class. -/
@[simp]
theorem smallPicardGroupAddEquiv_smallClassOf
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) (hL :
      IsInvertible O hO L) :
    smallPicardGroupAddEquiv O hO (smallClassOf O hO L hL) = picardClass O hO L hL :=
  (smallPicardGroupAddEquiv O hO).apply_symm_apply _

/-- `smallClassEquiv` sends the isomorphism class of an invertible sheaf of modules to its small
class. -/
theorem smallClassEquiv_eq_smallClassOf
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) (hL :
      IsInvertible O hO L) :
    smallClassEquiv O hO (toSkeleton (C := InvertibleModules O hO) ⟨L, hL⟩) =
      smallClassOf O hO L hL :=
  rfl

/-- Two invertible sheaves of modules determine the same small Picard class exactly when they
are isomorphic. -/
theorem smallClassOf_eq_smallClassOf_iff
    (L N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (hL : IsInvertible O hO L) (hN : IsInvertible O hO N) :
    smallClassOf O hO L hL = smallClassOf O hO N hN ↔ Nonempty (L ≅ N) :=
  ((smallPicardGroupAddEquiv O hO).symm.injective.eq_iff).trans
    (picardClass_eq_iff O hO L N hL hN)

/-- Addition of small Picard classes is tensor product of invertible sheaves of modules. -/
theorem smallClassOf_tensor (L N : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (hL : IsInvertible O hO L) (hN : IsInvertible O hO N)
    (hLN : IsInvertible O hO ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (L)).obj
        (N)))) :
    smallClassOf O hO L hL + smallClassOf O hO N hN =
      smallClassOf O hO ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (L)).obj (N))) hLN := by
  refine ((smallPicardGroupAddEquiv O hO).symm.map_add
    (picardClass O hO L hL) (picardClass O hO N hN)).symm.trans ?_
  exact congrArg _ (picardClass_tensorSheaf O hO L N hL hN hLN)

/-- Under `smallClassEquiv`, tensor product represents addition: the `classEquiv_tensor` field
of `Stacks.Picard.PicardGroupData`, at the smaller universe. -/
theorem smallClassEquiv_tensor (L N : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (hL : IsInvertible O hO L) (hN : IsInvertible O hO N)
    (hLN : IsInvertible O hO ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (L)).obj
        (N)))) :
    smallClassEquiv O hO (toSkeleton (C := InvertibleModules O hO) ⟨L, hL⟩) +
        smallClassEquiv O hO (toSkeleton (C := InvertibleModules O hO) ⟨N, hN⟩) =
      smallClassEquiv O hO (toSkeleton (C := InvertibleModules O hO)
        ⟨(((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
            (L)).obj (N)), hLN⟩) :=
  smallClassOf_tensor O hO L N hL hN hLN

end Site

section RingedSpace

/-- The Picard group of a ringed space, in `Type u`. -/
abbrev smallOfRingedSpace (X : RingedSpace.{u, u}) : Type u :=
  SmallPicardGroup X.presheaf (structureIsSheaf X)

/-- The Picard group of a scheme, in `Type u`. -/
abbrev smallOfScheme (X : Scheme.{u}) : Type u := smallOfRingedSpace X.toRingedSpace

variable {X Y Z : RingedSpace.{u, u}}

/-- Pullback on the small Picard groups of ringed spaces, as a homomorphism of abelian groups:
the pullback of `Stacks.Picard.pullbackClassHom` conjugated by
`Stacks.Picard.smallPicardGroupAddEquiv`. -/
def smallPullbackClassHom (f : X ⟶ Y) : smallOfRingedSpace Y →+ smallOfRingedSpace X :=
  ((smallPicardGroupAddEquiv X.presheaf (structureIsSheaf X)).symm.toAddMonoidHom.comp
    (pullbackClassHom f)).comp (smallPicardGroupAddEquiv Y.presheaf (structureIsSheaf Y))

/-- Under `smallPicardGroupAddEquiv`, small pullback corresponds to `pullbackClass`. -/
@[simp]
theorem smallPicardGroupAddEquiv_smallPullbackClassHom (f : X ⟶ Y) (x : smallOfRingedSpace Y) :
    smallPicardGroupAddEquiv X.presheaf (structureIsSheaf X) (smallPullbackClassHom f x) =
      pullbackClass f (smallPicardGroupAddEquiv Y.presheaf (structureIsSheaf Y) x) :=
  (smallPicardGroupAddEquiv X.presheaf (structureIsSheaf X)).apply_symm_apply _

/-- Small pullback sends `x` to `y` as soon as `pullbackClass` does after transport to the Picard
group. -/
private theorem smallPullbackClassHom_eq_of_pullbackClass_eq (f : X ⟶ Y) (x : smallOfRingedSpace Y)
    (y : smallOfRingedSpace X)
    (h : pullbackClass f (smallPicardGroupAddEquiv Y.presheaf (structureIsSheaf Y) x) =
      smallPicardGroupAddEquiv X.presheaf (structureIsSheaf X) y) :
    smallPullbackClassHom f x = y :=
  (smallPicardGroupAddEquiv X.presheaf (structureIsSheaf X)).injective
    ((smallPicardGroupAddEquiv_smallPullbackClassHom f x).trans h)

/-- Pullback on small Picard groups sends the small class of `L` to the small class of `f^*L`,
for any representative `L`. -/
theorem smallPullbackClass_classOf (f : X ⟶ Y)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf Y.presheaf
      (structureIsSheaf Y)))
    (hL : IsInvertible Y.presheaf (structureIsSheaf Y) L) :
    smallPullbackClassHom f (smallClassOf Y.presheaf (structureIsSheaf Y) L hL) =
      smallClassOf X.presheaf (structureIsSheaf X)
        ((Stacks.RingedSpace.pullbackFunctor f).obj L)
        (Stacks.RingedSpace.modulePullback_isInvertible_of f L hL) := by
  refine smallPullbackClassHom_eq_of_pullbackClass_eq f _ _ ?_
  rw [smallPicardGroupAddEquiv_smallClassOf]
  exact (pullbackClass_classOf f L hL).trans
    (smallPicardGroupAddEquiv_smallClassOf _ _ _ _).symm

/-- Pullback along the identity of a ringed space is the identity of its small Picard group. -/
@[simp]
theorem smallPullbackClassHom_id (X : RingedSpace.{u, u}) (x : smallOfRingedSpace X) :
    smallPullbackClassHom (𝟙 X) x = x :=
  smallPullbackClassHom_eq_of_pullbackClass_eq _ _ _ (pullbackClass_id X _)

/-- Pullback along a composite is pullback along `g` followed by pullback along `f`. -/
theorem smallPullbackClassHom_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : smallOfRingedSpace Z) :
    smallPullbackClassHom f (smallPullbackClassHom g x) = smallPullbackClassHom (f ≫ g) x := by
  refine smallPullbackClassHom_eq_of_pullbackClass_eq f _ _ ?_
  rw [smallPicardGroupAddEquiv_smallPullbackClassHom,
    smallPicardGroupAddEquiv_smallPullbackClassHom]
  exact pullbackClass_comp f g _

end RingedSpace

section Schemes

variable {X Y Z : Scheme.{u}}

/-- Pullback on the small Picard groups of schemes, as a homomorphism of abelian groups. -/
abbrev smallSchemePullbackClassHom (f : X ⟶ Y) : smallOfScheme Y →+ smallOfScheme X :=
  smallPullbackClassHom f.toLRSHom.toShHom

/-- Pullback along the identity of a scheme is the identity of its small Picard group. -/
@[simp]
theorem smallSchemePullbackClassHom_id (X : Scheme.{u}) (x : smallOfScheme X) :
    smallSchemePullbackClassHom (𝟙 X) x = x :=
  smallPullbackClassHom_id X.toRingedSpace x

/-- Pullback along a composite of morphisms of schemes is pullback along `g` followed by
pullback along `f`. -/
theorem smallSchemePullbackClassHom_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : smallOfScheme Z) :
    smallSchemePullbackClassHom f (smallSchemePullbackClassHom g x) =
      smallSchemePullbackClassHom (f ≫ g) x :=
  smallPullbackClassHom_comp f.toLRSHom.toShHom g.toLRSHom.toShHom x

end Schemes

end Stacks.Picard

end
