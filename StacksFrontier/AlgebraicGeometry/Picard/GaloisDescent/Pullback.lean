module

public import Mathlib.AlgebraicGeometry.Scheme
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.Group
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pullback on Picard groups

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces. The pullback of an invertible
sheaf of `𝒪_Y`-modules is an invertible sheaf of `𝒪_X`-modules (Tag 0B8L), so `f` induces a map
`f^* : Pic(Y) → Pic(X)` on Picard groups (Tag 01CX): represent a class by an invertible module,
pull that module back, and take its class. The representative is the one chosen by the skeleton
underlying the Picard group, so the map is a genuine function and not merely a relation, and
`Stacks.Picard.pullbackClass_classOf` says that it sends the class of `L` to the class of `f^*L`
whichever representative `L` is used.

The map is a homomorphism because pullback commutes with the tensor product (Tag 01CD) and
addition of Picard classes *is* the tensor product; it is functorial because pullback of sheaves
of modules is, being an adjoint. Both facts are proved here by the same two-step argument: move
the identity onto representatives with `pullbackClass_classOf`, then exhibit an isomorphism of
invertible modules and appeal to `Stacks.SheafOfModules.picardClass_eq_iff`, under which
equality of Picard classes is isomorphism of invertible modules.

## Main definitions

* `Stacks.RingedSpace.structureIsSheaf` — the structure sheaf of a ringed space read as a sheaf
  of not-necessarily-commutative rings, in the form the Picard group of Tag 01CX takes.
* `Stacks.Picard.ofRingedSpace` — the Picard group of a ringed space.
* `Stacks.Picard.ofScheme` — the Picard group of a scheme.
* `Stacks.Picard.picardRepresentative` — the invertible module chosen to represent a class.
* `Stacks.Picard.pullbackClass` — the pullback map on Picard groups.
* `Stacks.Picard.pullbackClassHom` — the same map, as a homomorphism of abelian groups.
* `Stacks.Picard.schemePullbackClass`, `Stacks.Picard.schemePullbackClassHom` — the same for a
  morphism of schemes.

## Main results

* `Stacks.Picard.pullbackClass_classOf` — pullback sends the class of `L` to the class of `f^*L`.
* `Stacks.Picard.pullbackClass_add` — pullback is additive.
* `Stacks.Picard.pullbackClass_id` — pullback along the identity is the identity.
* `Stacks.Picard.pullbackClass_comp` — pullback along `f ≫ g` is `g^*` followed by `f^*`.
* `Stacks.Picard.schemePullbackClass_add`, `Stacks.Picard.schemePullbackClass_id`,
  `Stacks.Picard.schemePullbackClass_comp` — the same three for a morphism of schemes.

## Implementation notes

No `@[stacks]` attribute is attached. The additivity of pullback is the "homomorphism property"
clause of Tag 0B9N, whose other six clauses concern the relative Picard functor and are not
proved here; and nothing in this file is the content of Tag 01CX, 0B8L or 01CD, all three of
which are already tagged where they are proved.

## References

* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0B9N](https://stacks.math.columbia.edu/tag/0B9N)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

open Stacks.SheafOfModules (IsInvertible InvertibleModules PicardGroup isInvertible_tensorSheaf
  picardClass picardClass_eq_iff picardClass_tensorSheaf)

open RingedSpaceModuleAdjunction (modulePullback structureSheafHom modulePushforward_isRightAdjoint)

open Stacks.RingedSpace (pullbackFunctor)

universe u

namespace Stacks.RingedSpace

/-- The structure sheaf of a ringed space, read as a sheaf of (not necessarily commutative)
rings: the sheaf condition in the form that the Picard group of Tag 01CX takes. -/
abbrev structureIsSheaf (X : RingedSpace.{u, u}) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X.carrier)
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf X.presheaf) :=
  Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf

/-- Tag 0B8L with invertibility of `L` taken as an ordinary hypothesis rather than as an
instance, which is the form needed when the hypothesis comes from a bundled Picard class. -/
theorem modulePullback_isInvertible_of {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf Y.presheaf
      (structureIsSheaf Y)))
    (hL : IsInvertible Y.presheaf (structureIsSheaf Y) L) :
    IsInvertible X.presheaf (structureIsSheaf X) ((pullbackFunctor f).obj L) :=
  @modulePullback_isInvertible X Y f L hL

end Stacks.RingedSpace

namespace Stacks.Picard

open Stacks.RingedSpace (structureIsSheaf modulePullback_isInvertible_of comparisonBifunctorIso
  pullbackFunctor)

/-- The Picard group of a ringed space: the abelian group of isomorphism classes of invertible
sheaves of `𝒪_X`-modules under tensor product. -/
abbrev ofRingedSpace (X : RingedSpace.{u, u}) : Type (u + 1) :=
  PicardGroup X.presheaf (structureIsSheaf X)

/-- The Picard group of a scheme. -/
abbrev ofScheme (X : Scheme.{u}) : Type (u + 1) := ofRingedSpace X.toRingedSpace

variable {X Y Z : RingedSpace.{u, u}}

/-- The invertible sheaf of modules representing a Picard class: the object that the skeleton
of the category of invertible modules chooses in the isomorphism class. -/
def picardRepresentative (X : RingedSpace.{u, u}) (x : ofRingedSpace X) :
    InvertibleModules X.presheaf (structureIsSheaf X) :=
  (fromSkeleton (InvertibleModules X.presheaf (structureIsSheaf X))).obj
    ((picardGroupData X.presheaf (structureIsSheaf X)).classEquiv.symm x)

/-- The chosen representative of a Picard class does represent it. -/
@[simp]
theorem classOf_picardRepresentative (X : RingedSpace.{u, u}) (x : ofRingedSpace X) :
    picardClass X.presheaf (structureIsSheaf X) (picardRepresentative X x).obj
      (picardRepresentative X x).property = x := by
  change (picardGroupData X.presheaf (structureIsSheaf X)).classEquiv
    (toSkeleton (C := InvertibleModules X.presheaf (structureIsSheaf X))
      ((fromSkeleton (InvertibleModules X.presheaf (structureIsSheaf X))).obj
        ((picardGroupData X.presheaf (structureIsSheaf X)).classEquiv.symm x))) = x
  rw [CategoryTheory.toSkeleton_fromSkeleton_obj]
  exact Equiv.apply_symm_apply _ _

/-- **Pullback on Picard groups.** The class of an invertible sheaf of `𝒪_Y`-modules is sent to
the class of its pullback along `f`, which is invertible by Tag 0B8L. -/
@[ega "0 5.4.8" "more general"]
def pullbackClass (f : X ⟶ Y) : ofRingedSpace Y → ofRingedSpace X := fun x ↦
  picardClass X.presheaf (structureIsSheaf X)
    ((pullbackFunctor f).obj (picardRepresentative Y x).obj)
    (modulePullback_isInvertible_of f _ (picardRepresentative Y x).property)

/-- Pullback on Picard groups is computed on any representative, not only on the chosen one:
the class of `L` goes to the class of `f^*L`. -/
theorem pullbackClass_classOf (f : X ⟶ Y)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf Y.presheaf
      (structureIsSheaf Y)))
    (hL : IsInvertible Y.presheaf (structureIsSheaf Y) L) :
    pullbackClass f (picardClass Y.presheaf (structureIsSheaf Y) L hL) =
      picardClass X.presheaf (structureIsSheaf X) ((pullbackFunctor f).obj L)
        (modulePullback_isInvertible_of f L hL) := by
  refine (picardClass_eq_iff _ _ _ _ _ _).2 ⟨(pullbackFunctor f).mapIso ?_⟩
  exact ((picardClass_eq_iff _ _ _ _ _ _).1
    (classOf_picardRepresentative Y (picardClass Y.presheaf (structureIsSheaf Y) L hL))).some

/-- Pullback of a class is the class of any invertible module isomorphic to the pullback of the
chosen representative. -/
private theorem pullbackClass_eq_picardClass_of_iso (f : X ⟶ Y) (x : ofRingedSpace Y)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf
      (structureIsSheaf X)))
    (hM : IsInvertible X.presheaf (structureIsSheaf X) M)
    (e : (pullbackFunctor f).obj (picardRepresentative Y x).obj ≅ M) :
    pullbackClass f x = picardClass X.presheaf (structureIsSheaf X) M hM :=
  (picardClass_eq_iff _ _ _ _ _ _).2 ⟨e⟩

/-- Pullback on Picard groups is additive: addition of classes is the tensor product, and
pullback commutes with the tensor product by Tag 01CD. -/
theorem pullbackClass_add (f : X ⟶ Y) (x y : ofRingedSpace Y) :
    pullbackClass f (x + y) = pullbackClass f x + pullbackClass f y := by
  have hLinv : IsInvertible Y.presheaf (structureIsSheaf Y) (picardRepresentative Y x).obj :=
    (picardRepresentative Y x).property
  have hNinv : IsInvertible Y.presheaf (structureIsSheaf Y) (picardRepresentative Y y).obj :=
    (picardRepresentative Y y).property
  have hfL := modulePullback_isInvertible_of f (picardRepresentative Y x).obj hLinv
  have hfN := modulePullback_isInvertible_of f (picardRepresentative Y y).obj hNinv
  have hLN := @isInvertible_tensorSheaf _ _ _ Y.presheaf (structureIsSheaf Y) _ _ _ _ hLinv hNinv
  have hfLN := @isInvertible_tensorSheaf _ _ _ X.presheaf (structureIsSheaf X) _ _ _ _ hfL hfN
  rw [← classOf_picardRepresentative Y x, ← classOf_picardRepresentative Y y,
    picardClass_tensorSheaf _ _ (picardRepresentative Y x).obj (picardRepresentative Y y).obj
      (picardRepresentative Y x).property (picardRepresentative Y y).property hLN,
    pullbackClass_classOf f (picardRepresentative Y x).obj,
    pullbackClass_classOf f (picardRepresentative Y y).obj,
    pullbackClass_classOf f ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (Y.presheaf) (forget₂ CommRingCat RingCat)
        ((structureIsSheaf Y))⟩).obj ((picardRepresentative Y x).obj)).obj
          ((picardRepresentative Y y).obj)))]
  exact Eq.trans
    ((picardClass_eq_iff _ _ _ _ _ hfLN).2
      ⟨(comparisonBifunctorIso f).app
        ((picardRepresentative Y x).obj, (picardRepresentative Y y).obj)⟩)
    (picardClass_tensorSheaf X.presheaf (structureIsSheaf X)
      ((pullbackFunctor f).obj (picardRepresentative Y x).obj)
      ((pullbackFunctor f).obj (picardRepresentative Y y).obj) hfL hfN hfLN).symm

/-- **Pullback on Picard groups, as a homomorphism of abelian groups.** -/
def pullbackClassHom (f : X ⟶ Y) : ofRingedSpace Y →+ ofRingedSpace X :=
  AddMonoidHom.mk' (pullbackClass f) (pullbackClass_add f)

/-- The homomorphism `pullbackClassHom f` evaluates as the map `pullbackClass f`. -/
@[simp]
theorem pullbackClassHom_apply (f : X ⟶ Y) (x : ofRingedSpace Y) :
    pullbackClassHom f x = pullbackClass f x := rfl

/-- Pullback along the identity is the identity of the Picard group. -/
@[simp]
theorem pullbackClass_id (X : RingedSpace.{u, u}) (x : ofRingedSpace X) :
    pullbackClass (𝟙 X) x = x := by
  have e : modulePullback (𝟙 X) ≅ 𝟭 (SheafOfModules.{u} (structureSheafRing X)) :=
    let : (SheafOfModules.pushforward (structureSheafHom (𝟙 X))).IsRightAdjoint :=
      modulePushforward_isRightAdjoint (𝟙 X)
    SheafOfModules.pullbackId (structureSheafRing X)
  exact (pullbackClass_eq_picardClass_of_iso _ x _ _ (e.app _)).trans
    (classOf_picardRepresentative X x)

/-- Pullback along a composite is pullback along `g` followed by pullback along `f`. -/
theorem pullbackClass_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : ofRingedSpace Z) :
    pullbackClass f (pullbackClass g x) = pullbackClass (f ≫ g) x := by
  have e : modulePullback g ⋙ modulePullback f ≅ modulePullback (f ≫ g) :=
    let : (SheafOfModules.pushforward (structureSheafHom f)).IsRightAdjoint :=
      modulePushforward_isRightAdjoint f
    let : (SheafOfModules.pushforward (structureSheafHom g)).IsRightAdjoint :=
      modulePushforward_isRightAdjoint g
    let : (SheafOfModules.pushforward (structureSheafHom (f ≫ g))).IsRightAdjoint :=
      modulePushforward_isRightAdjoint (f ≫ g)
    SheafOfModules.pullbackComp (structureSheafHom g) (structureSheafHom f)
  exact (pullbackClass_classOf f _ _).trans
    (pullbackClass_eq_picardClass_of_iso (f ≫ g) x _ _ (e.symm.app _)).symm

section Schemes

variable {X Y Z : Scheme.{u}}

/-- **Pullback on the Picard groups of schemes**, read off the underlying morphism of ringed
spaces. -/
abbrev schemePullbackClass (f : X ⟶ Y) : ofScheme Y → ofScheme X :=
  pullbackClass f.toLRSHom.toShHom

/-- Pullback on the Picard groups of schemes, as a homomorphism of abelian groups. -/
abbrev schemePullbackClassHom (f : X ⟶ Y) : ofScheme Y →+ ofScheme X :=
  pullbackClassHom f.toLRSHom.toShHom

/-- Pullback on the Picard groups of schemes is additive. -/
theorem schemePullbackClass_add (f : X ⟶ Y) (x y : ofScheme Y) :
    schemePullbackClass f (x + y) = schemePullbackClass f x + schemePullbackClass f y :=
  pullbackClass_add f.toLRSHom.toShHom x y

/-- Pullback along the identity of a scheme is the identity of its Picard group. -/
@[simp]
theorem schemePullbackClass_id (X : Scheme.{u}) (x : ofScheme X) :
    schemePullbackClass (𝟙 X) x = x :=
  pullbackClass_id X.toRingedSpace x

/-- Pullback along a composite of morphisms of schemes is pullback along `g` followed by
pullback along `f`. -/
theorem schemePullbackClass_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : ofScheme Z) :
    schemePullbackClass f (schemePullbackClass g x) = schemePullbackClass (f ≫ g) x :=
  pullbackClass_comp f.toLRSHom.toShHom g.toLRSHom.toShHom x

end Schemes

end Stacks.Picard

end
