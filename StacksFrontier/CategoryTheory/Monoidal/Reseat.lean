module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Transport

/-!
# Re-seating a monoidal structure on a prescribed tensor bifunctor

A monoidal category structure on `C` determines its curried tensor product
`MonoidalCategory.curriedTensor C : C ⥤ C ⥤ C` and its unit `𝟙_ C`, but only as the particular
terms that were used to build the structure.  It happens that one has a monoidal structure on
`C` produced by a transport or localization argument, together with an *independently defined*
bifunctor `T : C ⥤ C ⥤ C` and object `U : C` which are isomorphic to that tensor product and
that unit.  Statements phrased in terms of `T` and `U` are then unavailable for the monoidal
structure one has, because `curriedTensor C` is a different term.

This file re-seats the structure: from `e : curriedTensor C ≅ T` and `ε : 𝟙_ C ≅ U` it builds a
new monoidal structure `reseat e ε` on `C` whose tensor product is `T` and whose unit is `U`
*definitionally*, so that `curriedTensor C = T` and `𝟙_ C = U` hold by `rfl`
(`curriedTensor_reseat`, `tensorUnit_reseat`).  The braiding, the symmetry, bilinearity of the
tensor product on morphisms, and preservation of colimits by the tensor functors are carried
along with it.

The mechanism is `CategoryTheory.Monoidal.induced` applied to the identity functor.  The data
part of the new structure is written out by hand from `e` and `ε`, in exactly the shape that
`Monoidal.InducingFunctorData` expects, so that its three coherence fields hold by `rfl` and
only the naturality of `e` has to be checked.

## Main definitions

* `CategoryTheory.MonoidalCategory.reseat`: the re-seated monoidal structure.
* `CategoryTheory.MonoidalCategory.reseatBraided`,
  `CategoryTheory.MonoidalCategory.reseatSymmetric`: its braiding and its symmetry.
* `CategoryTheory.MonoidalCategory.reseatMonoidalPreadditive`: bilinearity on morphisms.
* `CategoryTheory.MonoidalCategory.reseatClosed`: its internal hom.
* `CategoryTheory.MonoidalCategory.reseat_whiskerLeft'`,
  `CategoryTheory.MonoidalCategory.reseat_whiskerRight'`: the whiskerings of the given
  structure read off from `T`, which is how properties of `T` are fed back to the given
  structure.

## Main results

* `CategoryTheory.MonoidalCategory.curriedTensor_reseat`,
  `CategoryTheory.MonoidalCategory.tensorUnit_reseat`: the tensor product and the unit of the
  re-seated structure are the prescribed `T` and `U`.
* `CategoryTheory.MonoidalCategory.reseat_braiding` and
  `CategoryTheory.MonoidalCategory.reseat_braiding_aux`: **the braiding of the re-seated
  structure is the given braiding conjugated by `reseatIso`**, in the conjugated and in the
  comparison form.

## Implementation notes

`C` carries two monoidal structures throughout, the given one and the re-seated one, so no
declaration here may leave either to instance synthesis: the re-seated structure is always
named by `@`-application rather than by a local instance.  For the same reason the component
isomorphism `reseatIso` and the two whiskering identities `reseat_whiskerLeft`,
`reseat_whiskerRight` are stated using only the given structure and `T`; the fields of the
re-seated structure are definitionally equal to their right-hand sides.
-/

@[expose] public section

universe v u

namespace CategoryTheory.MonoidalCategory

open Category Limits

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {T : C ⥤ C ⥤ C} {U : C}

/-- The isomorphism `X ⊗ Y ≅ (T.obj X).obj Y` given by `e : curriedTensor C ≅ T`. -/
abbrev reseatIso (e : curriedTensor C ≅ T) (X Y : C) : X ⊗ Y ≅ (T.obj X).obj Y :=
  (e.app X).app Y

/-- `reseatIso` is natural in the second variable. -/
@[reassoc]
lemma reseatIso_naturality_right (e : curriedTensor C ≅ T) (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) :
    X ◁ g ≫ (reseatIso e X Y₂).hom = (reseatIso e X Y₁).hom ≫ (T.obj X).map g :=
  (e.app X).hom.naturality g

/-- `reseatIso` is natural in the first variable. -/
@[reassoc]
lemma reseatIso_naturality_left (e : curriedTensor C ≅ T) {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) :
    f ▷ Y ≫ (reseatIso e X₂ Y).hom = (reseatIso e X₁ Y).hom ≫ (T.map f).app Y :=
  NatTrans.naturality_app e.hom Y f

/-- The isomorphism `tensorRight Y ≅ T.flip.obj Y` given by `e`. -/
private def reseatTensorRightIso (e : curriedTensor C ≅ T) (Y : C) : tensorRight Y ≅ T.flip.obj Y :=
  NatIso.ofComponents (fun X ↦ reseatIso e X Y) fun f ↦ reseatIso_naturality_left e f Y

/-- Left whiskering for the re-seated structure, conjugated back to the given one. -/
lemma reseat_whiskerLeft (e : curriedTensor C ≅ T) (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) :
    (T.obj X).map g = (reseatIso e X Y₁).inv ≫ (X ◁ g) ≫ (reseatIso e X Y₂).hom := by
  rw [reseatIso_naturality_right e X g, Iso.inv_hom_id_assoc]

/-- Right whiskering for the re-seated structure, conjugated back to the given one. -/
lemma reseat_whiskerRight (e : curriedTensor C ≅ T) {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) :
    (T.map f).app Y = (reseatIso e X₁ Y).inv ≫ (f ▷ Y) ≫ (reseatIso e X₂ Y).hom := by
  rw [reseatIso_naturality_left e f Y, Iso.inv_hom_id_assoc]

/-- Left whiskering of the given structure, in terms of the re-seated one. -/
lemma reseat_whiskerLeft' (e : curriedTensor C ≅ T) (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) :
    X ◁ g = (reseatIso e X Y₁).hom ≫ (T.obj X).map g ≫ (reseatIso e X Y₂).inv := by
  rw [reseat_whiskerLeft e X g]
  simp

/-- Right whiskering of the given structure, in terms of the re-seated one. -/
lemma reseat_whiskerRight' (e : curriedTensor C ≅ T) {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) :
    f ▷ Y = (reseatIso e X₁ Y).hom ≫ (T.map f).app Y ≫ (reseatIso e X₂ Y).inv := by
  rw [reseat_whiskerRight e f Y]
  simp

/-- The data of the re-seated monoidal structure: the tensor product is `T`, the unit is `U`,
and the associator and the unitors are conjugated from those of the given structure.  The
shape of the associator and of the unitors is dictated by `Monoidal.InducingFunctorData`,
whose coherence fields then hold by `rfl`. -/
@[instance_reducible]
def reseatStruct (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) : MonoidalCategoryStruct C where
  tensorObj X Y := (T.obj X).obj Y
  whiskerLeft X _ _ g := (T.obj X).map g
  whiskerRight f Y := (T.map f).app Y
  tensorUnit := U
  associator X Y Z :=
    ((reseatIso e ((T.obj X).obj Y) Z).symm ≪≫ ((reseatIso e X Y).symm ⊗ᵢ Iso.refl Z)) ≪≫
      α_ X Y Z ≪≫ ((Iso.refl X ⊗ᵢ reseatIso e Y Z) ≪≫ reseatIso e X ((T.obj Y).obj Z))
  leftUnitor X := ((reseatIso e U X).symm ≪≫ (ε.symm ⊗ᵢ Iso.refl X)) ≪≫ λ_ X
  rightUnitor X := ((reseatIso e X U).symm ≪≫ (Iso.refl X ⊗ᵢ ε.symm)) ≪≫ ρ_ X

/-- The identity functor, from `C` with the re-seated structure to `C` with the given one,
preserves all the data of a monoidal structure.

The fields are supplied to the constructor by `@`-application rather than by `where`: the
structure-instance elaborator re-synthesizes the `MonoidalCategoryStruct C` argument, which
would silently pick the given structure in place of the re-seated one. -/
def reseatData (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) :
    @Monoidal.InducingFunctorData C _ _ C _ (reseatStruct e ε) (𝟭 C) :=
  @Monoidal.InducingFunctorData.mk C _ _ C _ (reseatStruct e ε) (𝟭 C) (reseatIso e)
    (fun X _ _ g ↦ reseat_whiskerLeft e X g) (fun f Y ↦ reseat_whiskerRight e f Y)
    (fun f g ↦ by
      change (T.map f).app _ ≫ (T.obj _).map g = _ ≫ (_ ⊗ₘ _) ≫ _
      rw [tensorHom_def, reseat_whiskerLeft e _ g, reseat_whiskerRight e f _]
      simp)
    ε (fun _ _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- **The re-seated monoidal structure**: a monoidal category structure on `C` whose tensor
product is the prescribed bifunctor `T` and whose unit is the prescribed object `U`. -/
@[instance_reducible]
def reseat (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) : MonoidalCategory C :=
  @Monoidal.induced C _ _ C _ (reseatStruct e ε) (𝟭 C) inferInstance (reseatData e ε)

/-- The identity functor, from `C` with the re-seated structure to `C` with the given one, is
a monoidal functor. -/
@[instance_reducible]
def reseatMonoidal (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) :
    @Functor.Monoidal C _ (reseat e ε) C _ _ (𝟭 C) :=
  @Functor.CoreMonoidal.toMonoidal C _ (reseat e ε) C _ _ (𝟭 C)
    (@Monoidal.fromInducedCoreMonoidal C _ _ C _ (reseatStruct e ε) (𝟭 C) inferInstance
      (reseatData e ε))

/-- The tensor product of the re-seated structure is the prescribed bifunctor. -/
lemma curriedTensor_reseat (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) :
    @curriedTensor C _ (reseat e ε) = T := rfl

/-- The unit of the re-seated structure is the prescribed object. -/
lemma tensorUnit_reseat (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) :
    @tensorUnit C _ (reseat e ε).toMonoidalCategoryStruct = U := rfl

/-- **The associativity constraint of the re-seated structure is the given one, conjugated by
`reseatIso`.**  Its three objects are read into the prescribed bifunctor `T` by the component
isomorphisms of `e` on the source and on the target, and in the middle it is the associator of
the given structure, untouched.

This is the identity that transfers a computation of the *given* associator to the prescribed
bifunctor.  It is needed where the given structure is produced by a localization — the
associator is then computed on the images of objects, and the statement one wants is about `T` —
and it is recorded here, in a bare monoidal context, rather than at any one such caller. -/
lemma reseat_associator (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) (X Y Z : C) :
    (@associator C _ (reseat e ε).toMonoidalCategoryStruct X Y Z).hom =
      ((reseatIso e ((T.obj X).obj Y) Z).inv ≫ ((reseatIso e X Y).inv ⊗ₘ 𝟙 Z)) ≫
        (α_ X Y Z).hom ≫ (𝟙 X ⊗ₘ (reseatIso e Y Z).hom) ≫
          (reseatIso e X ((T.obj Y).obj Z)).hom := rfl

/-- **A comparison compatible with the associativity constraint of the given structure is
compatible with that of the re-seated one.**

The setting is the one a localization produces: four isomorphisms identifying the four twofold
tensor products of `X`, `Y`, `Z` with prescribed objects, and a morphism `a : W ⟶ V` between the
two threefold ones — in practice the image of an associativity constraint upstairs — satisfying
the associativity clause for the given structure.  Composing each comparison with `reseatIso`
turns it into a comparison for the prescribed bifunctor `T`, and the clause for the re-seated
associator holds with the *same* `a`.

The hypothesis and the conclusion differ only by where the two whiskerings and the associator
are taken, so the whole content is `reseat_whiskerLeft`, `reseat_whiskerRight` and
`reseat_associator`.  It is stated here, over an abstract bifunctor, because a caller whose
category is a derived category pays the `isDefEq` cost of each of those rewrites at objects for
which it is not cheap. -/
lemma reseat_associativity (e : curriedTensor C ≅ T) {X Y Z P Q W V : C}
    (cXY : X ⊗ Y ≅ P) (cPZ : P ⊗ Z ≅ W) (cYZ : Y ⊗ Z ≅ Q) (cXQ : X ⊗ Q ≅ V) {a : W ⟶ V}
    {α' : (T.obj ((T.obj X).obj Y)).obj Z ⟶ (T.obj X).obj ((T.obj Y).obj Z)}
    (hα : α' =
      ((reseatIso e ((T.obj X).obj Y) Z).inv ≫ ((reseatIso e X Y).inv ⊗ₘ 𝟙 Z)) ≫
        (α_ X Y Z).hom ≫ (𝟙 X ⊗ₘ (reseatIso e Y Z).hom) ≫
          (reseatIso e X ((T.obj Y).obj Z)).hom)
    (h : cXY.hom ▷ Z ≫ cPZ.hom ≫ a = (α_ X Y Z).hom ≫ X ◁ cYZ.hom ≫ cXQ.hom) :
    (T.map ((reseatIso e X Y).symm ≪≫ cXY).hom).app Z ≫
        ((reseatIso e P Z).symm ≪≫ cPZ).hom ≫ a =
      α' ≫ (T.obj X).map ((reseatIso e Y Z).symm ≪≫ cYZ).hom ≫
        ((reseatIso e X Q).symm ≪≫ cXQ).hom := by
  subst hα
  rw [reseat_whiskerRight e, reseat_whiskerLeft e]
  simp only [Iso.trans_hom, Iso.symm_hom, assoc, Iso.hom_inv_id_assoc, tensorHom_id,
    id_tensorHom, comp_whiskerRight, whiskerLeft_comp,
    whiskerLeft_hom_inv_assoc]
  rw [h]

/-- The re-seated structure is braided whenever the given one is. -/
@[instance_reducible]
noncomputable def reseatBraided [BraidedCategory C] (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) :
    @BraidedCategory C _ (reseat e ε) :=
  @BraidedCategory.ofFullyFaithful C C _ _ (reseat e ε) _ (𝟭 C) (reseatMonoidal e ε)
    inferInstance inferInstance _

/-- The re-seated structure is symmetric whenever the given one is. -/
@[instance_reducible]
noncomputable def reseatSymmetric [SymmetricCategory C] (e : curriedTensor C ≅ T)
    (ε : 𝟙_ C ≅ U) :
    @SymmetricCategory C _ (reseat e ε) :=
  @SymmetricCategory.ofFullyFaithful C C _ _ (reseat e ε) _ (𝟭 C) (reseatMonoidal e ε)
    inferInstance inferInstance _

/-- The re-seated tensor product is bilinear on morphisms whenever the given one is. -/
lemma reseatMonoidalPreadditive [Preadditive C] [MonoidalPreadditive C] (e : curriedTensor C ≅ T)
    (ε : 𝟙_ C ≅ U) :
    @MonoidalPreadditive C _ _ (reseat e ε) :=
  have (X : C) : (T.obj X).Additive := Functor.additive_of_iso (e.app X)
  have (X : C) : (T.flip.obj X).Additive :=
    Functor.additive_of_iso (reseatTensorRightIso e X)
  @MonoidalPreadditive.mk C _ _ (reseat e ε)
    (fun {X Y Z} ↦ Functor.map_zero (T.obj X) Y Z)
    (fun {X Y Z} ↦ Functor.map_zero (T.flip.obj X) Y Z)
    (fun {X _ _} _ _ ↦ Functor.map_add (T.obj X))
    (fun {X _ _} _ _ ↦ Functor.map_add (T.flip.obj X))

/-- The re-seated structure is monoidal closed whenever the given one is: the internal hom is
unchanged, and the adjunction is transported along `e`. -/
@[instance_reducible]
noncomputable def reseatClosed [MonoidalClosed C] (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) :
    @MonoidalClosed C _ (reseat e ε) :=
  @MonoidalClosed.mk C _ (reseat e ε) (fun X ↦
    @Closed.mk C _ (reseat e ε) X (_root_.CategoryTheory.ihom X)
      ((_root_.CategoryTheory.ihom.adjunction X).ofNatIsoLeft (e.app X)))

/-- Re-seating changes the tensor product but retains the chosen internal-Hom functor. -/
lemma ihom_reseatClosed [MonoidalClosed C] (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U)
    (X : C) :
    @CategoryTheory.ihom C _ (reseat e ε) X
        (@MonoidalClosed.closed C _ (reseat e ε) (reseatClosed e ε) X) =
      CategoryTheory.ihom X := rfl

/-- Tensoring on the left by a fixed object preserves a colimit for the re-seated structure as
soon as it does for the given one. -/
lemma reseatPreservesColimit_tensorLeft (e : curriedTensor C ≅ T) {K : Type*} [Category K]
    (F : K ⥤ C) (X : C) [PreservesColimit F (tensorLeft X)] :
    PreservesColimit F (T.obj X) :=
  preservesColimit_of_natIso _ (e.app X)

/-- Tensoring on the right by a fixed object preserves a colimit for the re-seated structure
as soon as it does for the given one. -/
lemma reseatPreservesColimit_tensorRight (e : curriedTensor C ≅ T) {K : Type*} [Category K]
    (F : K ⥤ C) (Y : C) [PreservesColimit F (tensorRight Y)] :
    PreservesColimit F (T.flip.obj Y) :=
  preservesColimit_of_natIso _ (reseatTensorRightIso e Y)

end CategoryTheory.MonoidalCategory

end
