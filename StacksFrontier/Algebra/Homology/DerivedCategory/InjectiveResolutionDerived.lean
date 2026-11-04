module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import StacksCore.Tactic.StacksAttribute

/-! # The right derived functor evaluated on an injective resolution

Let `G : C ⥤ D` be an additive functor between abelian categories with `C` having enough
injectives, and let `J` be an injective resolution of an object `X` of `C`. Applying `G`
degreewise to `J` and passing to the derived category computes `RG` at `X`: this file builds the
comparison morphism `G(J^•) ⟶ RG(X[0])` in `D(D)`, shows that it is an isomorphism, and proves
that it is natural in the pair consisting of a morphism of `C` and a morphism of injective
resolutions above it.

This is Stacks 05TN specialised to the bounded-below derived category. Mathlib's
`CategoryTheory.Functor.rightDerivedFunctorPlusUnit` is already invertible on complexes of
injective objects; what is added here is the identification of its source with the
derived-category image of `G(J^•)`, together with the naturality statement in the form needed to
compare two injective resolutions of the same object.

## Main definitions

* `DerivedCategory.Plus.qhQIso`: the comparison between the two descriptions of the
  bounded-below derived-category image of a bounded-below cochain complex.
* `CategoryTheory.InjectiveResolution.plusObj`: the resolution as a bounded-below complex.
* `CategoryTheory.InjectiveResolution.inclusionZero`: the map `X ⟶ J^0`.
* `CategoryTheory.InjectiveResolution.plusQIso`: the isomorphism `X[0] ≅ J^•` in `D⁺(C)`.
* `CategoryTheory.InjectiveResolution.homOfDesc`: the descent of a morphism to chosen injective
  resolutions, as a morphism of injective resolutions.
* `CategoryTheory.InjectiveResolution.toRightDerived`: the comparison `G(J^•) ⟶ RG(X[0])`.

## Main results

* `CategoryTheory.InjectiveResolution.isIso_toRightDerived`: the comparison is an isomorphism.
* `CategoryTheory.InjectiveResolution.toRightDerived_naturality`: a morphism of injective
  resolutions above `f : X ⟶ Y` makes the comparisons for the two resolutions into a commutative
  square with `RG(f[0])`.
* `CategoryTheory.InjectiveResolution.inclusionZero_comp_hom'_f_zero`: the maps `X ⟶ J^0` are
  compatible with a morphism of injective resolutions.

## Implementation notes

The comparison is spelled as a morphism between the *underlying* objects of `DerivedCategory D`
rather than of the full subcategory `DerivedCategory.Plus D`, because its source is the image of
a plain cochain complex under `DerivedCategory.Q`. It is built from a morphism
`toRightDerivedPlus` of the full subcategory, where the naturality argument takes place; the two
differ by the comparison `DerivedCategory.quotientCompQhIso` and the forgetful functor, and
`toRightDerived_eq` records that the result is the four-fold composite one writes down by hand.

Naturality is stated for a `CategoryTheory.InjectiveResolution.Hom`, that is for a chosen
morphism of resolutions above `f`, rather than for the descent produced by
`CategoryTheory.InjectiveResolution.desc`: this is the form in which two resolutions of one
object are compared, where `f` is the identity and the morphism of resolutions is a descent of
it.

## References

* [Stacks Project, Tag 05TN](https://stacks.math.columbia.edu/tag/05TN)
-/

@[expose] public noncomputable section

universe v v' u u'

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory.Plus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- The bounded-below derived-category image of a bounded-below cochain complex, computed either
through the bounded-below homotopy category or directly. -/
def qhQIso (L : CochainComplex.Plus C) :
    Qh.obj ((HomotopyCategory.Plus.quotient C).obj L) ≅ Q.obj L :=
  ObjectProperty.isoMk _ ((DerivedCategory.quotientCompQhIso C).app L.obj)

/-- The underlying morphism of the comparison is the component of `quotientCompQhIso`. -/
@[simp]
lemma qhQIso_hom_hom (L : CochainComplex.Plus C) :
    (qhQIso L).hom.hom = (DerivedCategory.quotientCompQhIso C).hom.app L.obj :=
  rfl

/-- The underlying morphism of the image of a morphism under `Q`. -/
@[simp]
lemma Q_map_hom {L L' : CochainComplex.Plus C} (h : L ⟶ L') :
    (Q.map h).hom = DerivedCategory.Q.map h.hom :=
  rfl

/-- The underlying morphism of the image of a morphism under `Qh`. -/
@[simp]
lemma Qh_map_hom {L L' : HomotopyCategory.Plus C} (h : L ⟶ L') :
    (Qh.map h).hom = DerivedCategory.Qh.map h.hom :=
  rfl

/-- The underlying morphism of the image of a morphism under a single functor. -/
@[simp]
lemma singleFunctor_map_hom (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    ((singleFunctor C n).map f).hom =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor C n).map f) :=
  rfl

/-- The comparison between the two descriptions of the derived category is natural. -/
@[reassoc]
lemma qhQIso_naturality {L L' : CochainComplex.Plus C} (h : L ⟶ L') :
    Qh.map ((HomotopyCategory.Plus.quotient C).map h) ≫ (qhQIso L').hom =
      (qhQIso L).hom ≫ Q.map h :=
  ObjectProperty.hom_ext _ (DerivedCategory.quotientCompQhIso_hom_naturality h.hom)

end DerivedCategory.Plus

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- The bounded-below cochain complex underlying an injective resolution. -/
abbrev plusObj {X : C} (J : InjectiveResolution X) : CochainComplex.Plus C :=
  ⟨J.cochainComplex, 0, inferInstance⟩

/-- The inclusion of an object into the degree-zero term of an injective resolution. -/
def inclusionZero {X : C} (J : InjectiveResolution X) : X ⟶ J.cochainComplex.X 0 :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫ J.ι'.f 0

omit [HasDerivedCategory C] in
/-- The inclusion into the degree-zero term of a resolution is killed by the differential. -/
@[reassoc (attr := simp)]
lemma inclusionZero_comp_d {X : C} (J : InjectiveResolution X) :
    J.inclusionZero ≫ J.cochainComplex.d 0 1 = 0 := by
  dsimp only [inclusionZero]
  rw [Category.assoc, J.ι'.comm 0 1]
  simp

omit [HasDerivedCategory C] in
/-- The inclusions into the degree-zero terms are compatible with a morphism of injective
resolutions. -/
@[reassoc]
lemma inclusionZero_comp_hom'_f_zero {X Y : C} {f : X ⟶ Y} {J : InjectiveResolution X}
    {J' : InjectiveResolution Y} (φ : InjectiveResolution.Hom J J' f) :
    J.inclusionZero ≫ φ.hom'.f 0 = f ≫ J'.inclusionZero := by
  have h := congrArg (fun g ↦ HomologicalComplex.Hom.f g 0) φ.ι'_comp_hom'
  simp only [HomologicalComplex.comp_f] at h
  have hs : ((CochainComplex.singleFunctor C 0).map f).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom ≫ f ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y).inv :=
    HomologicalComplex.single_map_f_self (ComplexShape.up ℤ) 0 f
  rw [hs] at h
  dsimp only [inclusionZero]
  rw [Category.assoc, h]
  simp

/-- An injective resolution identifies its object, placed in degree zero, with the resolution
itself, as objects of the bounded-below derived category. -/
def plusQIso {X : C} (J : InjectiveResolution X) :
    (DerivedCategory.Plus.singleFunctor C 0).obj X ≅
      DerivedCategory.Plus.Q.obj J.plusObj :=
  haveI : QuasiIso J.ι' := inferInstance
  haveI : IsIso (DerivedCategory.Q.map J.ι') :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso C J.ι').2 inferInstance
  let e := @asIso _ _ _ _ (DerivedCategory.Q.map J.ι') inferInstance
  ObjectProperty.isoMk _ e

/-- The underlying morphism of `plusQIso` is the image of the resolution's quasi-isomorphism. -/
@[simp]
lemma plusQIso_hom_hom {X : C} (J : InjectiveResolution X) :
    J.plusQIso.hom.hom = DerivedCategory.Q.map J.ι' :=
  rfl

/-- The descent of a morphism to chosen injective resolutions, as a morphism of injective
resolutions. -/
def homOfDesc [EnoughInjectives C] {X Y : C} (f : X ⟶ Y) (J : InjectiveResolution X)
    (J' : InjectiveResolution Y) : InjectiveResolution.Hom J J' f where
  hom := InjectiveResolution.desc f J' J
  ι_f_zero_comp_hom_f_zero :=
    congrArg (fun h ↦ HomologicalComplex.Hom.f h 0) (InjectiveResolution.desc_commutes f J' J)

/-- A morphism of injective resolutions, as a morphism of bounded-below complexes. -/
abbrev Hom.plusHom {X Y : C} {f : X ⟶ Y} {J : InjectiveResolution X}
    {J' : InjectiveResolution Y} (φ : InjectiveResolution.Hom J J' f) :
    J.plusObj ⟶ J'.plusObj :=
  ObjectProperty.homMk φ.hom'

/-- A morphism of injective resolutions above `f` turns the identifications of the resolutions
with the objects they resolve into a commutative square. -/
@[reassoc]
lemma plusQIso_naturality {X Y : C} {f : X ⟶ Y} {J : InjectiveResolution X}
    {J' : InjectiveResolution Y} (φ : InjectiveResolution.Hom J J' f) :
    (DerivedCategory.Plus.singleFunctor C 0).map f ≫ J'.plusQIso.hom =
      J.plusQIso.hom ≫ DerivedCategory.Plus.Q.map φ.plusHom := by
  apply ObjectProperty.hom_ext
  have h := DerivedCategory.Q.congr_map φ.ι'_comp_hom'
  simp only [Functor.map_comp] at h
  exact h.symm

/-- The inverse comparison is natural: a morphism of injective resolutions above `f` turns the
identification of each resolution with the object it resolves into a commutative square. -/
@[reassoc]
lemma plusQIso_inv_naturality {X Y : C} {f : X ⟶ Y} {J : InjectiveResolution X}
    {J' : InjectiveResolution Y} (φ : InjectiveResolution.Hom J J' f) :
    DerivedCategory.Plus.Q.map φ.plusHom ≫ J'.plusQIso.inv =
      J.plusQIso.inv ≫ (DerivedCategory.Plus.singleFunctor C 0).map f := by
  rw [← cancel_epi J.plusQIso.hom, ← Category.assoc, ← plusQIso_naturality φ]
  simp

variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory D]
  (G : C ⥤ D) [G.Additive] [EnoughInjectives C]

/-- The comparison, inside the bounded-below derived category, between the image of an injective
resolution of `X` under `G` and the value at `X` of the right derived functor of `G`. -/
def toRightDerivedPlus {X : C} (J : InjectiveResolution X) :
    DerivedCategory.Plus.Qh.obj (G.mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient C).obj J.plusObj)) ⟶
      G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj X) :=
  G.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj J.plusObj) ≫
    G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.qhQIso J.plusObj).hom ≫
    G.rightDerivedFunctorPlus.map J.plusQIso.inv

/-- The comparison inside the bounded-below derived category is an isomorphism. -/
instance isIso_toRightDerivedPlus {X : C} (J : InjectiveResolution X) :
    IsIso (toRightDerivedPlus G J) := by
  dsimp only [toRightDerivedPlus]
  infer_instance

/-- A morphism of injective resolutions above `f` turns the comparisons inside the bounded-below
derived category into a commutative square with `RG(f[0])`. -/
@[reassoc]
lemma toRightDerivedPlus_naturality {X Y : C} {f : X ⟶ Y} {J : InjectiveResolution X}
    {J' : InjectiveResolution Y} (φ : InjectiveResolution.Hom J J' f) :
    DerivedCategory.Plus.Qh.map (G.mapHomotopyCategoryPlus.map
        ((HomotopyCategory.Plus.quotient C).map φ.plusHom)) ≫ toRightDerivedPlus G J' =
      toRightDerivedPlus G J ≫
        G.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map f) := by
  have hn := G.rightDerivedFunctorPlusUnit.naturality
    ((HomotopyCategory.Plus.quotient C).map φ.plusHom)
  dsimp only [Functor.comp_map] at hn
  dsimp only [toRightDerivedPlus]
  rw [← Category.assoc, ← Category.assoc, hn]
  simp only [Category.assoc, ← Functor.map_comp]
  congr 2
  rw [DerivedCategory.Plus.qhQIso_naturality_assoc, plusQIso_inv_naturality φ]

/-- The comparison between the derived-category image of `G(J^•)` and the image, under `Qh`, of
its class in the bounded-below homotopy category. -/
def toQhPlus {X : C} (J : InjectiveResolution X) :
    DerivedCategory.Q.obj
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj J.cochainComplex) ⟶
      (DerivedCategory.Plus.Qh.obj (G.mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient C).obj J.plusObj))).obj :=
  (DerivedCategory.quotientCompQhIso D).inv.app _

/-- The comparison morphism from the derived-category image of `G` applied degreewise to an
injective resolution of `X` to the value at `X` of the right derived functor of `G`. -/
def toRightDerived {X : C} (J : InjectiveResolution X) :
    DerivedCategory.Q.obj
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj J.cochainComplex) ⟶
      (G.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor C 0).obj X)).obj :=
  toQhPlus G J ≫ (toRightDerivedPlus G J).hom

/-- The comparison morphism, written out as the composite of the comparison between the two
descriptions of the derived category, the unit of the right derived functor, and the
identification of the resolution with the object it resolves. -/
lemma toRightDerived_eq {X : C} (J : InjectiveResolution X) :
    J.toRightDerived G =
      (DerivedCategory.quotientCompQhIso D).inv.app _ ≫
      (G.rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.quotient C).obj J.plusObj)).hom ≫
      (G.rightDerivedFunctorPlus.map (ObjectProperty.homMk
        ((DerivedCategory.quotientCompQhIso C).hom.app J.cochainComplex))).hom ≫
      (G.rightDerivedFunctorPlus.mapIso J.plusQIso).inv.hom :=
  rfl

/-- The comparison morphism of `toRightDerived`, as an isomorphism. -/
def toRightDerivedIso {X : C} (J : InjectiveResolution X) :
    DerivedCategory.Q.obj
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj J.cochainComplex) ≅
      (G.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor C 0).obj X)).obj :=
  ((DerivedCategory.quotientCompQhIso D).app
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj J.cochainComplex)).symm ≪≫
    (ObjectProperty.ι _).mapIso (asIso (toRightDerivedPlus G J))

/-- The comparison `G(J^•) ⟶ RG(X[0])` is an isomorphism. -/
instance isIso_toRightDerived {X : C} (J : InjectiveResolution X) :
    IsIso (J.toRightDerived G) :=
  (toRightDerivedIso G J).isIso_hom

omit [HasDerivedCategory C] [EnoughInjectives C] in
/-- The underlying morphism of the image under `Qh` of a morphism of injective resolutions is the
image under `Qh` of the degreewise application of `G` to it. -/
lemma Qh_map_mapHomotopyCategoryPlus_hom {X Y : C} {f : X ⟶ Y} {J : InjectiveResolution X}
    {J' : InjectiveResolution Y} (φ : InjectiveResolution.Hom J J' f) :
    (DerivedCategory.Plus.Qh.map (G.mapHomotopyCategoryPlus.map
        ((HomotopyCategory.Plus.quotient C).map φ.plusHom))).hom =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map φ.hom')) :=
  congrArg DerivedCategory.Qh.map (G.mapHomotopyCategory_map φ.hom')

omit [HasDerivedCategory C] [EnoughInjectives C] in
/-- `toQhPlus` is natural in a morphism of injective resolutions. -/
@[reassoc]
lemma toQhPlus_naturality {X Y : C} {f : X ⟶ Y} {J : InjectiveResolution X}
    {J' : InjectiveResolution Y} (φ : InjectiveResolution.Hom J J' f) :
    DerivedCategory.Q.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map φ.hom') ≫
        toQhPlus G J' =
      toQhPlus G J ≫ (DerivedCategory.Plus.Qh.map (G.mapHomotopyCategoryPlus.map
        ((HomotopyCategory.Plus.quotient C).map φ.plusHom))).hom := by
  rw [Qh_map_mapHomotopyCategoryPlus_hom G φ]
  exact DerivedCategory.quotientCompQhIso_inv_naturality
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map φ.hom')

/-- The naturality square of `toRightDerivedPlus`, read on underlying morphisms. -/
@[reassoc]
lemma toRightDerivedPlus_naturality_hom {X Y : C} {f : X ⟶ Y} {J : InjectiveResolution X}
    {J' : InjectiveResolution Y} (φ : InjectiveResolution.Hom J J' f) :
    (DerivedCategory.Plus.Qh.map (G.mapHomotopyCategoryPlus.map
        ((HomotopyCategory.Plus.quotient C).map φ.plusHom))).hom ≫
        (toRightDerivedPlus G J').hom =
      (toRightDerivedPlus G J).hom ≫
        (G.rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor C 0).map f)).hom :=
  (ObjectProperty.ι _).congr_map (toRightDerivedPlus_naturality G φ)

/-- A morphism of injective resolutions above `f : X ⟶ Y` turns the comparisons for the two
resolutions into a commutative square with `RG(f[0])`. -/
@[reassoc]
lemma toRightDerived_naturality {X Y : C} {f : X ⟶ Y} {J : InjectiveResolution X}
    {J' : InjectiveResolution Y} (φ : InjectiveResolution.Hom J J' f) :
    DerivedCategory.Q.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map φ.hom') ≫
        J'.toRightDerived G =
      J.toRightDerived G ≫
        (G.rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor C 0).map f)).hom := by
  dsimp only [toRightDerived]
  rw [← Category.assoc, toQhPlus_naturality G φ, Category.assoc,
    toRightDerivedPlus_naturality_hom G φ, ← Category.assoc]

end CategoryTheory.InjectiveResolution

end
