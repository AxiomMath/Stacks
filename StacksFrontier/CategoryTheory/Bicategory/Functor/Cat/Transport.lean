module

public import StacksFrontier.CategoryTheory.Sites.Descent.StrongTransDescentData

/-!
# Transport of a pseudofunctor to `Cat` along equivalences of its fibres

Let `B` be a bicategory, let `F : Pseudofunctor B Cat` and suppose that for every object `a`
of `B` we are given a category `H a` and an equivalence `e a : F.obj a ≌ H a`. This file
builds a pseudofunctor `F.transport H e` whose fibre over `a` is `H a`, and the canonical
strong transformation `F.transportStrongTrans H e : F.StrongTrans (F.transport H e)` whose
component at `a` is `(e a).functor`.

On a one-morphism `f : a ⟶ b` the transported pseudofunctor acts by conjugation,
`(e a).inverse ⋙ F.map f ⋙ (e b).functor`. The unitality constraint is the counit of `e a`,
and the composition constraint is the composition constraint of `F` followed by the
insertion of the unit of `e b` at the intermediate object. That insertion is the only place
where the equivalences are used in an essential way: evaluated at an object, each of the five
coherence axioms of a pseudofunctor and each of the three axioms of a strong transformation
reduces to the corresponding axiom for `F` together with the naturality of that unit.

For a pseudofunctor from `LocallyDiscrete Cᵒᵖ` the file also records what the transport does
to descent data, by combining the above with the transport of descent data along a strong
transformation.

## Main definitions

* `CategoryTheory.Pseudofunctor.transport`, the transported pseudofunctor;
* `CategoryTheory.Pseudofunctor.transportStrongTrans`, the canonical strong transformation
  from a pseudofunctor to its transport;
* `CategoryTheory.Pseudofunctor.descentDataTransportEquivalence`, the induced equivalence of
  categories of descent data.

## Main results

* `CategoryTheory.Pseudofunctor.isEquivalence_transportStrongTrans_app`, the components of
  the canonical strong transformation are equivalences;
* `CategoryTheory.Pseudofunctor.isEquivalence_toDescentData_transport_iff` and
  `CategoryTheory.Pseudofunctor.isStackFor_transport_iff`, the invariance of effective
  descent and of being a stack.

## Implementation notes

`transportMap`, `transportApp` and `transport` are `reducible`. The composition constraint of
a pseudofunctor to `Cat` has a type mentioning the composite one-morphism, so a rewrite
inside such a type is only well formed once that composite has been unfolded; marking those
constructions `reducible` is what makes them unfold at the transparency level the tactic
framework uses for that check, and it is why this file needs no transparency option.

The lemmas `CategoryTheory.Equivalence.unit_conj` and
`CategoryTheory.Equivalence.map_unit_comp_map_unitInv` record that conjugating a morphism by
the unit of an equivalence does nothing; the coherence axioms of `transport` and
`transportStrongTrans` reduce to them.
-/

@[expose] public section

universe w v v' u u' t v₂ u₂

namespace CategoryTheory

open Bicategory

namespace Equivalence

variable {C₁ : Type*} [Category C₁] {C₂ : Type*} [Category C₂] {C₃ : Type*} [Category C₃]
  (ε : C₁ ≌ C₂)

/-- Conjugating a morphism by the unit of an equivalence does nothing. -/
@[reassoc]
lemma unit_conj {X Y : C₁} (φ : X ⟶ Y) :
    ε.unit.app X ≫ ε.inverse.map (ε.functor.map φ) ≫ ε.unitInv.app Y = φ := by
  have hnat := ε.unitIso.hom.naturality φ
  simp only [Functor.id_map, Functor.comp_map] at hnat
  rw [← Category.assoc, ← hnat]
  simp

/-- A functor kills the unit of an equivalence against its inverse. -/
@[reassoc]
lemma map_unit_comp_map_unitInv (K : C₁ ⥤ C₃) (Y : C₁) :
    K.map (ε.unit.app Y) ≫ K.map (ε.unitInv.app Y) = 𝟙 _ := by
  rw [← Functor.map_comp]
  simp

end Equivalence

namespace Pseudofunctor

variable {B : Type u} [Bicategory.{w, v} B] (F : Pseudofunctor B Cat.{v', u'})
  (H : B → Cat.{v', u'}) (e : ∀ a, F.obj a ≌ H a)

/-- The one-morphism of `Cat` obtained from `F.map f` by conjugating with the given
equivalences. -/
@[reducible]
def transportMap {a b : B} (f : a ⟶ b) : H a ⟶ H b :=
  Cat.Hom.ofFunctor ((e a).inverse ⋙ (F.map f).toFunctor ⋙ (e b).functor)

/-- The functor `transportMap F H e f` sends `M` to `(e b).functor` applied to the image under
`F.map f` of `(e a).inverse.obj M`. -/
@[simp]
lemma transportMap_obj {a b : B} (f : a ⟶ b) (M : H a) :
    (transportMap F H e f).toFunctor.obj M =
      (e b).functor.obj ((F.map f).toFunctor.obj ((e a).inverse.obj M)) := rfl

/-- The functor `transportMap F H e f` acts on morphisms by `(e a).inverse`, then `F.map f`,
then `(e b).functor`. -/
@[simp]
lemma transportMap_map {a b : B} (f : a ⟶ b) {M N : H a} (φ : M ⟶ N) :
    (transportMap F H e f).toFunctor.map φ =
      (e b).functor.map ((F.map f).toFunctor.map ((e a).inverse.map φ)) := rfl

/-- The two-morphism of `Cat` obtained from `F.map₂ α` by conjugating with the given
equivalences. -/
def transportMap₂ {a b : B} {f g : a ⟶ b} (α : f ⟶ g) :
    transportMap F H e f ⟶ transportMap F H e g :=
  Cat.Hom₂.ofNatTrans
    (Functor.whiskerLeft (e a).inverse
      (Functor.whiskerRight (F.map₂ α).toNatTrans (e b).functor))

/-- The component of `transportMap₂ F H e α` at `M` is the image under `(e b).functor` of the
component of `F.map₂ α` at `(e a).inverse.obj M`. -/
@[simp]
lemma transportMap₂_app {a b : B} {f g : a ⟶ b} (α : f ⟶ g) (M : H a) :
    (transportMap₂ F H e α).toNatTrans.app M =
      (e b).functor.map ((F.map₂ α).toNatTrans.app ((e a).inverse.obj M)) := rfl

/-- The unitality constraint of the transported pseudofunctor: it is the counit of the
equivalence at that object. -/
def transportMapId (a : B) : transportMap F H e (𝟙 a) ≅ 𝟙 (H a) :=
  Cat.Hom.isoMk
    (Functor.isoWhiskerLeft (e a).inverse
        (Functor.isoWhiskerRight (Cat.Hom.toNatIso (F.mapId a)) (e a).functor) ≪≫
      (e a).counitIso)

/-- The component at `M` of the forward unitality constraint of the transport is the image of
the unitality constraint of `F` followed by the counit of `e a` at `M`. -/
@[simp]
lemma transportMapId_hom_app (a : B) (M : H a) :
    (transportMapId F H e a).hom.toNatTrans.app M =
      (e a).functor.map ((F.mapId a).hom.toNatTrans.app ((e a).inverse.obj M)) ≫
        (e a).counitIso.hom.app M := rfl

/-- The component at `M` of the inverse unitality constraint of the transport is the inverse
counit of `e a` at `M` followed by the image of the inverse unitality constraint of `F`. -/
@[simp]
lemma transportMapId_inv_app (a : B) (M : H a) :
    (transportMapId F H e a).inv.toNatTrans.app M =
      (e a).counitIso.inv.app M ≫
        (e a).functor.map ((F.mapId a).inv.toNatTrans.app ((e a).inverse.obj M)) := rfl

/-- The composition constraint of the transported pseudofunctor: it is the constraint of `F`
followed by the insertion of the unit of the equivalence at the intermediate object. -/
def transportMapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    transportMap F H e (f ≫ g) ≅ transportMap F H e f ≫ transportMap F H e g :=
  Cat.Hom.isoMk
    (Functor.isoWhiskerLeft (e a).inverse
        (Functor.isoWhiskerRight (Cat.Hom.toNatIso (F.mapComp f g)) (e c).functor) ≪≫
      Functor.isoWhiskerLeft ((e a).inverse ⋙ (F.map f).toFunctor)
        (Functor.isoWhiskerRight (e b).unitIso ((F.map g).toFunctor ⋙ (e c).functor)))

/-- The component at `M` of the forward composition constraint of the transport is the image of
the composition constraint of `F` followed by the image of the unit of `e b`. -/
@[simp]
lemma transportMapComp_hom_app {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (M : H a) :
    (transportMapComp F H e f g).hom.toNatTrans.app M =
      (e c).functor.map ((F.mapComp f g).hom.toNatTrans.app ((e a).inverse.obj M)) ≫
        (e c).functor.map ((F.map g).toFunctor.map
          ((e b).unitIso.hom.app ((F.map f).toFunctor.obj ((e a).inverse.obj M)))) := rfl

/-- The component at `M` of the inverse composition constraint of the transport is the image of
the inverse unit of `e b` followed by the image of the inverse composition constraint of `F`. -/
@[simp]
lemma transportMapComp_inv_app {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (M : H a) :
    (transportMapComp F H e f g).inv.toNatTrans.app M =
      (e c).functor.map ((F.map g).toFunctor.map
          ((e b).unitIso.inv.app ((F.map f).toFunctor.obj ((e a).inverse.obj M)))) ≫
        (e c).functor.map ((F.mapComp f g).inv.toNatTrans.app ((e a).inverse.obj M)) := rfl

/-- **The transport of a pseudofunctor to `Cat` along a family of equivalences of its
fibres.** -/
@[reducible]
def transport : Pseudofunctor B Cat.{v', u'} where
  obj a := H a
  map f := transportMap F H e f
  map₂ α := transportMap₂ F H e α
  mapId a := transportMapId F H e a
  mapComp f g := transportMapComp F H e f g
  map₂_whisker_left := by
    intro a b c f g h η
    ext M
    simp only [Cat.Hom₂.comp_app, transportMap₂_app, transportMapComp_hom_app,
      transportMapComp_inv_app,
      Cat.whiskerLeft_app, Functor.comp_obj, Functor.id_obj, F.map₂_whisker_left_app,
      Category.assoc, ← Functor.map_comp]
    congr 1
    simp [Equivalence.map_unit_comp_map_unitInv_assoc]
  map₂_whisker_right := by
    intro a b c f g η h
    ext M
    simp only [Cat.Hom₂.comp_app, transportMap₂_app, transportMapComp_hom_app,
      transportMapComp_inv_app,
      Cat.whiskerRight_app, Functor.comp_map, Functor.comp_obj, Functor.id_obj,
      F.map₂_whisker_right_app, Category.assoc, ← Functor.map_comp, ← Functor.map_comp_assoc]
    congr 1
    simp
  map₂_associator := by
    intro a b c d f g h
    ext M
    simp only [Cat.Hom₂.comp_app, transportMap₂_app, transportMapComp_hom_app,
      transportMapComp_inv_app,
      Cat.whiskerLeft_app, Cat.whiskerRight_app, Functor.comp_map, Functor.comp_obj,
      Functor.id_obj, Cat.associator_hom_app, F.map₂_associator_app, eqToHom_refl,
      Category.id_comp, Category.assoc, ← Functor.map_comp, ← Functor.map_comp_assoc]
    congr 1
    rw [Equivalence.unit_conj]
    have hnat := (F.mapComp g h).inv.toNatTrans.naturality
      ((e _).unitIso.hom.app ((F.map f).toFunctor.obj ((e _).inverse.obj M)))
    simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Cat.Hom.comp_toFunctor] at hnat
    simp only [Functor.map_comp, Category.assoc, reassoc_of% hnat]
    simp [Equivalence.map_unit_comp_map_unitInv_assoc]
  map₂_left_unitor := by
    intro a b f
    ext M
    simp only [Cat.Hom₂.comp_app, transportMap₂_app, transportMapComp_hom_app,
      transportMapId_hom_app,
      Cat.whiskerRight_app, Functor.comp_map, Functor.comp_obj, Functor.id_obj,
      Cat.leftUnitor_hom_app, F.map₂_left_unitor_app, eqToHom_refl, Category.comp_id,
      Category.assoc, ← Functor.map_comp]
    congr 2
    simp
  map₂_right_unitor := by
    intro a b f
    ext M
    simp only [Cat.Hom₂.comp_app, transportMap₂_app, transportMapComp_hom_app,
      transportMapId_hom_app,
      Cat.whiskerLeft_app, Functor.comp_obj, Functor.id_obj, Cat.rightUnitor_hom_app,
      F.map₂_right_unitor_app, eqToHom_refl, Category.comp_id, Category.assoc,
      ← Functor.map_comp, ← Functor.map_comp_assoc]
    have hnat := (F.mapId _).hom.toNatTrans.naturality
      ((e _).unitIso.hom.app ((F.map f).toFunctor.obj ((e _).inverse.obj M)))
    simp only [Functor.comp_obj, Functor.id_obj, Functor.id_map, Cat.Hom.id_toFunctor] at hnat
    rw [hnat]
    simp

/-- The fibre of the transported pseudofunctor over `a` is `H a`. -/
@[simp] lemma transport_obj (a : B) : (transport F H e).obj a = H a := rfl

/-- The transported pseudofunctor acts on one-morphisms by `transportMap`. -/
@[simp] lemma transport_map {a b : B} (f : a ⟶ b) :
    (transport F H e).map f = transportMap F H e f := rfl

/-- The transported pseudofunctor acts on two-morphisms by `transportMap₂`. -/
@[simp] lemma transport_map₂ {a b : B} {f g : a ⟶ b} (α : f ⟶ g) :
    (transport F H e).map₂ α = transportMap₂ F H e α := rfl

/-- The unitality constraint of the transported pseudofunctor is `transportMapId`. -/
@[simp] lemma transport_mapId (a : B) :
    (transport F H e).mapId a = transportMapId F H e a := rfl

/-- The composition constraint of the transported pseudofunctor is `transportMapComp`. -/
@[simp] lemma transport_mapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (transport F H e).mapComp f g = transportMapComp F H e f g := rfl

/-- The component of the canonical strong transformation at an object. -/
@[reducible]
def transportApp (a : B) : F.obj a ⟶ (transport F H e).obj a :=
  Cat.Hom.ofFunctor (e a).functor

/-- The functor `transportApp F H e a` acts on objects as `(e a).functor`. -/
@[simp]
lemma transportApp_obj (a : B) (N : F.obj a) :
    (transportApp F H e a).toFunctor.obj N = (e a).functor.obj N := rfl

/-- The functor `transportApp F H e a` acts on morphisms as `(e a).functor`. -/
@[simp]
lemma transportApp_map (a : B) {N N' : F.obj a} (φ : N ⟶ N') :
    (transportApp F H e a).toFunctor.map φ = (e a).functor.map φ := rfl

/-- The strong naturality constraint of the canonical strong transformation: it is the unit
of the equivalence at the source. -/
def transportNaturality {a b : B} (f : a ⟶ b) :
    F.map f ≫ transportApp F H e b ≅ transportApp F H e a ≫ (transport F H e).map f :=
  Cat.Hom.isoMk (Functor.isoWhiskerRight (e a).unitIso ((F.map f).toFunctor ⋙ (e b).functor))

/-- The component at `N` of `transportNaturality F H e f` is the image under `F.map f` and
`(e b).functor` of the unit of `e a` at `N`. -/
@[simp]
lemma transportNaturality_hom_app {a b : B} (f : a ⟶ b) (N : F.obj a) :
    (transportNaturality F H e f).hom.toNatTrans.app N =
      (e b).functor.map ((F.map f).toFunctor.map ((e a).unitIso.hom.app N)) := rfl

/-- **The canonical strong transformation from a pseudofunctor to its transport.** -/
def transportStrongTrans : F.StrongTrans (transport F H e) where
  app a := transportApp F H e a
  naturality f := transportNaturality F H e f
  naturality_naturality := by
    intro a b f g η
    ext N
    simp only [Cat.Hom₂.comp_app]
    simp only [Cat.whiskerLeft_app, Cat.whiskerRight_app, transportNaturality_hom_app,
      transportMap₂_app, ← Functor.map_comp]
    congr 1
    exact ((F.map₂ η).toNatTrans.naturality ((e a).unitIso.hom.app N)).symm
  naturality_id := by
    intro a
    ext N
    simp only [Cat.Hom₂.comp_app]
    simp only [Cat.whiskerLeft_app, Cat.whiskerRight_app, Cat.leftUnitor_hom_app,
      Cat.rightUnitor_inv_app, transportNaturality_hom_app, transportMapId_hom_app,
      eqToHom_refl, Category.comp_id, ← Functor.map_comp_assoc]
    have hnat := (F.mapId a).hom.toNatTrans.naturality ((e a).unitIso.hom.app N)
    simp only [Functor.comp_obj, Functor.id_obj, Functor.id_map, Cat.Hom.id_toFunctor] at hnat
    rw [hnat]
    simp
  naturality_comp := by
    intro a b c f g
    ext N
    simp only [Cat.Hom₂.comp_app]
    simp only [Cat.whiskerLeft_app, Cat.whiskerRight_app, Cat.associator_hom_app,
      Cat.associator_inv_app, transportNaturality_hom_app, transportMapComp_hom_app,
      Functor.comp_obj, Functor.comp_map, Functor.id_obj, eqToHom_refl, Category.comp_id,
      Category.id_comp, ← Functor.map_comp]
    congr 1
    have hnat := (F.mapComp f g).hom.toNatTrans.naturality ((e a).unitIso.hom.app N)
    simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Cat.Hom.comp_toFunctor] at hnat
    simp only [reassoc_of% hnat, ← Functor.map_comp]
    congr 2
    exact (Equivalence.unit_naturality (e b)
      ((F.map f).toFunctor.map ((e a).unitIso.hom.app N))).symm

/-- The components of the canonical strong transformation are equivalences. -/
instance isEquivalence_transportStrongTrans_app (a : B) :
    ((transportStrongTrans F H e).app a).toFunctor.IsEquivalence :=
  inferInstanceAs (e a).functor.IsEquivalence

section Descent

open Opposite

variable {C : Type u₂} [Category.{v₂} C]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  (H : LocallyDiscrete Cᵒᵖ → Cat.{v', u'}) (e : ∀ a, F.obj a ≌ H a)

/-- **Effective descent along a family is invariant under transporting the fibres along
equivalences.** -/
theorem isEquivalence_toDescentData_transport_iff {ι : Type t} {S : C} {X : ι → C}
    (f : ∀ i, X i ⟶ S) :
    (F.toDescentData f).IsEquivalence ↔ ((transport F H e).toDescentData f).IsEquivalence :=
  (transportStrongTrans F H e).isEquivalence_toDescentData_iff f
    (isEquivalence_transportStrongTrans_app F H e)

/-- **Transport of descent data along a family of equivalences of the fibres.** -/
noncomputable def descentDataTransportEquivalence {ι : Type t} {S : C} {X : ι → C}
    (f : ∀ i, X i ⟶ S) : F.DescentData f ≌ (transport F H e).DescentData f :=
  (transportStrongTrans F H e).descentDataEquivalence f
    (isEquivalence_transportStrongTrans_app F H e)

/-- **Being a stack for a presieve is invariant under transporting the fibres along
equivalences.** -/
theorem isStackFor_transport_iff {S : C} (R : Presieve S) :
    F.IsStackFor R ↔ (transport F H e).IsStackFor R :=
  (transportStrongTrans F H e).isStackFor_iff_of_app_isEquivalence
    (isEquivalence_transportStrongTrans_app F H e) R

end Descent

end Pseudofunctor

end CategoryTheory

end
