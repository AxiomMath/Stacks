module

public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
public import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

/-!
# A pseudofunctor from a family of universal arrows

Let `I : C ⥤ᵖ E` and `K : D ⥤ᵖ E` be pseudofunctors into a common bicategory. Suppose that for
every object `X` of `C` an object `L X` of `D` and a 1-morphism `η X : I X ⟶ K (L X)` are given
which are *universal* among the objects `L X'`: for every object `X'` of `C` the functor of
hom-categories

`(L X ⟶ L X') ⥤ (I X ⟶ K (L X'))`,  `g ↦ η X ≫ K g`

is an equivalence of categories. Then `L` extends to a pseudofunctor `C ⥤ᵖ D`: the image of a
1-morphism `f : X ⟶ X'` is the 1-morphism corresponding to `I f ≫ η X'` under the equivalence,
the image of a 2-morphism is its transport through the equivalence, and the comparison
2-isomorphisms are the transports of the evident comparisons on the `E` side. This is the
pseudofunctoriality of a left biadjoint defined objectwise by universal arrows.

Moreover the functor `L` induces on hom-categories is, up to the equivalences above, the functor
`f ↦ I f ≫ η X'`; so it is an equivalence as soon as that one is.

## Main definitions

* `CategoryTheory.Pseudofunctor.UniversalArrows`: the data `L`, `η`.
* `CategoryTheory.Pseudofunctor.UniversalArrows.homFunctor`: the functor
  `g ↦ η X ≫ K g`.
* `CategoryTheory.Pseudofunctor.UniversalArrows.pseudofunctor`: the pseudofunctor.

## Main results

* `CategoryTheory.Pseudofunctor.UniversalArrows.mapFunctorCompHomFunctorIso`: the functor of
  hom-categories of the pseudofunctor, followed by the universal equivalence, is
  `f ↦ I f ≫ η X'`.
* `CategoryTheory.Pseudofunctor.UniversalArrows.isEquivalence_mapFunctor`: the functors of
  hom-categories of the pseudofunctor are equivalences when the functors `f ↦ I f ≫ η X'` are.

## Implementation notes

Every coherence is checked after applying the universal equivalence, which is faithful. There
the image of the transport of a 2-morphism is known (`unit_whiskerLeft_map₂`), and whiskering it
by a further 1-morphism on the left is computed by `unit_whiskerLeft_whiskerLeft` and
`whiskerLeft_mapIso_inv_whiskerRight`, where the exchange law is used; what remains is coherence
in the bicategory `E`.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory Category

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

namespace Pseudofunctor

variable {C : Type u₁} [Bicategory.{w₁, v₁} C] {D : Type u₂} [Bicategory.{w₂, v₂} D]
  {E : Type u₃} [Bicategory.{w₃, v₃} E]

/-- **A family of arrows from a pseudofunctor `I` to a pseudofunctor `K`**: an object `obj X` of
`D` for every object `X` of `C`, and a 1-morphism `unit X : I X ⟶ K (obj X)`. It is a family of
*universal* arrows when the functors `UniversalArrows.homFunctor` are equivalences. -/
structure UniversalArrows (I : C ⥤ᵖ E) (K : D ⥤ᵖ E) where
  /-- The object of `D` attached to an object of `C`. -/
  obj : C → D
  /-- The arrow from `I X` to `K (obj X)`. -/
  unit (X : C) : I.obj X ⟶ K.obj (obj X)

namespace UniversalArrows

variable {I : C ⥤ᵖ E} {K : D ⥤ᵖ E} (A : UniversalArrows I K)

/-- The functor of hom-categories `(obj X ⟶ Y) ⥤ (I X ⟶ K Y)`, `g ↦ unit X ≫ K g`. -/
def homFunctor (X : C) (Y : D) : (A.obj X ⟶ Y) ⥤ (I.obj X ⟶ K.obj Y) :=
  K.mapFunctor (A.obj X) Y ⋙ precomp (K.obj Y) (A.unit X)

/-- `UniversalArrows.homFunctor` sends `g` to `unit X ≫ K g`. -/
@[simp]
lemma homFunctor_obj {X : C} {Y : D} (g : A.obj X ⟶ Y) :
    (A.homFunctor X Y).obj g = A.unit X ≫ K.map g := rfl

/-- `UniversalArrows.homFunctor` sends a 2-morphism `θ` to `unit X ◁ K θ`. -/
@[simp]
lemma homFunctor_map {X : C} {Y : D} {g g' : A.obj X ⟶ Y} (θ : g ⟶ g') :
    (A.homFunctor X Y).map θ = A.unit X ◁ K.map₂ θ := rfl

variable [hA : ∀ X X' : C, (A.homFunctor X (A.obj X')).IsEquivalence]

/-- The image of a 1-morphism `f : X ⟶ X'`: the 1-morphism `obj X ⟶ obj X'` corresponding to
`I f ≫ unit X'`. -/
noncomputable def map {X X' : C} (f : X ⟶ X') : A.obj X ⟶ A.obj X' :=
  (A.homFunctor X (A.obj X')).objPreimage (I.map f ≫ A.unit X')

/-- The defining isomorphism of `UniversalArrows.map`. -/
noncomputable def mapIso {X X' : C} (f : X ⟶ X') :
    A.unit X ≫ K.map (A.map f) ≅ I.map f ≫ A.unit X' :=
  (A.homFunctor X (A.obj X')).objObjPreimageIso (I.map f ≫ A.unit X')

/-- The image of a 2-morphism: its transport through the universal equivalence. -/
noncomputable def map₂ {X X' : C} {f g : X ⟶ X'} (θ : f ⟶ g) : A.map f ⟶ A.map g :=
  (A.homFunctor X (A.obj X')).preimage
    ((A.mapIso f).hom ≫ I.map₂ θ ▷ A.unit X' ≫ (A.mapIso g).inv)

/-- Under the universal equivalence, the image of `map₂ θ` is `I θ ▷ unit X'` conjugated by
`UniversalArrows.mapIso`. -/
lemma unit_whiskerLeft_map₂ {X X' : C} {f g : X ⟶ X'} (θ : f ⟶ g) :
    A.unit X ◁ K.map₂ (A.map₂ θ) =
      (A.mapIso f).hom ≫ I.map₂ θ ▷ A.unit X' ≫ (A.mapIso g).inv :=
  (A.homFunctor X (A.obj X')).map_preimage _

/-- Naturality of `UniversalArrows.mapIso` in the 1-morphism. -/
lemma unit_whiskerLeft_map₂_comp_mapIso_hom {X X' : C} {f g : X ⟶ X'} (θ : f ⟶ g) :
    A.unit X ◁ K.map₂ (A.map₂ θ) ≫ (A.mapIso g).hom =
      (A.mapIso f).hom ≫ I.map₂ θ ▷ A.unit X' := by
  rw [unit_whiskerLeft_map₂]
  simp

/-- **Whiskering on the left by the image of a 1-morphism.** After `unit X ≫ K (map f)` has been
identified with `I f ≫ unit X'`, whiskering a 2-morphism `γ` by `K (map f)` becomes whiskering
`unit X' ◁ γ` by `I f`. -/
lemma unit_whiskerLeft_whiskerLeft {X X' : C} (f : X ⟶ X') {Z : E}
    {P Q : K.obj (A.obj X') ⟶ Z} (γ : P ⟶ Q) :
    A.unit X ◁ K.map (A.map f) ◁ γ =
      (α_ _ _ _).inv ≫ (A.mapIso f).hom ▷ P ≫ (α_ _ _ _).hom ≫
        I.map f ◁ (A.unit X' ◁ γ) ≫
          (α_ _ _ _).inv ≫ (A.mapIso f).inv ▷ Q ≫ (α_ _ _ _).hom := by
  calc A.unit X ◁ K.map (A.map f) ◁ γ
      = (α_ _ _ _).inv ≫ ((A.unit X ≫ K.map (A.map f)) ◁ γ ≫
          (A.mapIso f).hom ▷ Q) ≫ (A.mapIso f).inv ▷ Q ≫ (α_ _ _ _).hom := by
        simp only [assoc]
        simp
    _ = _ := by
        rw [whisker_exchange (A.mapIso f).hom γ]
        simp

/-- **Whiskering the transport of a 2-morphism on the left.** -/
lemma unit_whiskerLeft_whiskerLeft_map₂ {X X' X'' : C} (f : X ⟶ X') {g h : X' ⟶ X''}
    (θ : g ⟶ h) :
    A.unit X ◁ K.map (A.map f) ◁ K.map₂ (A.map₂ θ) =
      (α_ _ _ _).inv ≫ (A.mapIso f).hom ▷ K.map (A.map g) ≫ (α_ _ _ _).hom ≫
        I.map f ◁ ((A.mapIso g).hom ≫ I.map₂ θ ▷ A.unit X'' ≫ (A.mapIso h).inv) ≫
          (α_ _ _ _).inv ≫ (A.mapIso f).inv ▷ K.map (A.map h) ≫ (α_ _ _ _).hom := by
  rw [unit_whiskerLeft_whiskerLeft (γ := K.map₂ (A.map₂ θ)), unit_whiskerLeft_map₂]

omit hA in
/-- `unit X ◁ (K β ▷ K k)` is `(unit X ◁ K β) ▷ K k`, up to associators. -/
lemma unit_whiskerLeft_whiskerRight {X : C} {Y Z : D} {g h : A.obj X ⟶ Y} (β : g ⟶ h)
    (k : Y ⟶ Z) :
    A.unit X ◁ (K.map₂ β ▷ K.map k) =
      (α_ _ _ _).inv ≫ (A.unit X ◁ K.map₂ β) ▷ K.map k ≫ (α_ _ _ _).hom := by
  simp

/-- The comparison of `unit X ≫ K (map (𝟙 X))` with `unit X ≫ K (𝟙 (obj X))` on the `E` side, of
which `UniversalArrows.mapId` is the transport. -/
noncomputable def mapIdAux (X : C) :
    A.unit X ≫ K.map (A.map (𝟙 X)) ≅ A.unit X ≫ K.map (𝟙 (A.obj X)) :=
  A.mapIso (𝟙 X) ≪≫ whiskerRightIso (I.mapId X) (A.unit X) ≪≫ λ_ (A.unit X) ≪≫
    (ρ_ (A.unit X)).symm ≪≫ whiskerLeftIso (A.unit X) (K.mapId (A.obj X)).symm

/-- The comparison isomorphism `map (𝟙 X) ≅ 𝟙 (obj X)`. -/
noncomputable def mapId (X : C) : A.map (𝟙 X) ≅ 𝟙 (A.obj X) :=
  (A.homFunctor X (A.obj X)).preimageIso (A.mapIdAux X)

/-- The image of `(mapId X).hom` under the universal equivalence is `(mapIdAux X).hom`. -/
lemma unit_whiskerLeft_mapId_hom (X : C) :
    A.unit X ◁ K.map₂ (A.mapId X).hom = (A.mapIdAux X).hom :=
  (A.homFunctor X (A.obj X)).map_preimage _

/-- The image of `(mapId X).inv` under the universal equivalence is `(mapIdAux X).inv`. -/
lemma unit_whiskerLeft_mapId_inv (X : C) :
    A.unit X ◁ K.map₂ (A.mapId X).inv = (A.mapIdAux X).inv :=
  (A.homFunctor X (A.obj X)).map_preimage _

/-- The comparison of `unit X ≫ K (map (f ≫ g))` with `unit X ≫ K (map f ≫ map g)` on the `E`
side, of which `UniversalArrows.mapComp` is the transport. -/
noncomputable def mapCompAux {X X' X'' : C} (f : X ⟶ X') (g : X' ⟶ X'') :
    A.unit X ≫ K.map (A.map (f ≫ g)) ≅ A.unit X ≫ K.map (A.map f ≫ A.map g) :=
  A.mapIso (f ≫ g) ≪≫ whiskerRightIso (I.mapComp f g) (A.unit X'') ≪≫ α_ _ _ _ ≪≫
    whiskerLeftIso (I.map f) (A.mapIso g).symm ≪≫ (α_ _ _ _).symm ≪≫
      whiskerRightIso (A.mapIso f).symm (K.map (A.map g)) ≪≫ α_ _ _ _ ≪≫
        whiskerLeftIso (A.unit X) (K.mapComp (A.map f) (A.map g)).symm

/-- The comparison isomorphism `map (f ≫ g) ≅ map f ≫ map g`. -/
noncomputable def mapComp {X X' X'' : C} (f : X ⟶ X') (g : X' ⟶ X'') :
    A.map (f ≫ g) ≅ A.map f ≫ A.map g :=
  (A.homFunctor X (A.obj X'')).preimageIso (A.mapCompAux f g)

/-- The image of `(mapComp f g).hom` under the universal equivalence is
`(mapCompAux f g).hom`. -/
lemma unit_whiskerLeft_mapComp_hom {X X' X'' : C} (f : X ⟶ X') (g : X' ⟶ X'') :
    A.unit X ◁ K.map₂ (A.mapComp f g).hom = (A.mapCompAux f g).hom :=
  (A.homFunctor X (A.obj X'')).map_preimage _

/-- The image of `(mapComp f g).inv` under the universal equivalence is
`(mapCompAux f g).inv`. -/
lemma unit_whiskerLeft_mapComp_inv {X X' X'' : C} (f : X ⟶ X') (g : X' ⟶ X'') :
    A.unit X ◁ K.map₂ (A.mapComp f g).inv = (A.mapCompAux f g).inv :=
  (A.homFunctor X (A.obj X'')).map_preimage _

/-- `UniversalArrows.map₂` preserves identity 2-morphisms. -/
lemma map₂_id {X X' : C} (f : X ⟶ X') : A.map₂ (𝟙 f) = 𝟙 (A.map f) := by
  apply (A.homFunctor X (A.obj X')).map_injective
  rw [homFunctor_map, unit_whiskerLeft_map₂]
  simp

/-- `UniversalArrows.map₂` preserves vertical composition of 2-morphisms. -/
lemma map₂_comp {X X' : C} {f g h : X ⟶ X'} (θ : f ⟶ g) (θ' : g ⟶ h) :
    A.map₂ (θ ≫ θ') = A.map₂ θ ≫ A.map₂ θ' := by
  apply (A.homFunctor X (A.obj X')).map_injective
  simp only [homFunctor_map, PrelaxFunctor.map₂_comp, whiskerLeft_comp, unit_whiskerLeft_map₂,
    comp_whiskerRight, assoc, Iso.inv_hom_id_assoc]
  rfl

/-- Naturality of `UniversalArrows.mapCompAux` in the second 1-morphism, under the universal
equivalence. -/
@[reassoc]
lemma mapCompAux_hom_whiskerLeft_map₂ {X X' X'' : C} (f : X ⟶ X') {g h : X' ⟶ X''}
    (θ : g ⟶ h) :
    (A.mapCompAux f g).hom ≫ A.unit X ◁ K.map₂ (A.map f ◁ A.map₂ θ) =
      A.unit X ◁ K.map₂ (A.map₂ (f ◁ θ)) ≫ (A.mapCompAux f h).hom := by
  rw [Pseudofunctor.map₂_whisker_left, whiskerLeft_comp, whiskerLeft_comp,
    unit_whiskerLeft_whiskerLeft_map₂, unit_whiskerLeft_map₂, Pseudofunctor.map₂_whisker_left]
  simp only [mapCompAux, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, whiskerRightIso_hom,
    assoc]
  simp

/-- A 2-morphism between images of composites is conjugate by `UniversalArrows.mapComp` to `φ`
as soon as this holds after applying the universal equivalence. -/
private lemma eq_mapComp_hom_comp_of_mapCompAux {X X' X'' : C} {f f' : X ⟶ X'} {g g' : X' ⟶ X''}
    {ψ : A.map (f ≫ g) ⟶ A.map (f' ≫ g')} {φ : A.map f ≫ A.map g ⟶ A.map f' ≫ A.map g'}
    (h : (A.mapCompAux f g).hom ≫ A.unit X ◁ K.map₂ φ =
      A.unit X ◁ K.map₂ ψ ≫ (A.mapCompAux f' g').hom) :
    ψ = (A.mapComp f g).hom ≫ φ ≫ (A.mapComp f' g').inv := by
  apply (A.homFunctor X (A.obj X'')).map_injective
  simp only [homFunctor_map, PrelaxFunctor.map₂_comp, whiskerLeft_comp,
    unit_whiskerLeft_mapComp_hom, unit_whiskerLeft_mapComp_inv]
  rw [← assoc, h, assoc, Iso.hom_inv_id, comp_id]

/-- `map₂ (f ◁ θ)` is `map f ◁ map₂ θ`, conjugated by `UniversalArrows.mapComp`. -/
lemma map₂_whisker_left {X X' X'' : C} (f : X ⟶ X') {g h : X' ⟶ X''} (θ : g ⟶ h) :
    A.map₂ (f ◁ θ) = (A.mapComp f g).hom ≫ A.map f ◁ A.map₂ θ ≫ (A.mapComp f h).inv :=
  A.eq_mapComp_hom_comp_of_mapCompAux (mapCompAux_hom_whiskerLeft_map₂ A f θ)

/-- Naturality of `UniversalArrows.mapCompAux` in the first 1-morphism, under the universal
equivalence. -/
@[reassoc]
lemma mapCompAux_hom_whiskerRight_map₂ {X X' X'' : C} {f g : X ⟶ X'} (θ : f ⟶ g)
    (h : X' ⟶ X'') :
    (A.mapCompAux f h).hom ≫ A.unit X ◁ K.map₂ (A.map₂ θ ▷ A.map h) =
      A.unit X ◁ K.map₂ (A.map₂ (θ ▷ h)) ≫ (A.mapCompAux g h).hom := by
  rw [Pseudofunctor.map₂_whisker_right, whiskerLeft_comp, whiskerLeft_comp,
    unit_whiskerLeft_whiskerRight,
    unit_whiskerLeft_map₂, unit_whiskerLeft_map₂, Pseudofunctor.map₂_whisker_right]
  simp only [mapCompAux, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, whiskerRightIso_hom,
    assoc]
  simp only [comp_whiskerRight, assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    inv_hom_whiskerRight_assoc, whiskerLeft_inv_hom_assoc]
  rw [← associator_inv_naturality_left_assoc, whisker_exchange_assoc]
  bicategory

/-- `map₂ (θ ▷ h)` is `map₂ θ ▷ map h`, conjugated by `UniversalArrows.mapComp`. -/
lemma map₂_whisker_right {X X' X'' : C} {f g : X ⟶ X'} (θ : f ⟶ g) (h : X' ⟶ X'') :
    A.map₂ (θ ▷ h) = (A.mapComp f h).hom ≫ A.map₂ θ ▷ A.map h ≫ (A.mapComp g h).inv :=
  A.eq_mapComp_hom_comp_of_mapCompAux (mapCompAux_hom_whiskerRight_map₂ A θ h)

/-- Sliding a 2-morphism whiskered on the right past the inverse of `UniversalArrows.mapIso`
whiskered on the left: an instance of the exchange law. -/
@[reassoc]
lemma whiskerLeft_mapIso_inv_whiskerRight {X X' : C} (f : X ⟶ X') {W : E}
    {a b : W ⟶ I.obj X} (η : a ⟶ b) :
    a ◁ (A.mapIso f).inv ≫ (α_ _ _ _).inv ≫ η ▷ A.unit X ▷ K.map (A.map f) =
      (α_ _ _ _).inv ≫ η ▷ I.map f ▷ A.unit X' ≫ (α_ _ _ _).hom ≫ b ◁ (A.mapIso f).inv ≫
        (α_ _ _ _).inv := by
  have hx := whisker_exchange η (A.mapIso f).inv
  simp only [whiskerRight_comp] at hx
  simp only [← assoc, Iso.eq_comp_inv]
  simp only [assoc]
  simpa using hx

/-- Compatibility of `UniversalArrows.map₂` with left unitors. -/
lemma map₂_left_unitor {X X' : C} (f : X ⟶ X') :
    A.map₂ (λ_ f).hom = (A.mapComp (𝟙 X) f).hom ≫ (A.mapId X).hom ▷ A.map f ≫
      (λ_ (A.map f)).hom := by
  apply (A.homFunctor X (A.obj X')).map_injective
  simp only [homFunctor_map, PrelaxFunctor.map₂_comp, whiskerLeft_comp,
    unit_whiskerLeft_mapComp_hom, unit_whiskerLeft_map₂, Pseudofunctor.map₂_whisker_right,
    unit_whiskerLeft_whiskerRight, unit_whiskerLeft_mapId_hom, Pseudofunctor.map₂_left_unitor]
  simp only [mapCompAux, mapIdAux, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom,
    whiskerRightIso_hom, assoc]
  simp only [homFunctor_obj, comp_whiskerRight, leftUnitor_whiskerRight, assoc, whisker_assoc,
    triangle_assoc_comp_right_inv_assoc, whiskerLeft_inv_hom_assoc, Iso.inv_hom_id_assoc,
    whiskerLeft_inv_hom_whiskerRight_assoc, whiskerLeft_inv_hom, comp_id, Iso.hom_inv_id_assoc,
    inv_hom_whiskerRight_assoc, Iso.cancel_iso_hom_left]
  rw [whiskerLeft_mapIso_inv_whiskerRight_assoc]
  simp

/-- Compatibility of `UniversalArrows.map₂` with right unitors. -/
lemma map₂_right_unitor {X X' : C} (f : X ⟶ X') :
    A.map₂ (ρ_ f).hom = (A.mapComp f (𝟙 X')).hom ≫ A.map f ◁ (A.mapId X').hom ≫
      (ρ_ (A.map f)).hom := by
  apply (A.homFunctor X (A.obj X')).map_injective
  simp only [homFunctor_map, PrelaxFunctor.map₂_comp, whiskerLeft_comp,
    unit_whiskerLeft_mapComp_hom, unit_whiskerLeft_map₂, Pseudofunctor.map₂_whisker_left,
    Pseudofunctor.map₂_right_unitor]
  simp only [unit_whiskerLeft_whiskerLeft, unit_whiskerLeft_mapId_hom, mapCompAux, mapIdAux,
    Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, whiskerRightIso_hom, assoc]
  simp

/-- Compatibility of `UniversalArrows.map₂` with associators. -/
lemma map₂_associator {X₀ X₁ X₂ X₃ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) :
    A.map₂ (α_ f g h).hom = (A.mapComp (f ≫ g) h).hom ≫ (A.mapComp f g).hom ▷ A.map h ≫
      (α_ (A.map f) (A.map g) (A.map h)).hom ≫ A.map f ◁ (A.mapComp g h).inv ≫
        (A.mapComp f (g ≫ h)).inv := by
  apply (A.homFunctor X₀ (A.obj X₃)).map_injective
  simp only [homFunctor_map, PrelaxFunctor.map₂_comp, whiskerLeft_comp,
    unit_whiskerLeft_mapComp_hom, unit_whiskerLeft_mapComp_inv, unit_whiskerLeft_map₂,
    Pseudofunctor.map₂_whisker_right, Pseudofunctor.map₂_whisker_left,
    unit_whiskerLeft_whiskerRight, Pseudofunctor.map₂_associator]
  simp only [unit_whiskerLeft_whiskerLeft, unit_whiskerLeft_mapComp_inv, mapCompAux,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, whiskerLeftIso_hom,
    whiskerLeftIso_inv, whiskerRightIso_hom, whiskerRightIso_inv, assoc]
  simp only [homFunctor_obj, comp_whiskerRight, whisker_assoc, assoc, whiskerRight_comp,
    whiskerLeft_comp, whiskerLeft_inv_hom_assoc, Iso.hom_inv_id_assoc, inv_hom_whiskerRight_assoc,
    Iso.inv_hom_id_assoc, whiskerLeft_whiskerLeft_inv_hom_assoc, pentagon_hom_hom_inv_hom_hom_assoc,
    pentagon_hom_inv_inv_inv_inv_assoc, whiskerLeft_inv_hom_whiskerRight_assoc,
    hom_inv_whiskerRight_assoc, inv_hom_whiskerRight_whiskerRight_assoc, pentagon_assoc,
    Iso.cancel_iso_hom_left]
  rw [whiskerLeft_mapIso_inv_whiskerRight_assoc]
  simp

/-- **The pseudofunctor determined by a family of universal arrows.** On objects it is
`UniversalArrows.obj`; the image of a 1-morphism `f` is the 1-morphism corresponding to
`I f ≫ unit X'`, and the comparison 2-isomorphisms are the transports of the evident comparisons
on the `E` side. -/
noncomputable def pseudofunctor : C ⥤ᵖ D where
  obj := A.obj
  map := A.map
  map₂ := A.map₂
  map₂_id := A.map₂_id
  map₂_comp := A.map₂_comp
  mapId := A.mapId
  mapComp := A.mapComp
  map₂_whisker_left := A.map₂_whisker_left
  map₂_whisker_right := A.map₂_whisker_right
  map₂_associator := A.map₂_associator
  map₂_left_unitor := A.map₂_left_unitor
  map₂_right_unitor := A.map₂_right_unitor

/-- On objects, `UniversalArrows.pseudofunctor` is `UniversalArrows.obj`. -/
@[simp] lemma pseudofunctor_obj (X : C) : A.pseudofunctor.obj X = A.obj X := rfl

/-- On 1-morphisms, `UniversalArrows.pseudofunctor` is `UniversalArrows.map`. -/
@[simp] lemma pseudofunctor_map {X X' : C} (f : X ⟶ X') : A.pseudofunctor.map f = A.map f := rfl

/-- **The functor of hom-categories of the pseudofunctor, followed by the universal equivalence,
is `f ↦ I f ≫ unit X'`.** -/
noncomputable def mapFunctorCompHomFunctorIso (X X' : C) :
    A.pseudofunctor.mapFunctor X X' ⋙ A.homFunctor X (A.obj X') ≅
      I.mapFunctor X X' ⋙ postcomp (I.obj X) (A.unit X') :=
  NatIso.ofComponents (fun f => A.mapIso f) fun θ =>
    A.unit_whiskerLeft_map₂_comp_mapIso_hom θ

/-- **The functors of hom-categories of the pseudofunctor are equivalences** as soon as the
functors `f ↦ I f ≫ unit X'` are. -/
theorem isEquivalence_mapFunctor (X X' : C)
    [(I.mapFunctor X X' ⋙ postcomp (I.obj X) (A.unit X')).IsEquivalence] :
    (A.pseudofunctor.mapFunctor X X').IsEquivalence := by
  have h₁ : (A.homFunctor X (A.obj X')).IsEquivalence := hA X X'
  have h₂ : (A.pseudofunctor.mapFunctor X X' ⋙ A.homFunctor X (A.obj X')).IsEquivalence :=
    Functor.isEquivalence_of_iso (A.mapFunctorCompHomFunctorIso X X').symm
  exact @Functor.isEquivalence_of_comp_right _ _ _ _ _ _ _ _ h₁ h₂

end UniversalArrows

end Pseudofunctor

end CategoryTheory

end
