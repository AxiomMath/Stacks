module

public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Equivalence

/-!
# Units for a tensor functor with an associativity constraint

Following the Stacks project (Categories, Section "Monoidal categories"), we consider a category
`C` with a functor `T : C × C ⥤ C`, written `X ⊗ Y = T.obj (X, Y)`, and an *associativity
constraint*: a functorial isomorphism `φ : X ⊗ (Y ⊗ Z) ≅ (X ⊗ Y) ⊗ Z` satisfying the pentagon
axiom. No unit is part of these data.

A *unit* for `(C, T, φ)` is an object `𝟏` with functorial isomorphisms `l : 𝟏 ⊗ X ≅ X` and
`r : X ⊗ 𝟏 ≅ X` satisfying the triangle axiom `(r ⊗ id) ∘ φ = id ⊗ l`. A *unit pair* is an
object `𝟏` with an isomorphism `1 : 𝟏 ⊗ 𝟏 ≅ 𝟏` such that `X ↦ 𝟏 ⊗ X` and `X ↦ X ⊗ 𝟏` are
equivalences.

## Main definitions

* `CategoryTheory.AssociativityConstraint`: an associativity constraint for `T`.
* `CategoryTheory.AssociativityConstraint.MonoidalUnit`: a unit `(𝟏, l, r)` for `(C, T, φ)`.
* `CategoryTheory.AssociativityConstraint.UnitPair`: a pair `(𝟏, 1)` as above.
* `CategoryTheory.AssociativityConstraint.unitEquivUnitPair`: the one-to-one correspondence
  between units and pairs, sending `(𝟏, l, r)` to `(𝟏, r_𝟏)`; its inverse sends `(𝟏, 1)` to the
  unit whose isomorphisms are characterized by `id_𝟏 ⊗ l_X = (1 ⊗ id_X) ∘ φ` and
  `r_X ⊗ id_𝟏 = (id_X ⊗ 1) ∘ φ⁻¹` (Stacks, Tag 0HAW).
-/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory

open Category

namespace AssociativityConstraint

variable {C : Type u} [Category.{v} C] (T : C × C ⥤ C)

/-- The tensor product `f ⊗ g : X ⊗ Y ⟶ X' ⊗ Y'` of two morphisms, for `T : C × C ⥤ C`. -/
def tensorMap {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') : T.obj (X, Y) ⟶ T.obj (X', Y') :=
  T.map ((f, g) : (X, Y) ⟶ (X', Y'))

@[simp]
lemma tensorMap_id (X Y : C) : tensorMap T (𝟙 X) (𝟙 Y) = 𝟙 _ :=
  T.map_id (X, Y)

@[reassoc (attr := simp)]
lemma tensorMap_comp_tensorMap {X X' X'' Y Y' Y'' : C} (f : X ⟶ X') (f' : X' ⟶ X'')
    (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    tensorMap T f g ≫ tensorMap T f' g' = tensorMap T (f ≫ f') (g ≫ g') :=
  (T.map_comp ((f, g) : (X, Y) ⟶ (X', Y')) ((f', g') : (X', Y') ⟶ (X'', Y''))).symm

lemma tensorMap_id_comp (X : C) {Y Y' Y'' : C} (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    tensorMap T (𝟙 X) (g ≫ g') = tensorMap T (𝟙 X) g ≫ tensorMap T (𝟙 X) g' := by
  simp

lemma tensorMap_comp_id {X X' X'' : C} (f : X ⟶ X') (f' : X' ⟶ X'') (Y : C) :
    tensorMap T (f ≫ f') (𝟙 Y) = tensorMap T f (𝟙 Y) ≫ tensorMap T f' (𝟙 Y) := by
  simp

/-- The tensor product of two isomorphisms. -/
@[simps]
def tensorIso {X X' Y Y' : C} (e : X ≅ X') (e' : Y ≅ Y') : T.obj (X, Y) ≅ T.obj (X', Y') where
  hom := tensorMap T e.hom e'.hom
  inv := tensorMap T e.inv e'.inv

lemma sectR_comp_map (Z : C) {X Y : C} (f : X ⟶ Y) :
    (Prod.sectR Z C ⋙ T).map f = tensorMap T (𝟙 Z) f :=
  rfl

lemma sectL_comp_map (Z : C) {X Y : C} (f : X ⟶ Y) :
    (Prod.sectL C Z ⋙ T).map f = tensorMap T f (𝟙 Z) :=
  rfl

end AssociativityConstraint

open AssociativityConstraint

/-- An *associativity constraint* (Stacks, Section "Monoidal categories") for a functor
`T : C × C ⥤ C`, written `X ⊗ Y = T.obj (X, Y)`: isomorphisms
`φ_{X,Y,Z} : X ⊗ (Y ⊗ Z) ≅ (X ⊗ Y) ⊗ Z`, functorial in `X`, `Y`, `Z`, satisfying the pentagon axiom
`φ_{X⊗Y,Z,W} ∘ φ_{X,Y,Z⊗W} = (φ_{X,Y,Z} ⊗ id_W) ∘ φ_{X,Y⊗Z,W} ∘ (id_X ⊗ φ_{Y,Z,W})`. -/
structure AssociativityConstraint {C : Type u} [Category.{v} C] (T : C × C ⥤ C) where
  /-- The isomorphism `φ_{X,Y,Z} : X ⊗ (Y ⊗ Z) ≅ (X ⊗ Y) ⊗ Z`. -/
  iso (X Y Z : C) : T.obj (X, T.obj (Y, Z)) ≅ T.obj (T.obj (X, Y), Z)
  /-- Functoriality of `φ` in `X`, `Y` and `Z`. -/
  naturality {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    tensorMap T f (tensorMap T g h) ≫ (iso X' Y' Z').hom =
      (iso X Y Z).hom ≫ tensorMap T (tensorMap T f g) h
  /-- The pentagon axiom. -/
  pentagon (X Y Z W : C) :
    (iso X Y (T.obj (Z, W))).hom ≫ (iso (T.obj (X, Y)) Z W).hom =
      tensorMap T (𝟙 X) (iso Y Z W).hom ≫ (iso X (T.obj (Y, Z)) W).hom ≫
        tensorMap T (iso X Y Z).hom (𝟙 W)

namespace AssociativityConstraint

variable {C : Type u} [Category.{v} C] {T : C × C ⥤ C} (φ : AssociativityConstraint T)

@[reassoc]
lemma naturality_inv {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    tensorMap T (tensorMap T f g) h ≫ (φ.iso X' Y' Z').inv =
      (φ.iso X Y Z).inv ≫ tensorMap T f (tensorMap T g h) := by
  rw [Iso.eq_inv_comp, ← assoc, ← φ.naturality, assoc, Iso.hom_inv_id, comp_id]

/-- A *unit* (Stacks, Section "Monoidal categories") for `(C, T, φ)`: an object `𝟏` with
isomorphisms `l_X : 𝟏 ⊗ X ≅ X` and `r_X : X ⊗ 𝟏 ≅ X`, functorial in `X`, such that
`(r_X ⊗ id_Y) ∘ φ_{X,𝟏,Y} = id_X ⊗ l_Y` for all `X`, `Y`. -/
structure MonoidalUnit where
  /-- The unit object `𝟏`. -/
  obj : C
  /-- The isomorphism `l_X : 𝟏 ⊗ X ≅ X`. -/
  l (X : C) : T.obj (obj, X) ≅ X
  /-- The isomorphism `r_X : X ⊗ 𝟏 ≅ X`. -/
  r (X : C) : T.obj (X, obj) ≅ X
  l_naturality {X Y : C} (f : X ⟶ Y) : tensorMap T (𝟙 obj) f ≫ (l Y).hom = (l X).hom ≫ f
  r_naturality {X Y : C} (f : X ⟶ Y) : tensorMap T f (𝟙 obj) ≫ (r Y).hom = (r X).hom ≫ f
  triangle (X Y : C) :
    (φ.iso X obj Y).hom ≫ tensorMap T (r X).hom (𝟙 Y) = tensorMap T (𝟙 X) (l Y).hom

variable (T) in
/-- A pair `(𝟏, 1)` (Stacks, Tag 0HAW): an object `𝟏` with an isomorphism `1 : 𝟏 ⊗ 𝟏 ≅ 𝟏` such
that the functors `L : X ↦ 𝟏 ⊗ X` and `R : X ↦ X ⊗ 𝟏` are equivalences. -/
structure UnitPair where
  /-- The object `𝟏`. -/
  obj : C
  /-- The isomorphism `1 : 𝟏 ⊗ 𝟏 ≅ 𝟏`. -/
  iso : T.obj (obj, obj) ≅ obj
  isEquivalence_left : (Prod.sectR obj C ⋙ T).IsEquivalence
  isEquivalence_right : (Prod.sectL C obj ⋙ T).IsEquivalence

namespace MonoidalUnit

variable {φ} (u : φ.MonoidalUnit)

lemma mk_eq (l' : ∀ X : C, T.obj (u.obj, X) ≅ X) (r' : ∀ X : C, T.obj (X, u.obj) ≅ X)
    (hl' : ∀ {X Y : C} (f : X ⟶ Y), tensorMap T (𝟙 u.obj) f ≫ (l' Y).hom = (l' X).hom ≫ f)
    (hr' : ∀ {X Y : C} (f : X ⟶ Y), tensorMap T f (𝟙 u.obj) ≫ (r' Y).hom = (r' X).hom ≫ f)
    (ht' : ∀ X Y : C,
      (φ.iso X u.obj Y).hom ≫ tensorMap T (r' X).hom (𝟙 Y) = tensorMap T (𝟙 X) (l' Y).hom)
    (hl : ∀ X, (l' X).hom = (u.l X).hom) (hr : ∀ X, (r' X).hom = (u.r X).hom) :
    (⟨u.obj, l', r', hl', hr', ht'⟩ : φ.MonoidalUnit) = u := by
  obtain ⟨o, l, r, _, _, _⟩ := u
  simp only [MonoidalUnit.mk.injEq, heq_eq_eq, true_and]
  exact ⟨funext fun X => Iso.ext (hl X), funext fun X => Iso.ext (hr X)⟩

lemma l_tensor_hom (X : C) : (u.l (T.obj (u.obj, X))).hom = tensorMap T (𝟙 u.obj) (u.l X).hom := by
  rw [← cancel_mono (u.l X).hom, u.l_naturality]

lemma r_tensor_hom (X : C) : (u.r (T.obj (X, u.obj))).hom = tensorMap T (u.r X).hom (𝟙 u.obj) := by
  rw [← cancel_mono (u.r X).hom, u.r_naturality]

/-- The isomorphism `𝟭 C ≅ L`, `L : X ↦ 𝟏 ⊗ X`, given by `l`. -/
def leftIso : 𝟭 C ≅ Prod.sectR u.obj C ⋙ T :=
  (NatIso.ofComponents (fun X => u.l X) (fun f => by
    rw [sectR_comp_map]; exact u.l_naturality f)).symm

/-- The isomorphism `𝟭 C ≅ R`, `R : X ↦ X ⊗ 𝟏`, given by `r`. -/
def rightIso : 𝟭 C ≅ Prod.sectL C u.obj ⋙ T :=
  (NatIso.ofComponents (fun X => u.r X) (fun f => by
    rw [sectL_comp_map]; exact u.r_naturality f)).symm

lemma isEquivalence_left : (Prod.sectR u.obj C ⋙ T).IsEquivalence :=
  Functor.isEquivalence_of_iso u.leftIso

lemma isEquivalence_right : (Prod.sectL C u.obj ⋙ T).IsEquivalence :=
  Functor.isEquivalence_of_iso u.rightIso

/-- The pair `(𝟏, r_𝟏)` attached to a unit `(𝟏, l, r)`. -/
def toUnitPair : UnitPair T where
  obj := u.obj
  iso := u.r u.obj
  isEquivalence_left := u.isEquivalence_left
  isEquivalence_right := u.isEquivalence_right

/-- The monoidal category structure on `C` given by `T`, `φ⁻¹` and a unit `(𝟏, l, r)`. -/
@[implicit_reducible]
def monoidalCategoryStruct : MonoidalCategoryStruct C where
  tensorObj X Y := T.obj (X, Y)
  whiskerLeft X _ _ f := tensorMap T (𝟙 X) f
  whiskerRight f Y := tensorMap T f (𝟙 Y)
  tensorHom f g := tensorMap T f g
  tensorUnit := u.obj
  associator X Y Z := (φ.iso X Y Z).symm
  leftUnitor := u.l
  rightUnitor := u.r

/-- The monoidal category structure on `C` given by `T`, `φ⁻¹` and a unit `(𝟏, l, r)`. -/
@[implicit_reducible]
def monoidalCategory : MonoidalCategory C :=
  letI := u.monoidalCategoryStruct
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun X Y => tensorMap_id T X Y)
    (id_tensorHom := fun _ _ _ _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ => tensorMap_comp_tensorMap T f₁ g₁ f₂ g₂)
    (associator_naturality := fun f₁ f₂ f₃ => by
      change tensorMap T (tensorMap T f₁ f₂) f₃ ≫ (φ.iso _ _ _).inv =
        (φ.iso _ _ _).inv ≫ tensorMap T f₁ (tensorMap T f₂ f₃)
      exact φ.naturality_inv f₁ f₂ f₃)
    (leftUnitor_naturality := fun f => u.l_naturality f)
    (rightUnitor_naturality := fun f => u.r_naturality f)
    (pentagon := fun X Y Z W => by
      change tensorMap T (φ.iso X Y Z).inv (𝟙 W) ≫ (φ.iso X (T.obj (Y, Z)) W).inv ≫
          tensorMap T (𝟙 X) (φ.iso Y Z W).inv =
        (φ.iso (T.obj (X, Y)) Z W).inv ≫ (φ.iso X Y (T.obj (Z, W))).inv
      have h : φ.iso X Y (T.obj (Z, W)) ≪≫ φ.iso (T.obj (X, Y)) Z W =
          tensorIso T (Iso.refl X) (φ.iso Y Z W) ≪≫ φ.iso X (T.obj (Y, Z)) W ≪≫
            tensorIso T (φ.iso X Y Z) (Iso.refl W) := Iso.ext (φ.pentagon X Y Z W)
      have := congrArg Iso.inv h
      simp only [Iso.trans_inv, tensorIso_inv, Iso.refl_inv, assoc] at this
      exact this.symm)
    (triangle := fun X Y => by
      change (φ.iso X u.obj Y).inv ≫ tensorMap T (𝟙 X) (u.l Y).hom =
        tensorMap T (u.r X).hom (𝟙 Y)
      rw [← u.triangle, Iso.inv_hom_id_assoc])

lemma l_obj_eq_r_obj : (u.l u.obj).hom = (u.r u.obj).hom := by
  let _ : MonoidalCategory C := u.monoidalCategory
  exact MonoidalCategory.unitors_equal

end MonoidalUnit

namespace UnitPair

variable {φ} (p : UnitPair T)

lemma mk_eq (e : T.obj (p.obj, p.obj) ≅ p.obj)
    (hL : (Prod.sectR p.obj C ⋙ T).IsEquivalence) (hR : (Prod.sectL C p.obj ⋙ T).IsEquivalence)
    (h : e.hom = p.iso.hom) :
    (⟨p.obj, e, hL, hR⟩ : UnitPair T) = p := by
  obtain ⟨o, e', _, _⟩ := p
  simp only [UnitPair.mk.injEq, true_and]
  exact heq_of_eq (Iso.ext h)

/-- `L : X ↦ 𝟏 ⊗ X` is fully faithful. -/
def fullyFaithfulLeft : (Prod.sectR p.obj C ⋙ T).FullyFaithful :=
  haveI := p.isEquivalence_left
  Functor.FullyFaithful.ofFullyFaithful _

/-- `R : X ↦ X ⊗ 𝟏` is fully faithful. -/
def fullyFaithfulRight : (Prod.sectL C p.obj ⋙ T).FullyFaithful :=
  haveI := p.isEquivalence_right
  Functor.FullyFaithful.ofFullyFaithful _

variable (φ)

/-- The isomorphism `l_X : 𝟏 ⊗ X ≅ X` characterized by `id_𝟏 ⊗ l_X = (1 ⊗ id_X) ∘ φ_{𝟏,𝟏,X}`. -/
def l (X : C) : T.obj (p.obj, X) ≅ X :=
  p.fullyFaithfulLeft.preimageIso (φ.iso p.obj p.obj X ≪≫ tensorIso T p.iso (Iso.refl X))

/-- The isomorphism `r_X : X ⊗ 𝟏 ≅ X` characterized by
`r_X ⊗ id_𝟏 = (id_X ⊗ 1) ∘ φ_{X,𝟏,𝟏}⁻¹`. -/
def r (X : C) : T.obj (X, p.obj) ≅ X :=
  p.fullyFaithfulRight.preimageIso ((φ.iso X p.obj p.obj).symm ≪≫ tensorIso T (Iso.refl X) p.iso)

lemma tensorMap_l (X : C) :
    tensorMap T (𝟙 p.obj) (p.l φ X).hom =
      (φ.iso p.obj p.obj X).hom ≫ tensorMap T p.iso.hom (𝟙 X) := by
  rw [← sectR_comp_map]
  exact p.fullyFaithfulLeft.map_preimage _

lemma tensorMap_r (X : C) :
    tensorMap T (p.r φ X).hom (𝟙 p.obj) =
      (φ.iso X p.obj p.obj).inv ≫ tensorMap T (𝟙 X) p.iso.hom := by
  rw [← sectL_comp_map]
  exact p.fullyFaithfulRight.map_preimage _

lemma tensorMap_l_injective {X Y : C} {f g : T.obj (p.obj, X) ⟶ Y}
    (h : tensorMap T (𝟙 p.obj) f = tensorMap T (𝟙 p.obj) g) : f = g :=
  p.fullyFaithfulLeft.map_injective h

lemma tensorMap_r_injective {X Y : C} {f g : T.obj (X, p.obj) ⟶ Y}
    (h : tensorMap T f (𝟙 p.obj) = tensorMap T g (𝟙 p.obj)) : f = g :=
  p.fullyFaithfulRight.map_injective h

lemma l_naturality {X Y : C} (f : X ⟶ Y) :
    tensorMap T (𝟙 p.obj) f ≫ (p.l φ Y).hom = (p.l φ X).hom ≫ f := by
  apply p.tensorMap_l_injective
  rw [tensorMap_id_comp, tensorMap_id_comp, tensorMap_l, tensorMap_l,
    reassoc_of% (φ.naturality (𝟙 p.obj) (𝟙 p.obj) f)]
  simp

lemma r_naturality {X Y : C} (f : X ⟶ Y) :
    tensorMap T f (𝟙 p.obj) ≫ (p.r φ Y).hom = (p.r φ X).hom ≫ f := by
  apply p.tensorMap_r_injective
  rw [tensorMap_comp_id, tensorMap_comp_id, tensorMap_r, tensorMap_r,
    φ.naturality_inv_assoc f (𝟙 p.obj) (𝟙 p.obj)]
  simp

lemma l_tensor_hom (X : C) :
    (p.l φ (T.obj (p.obj, X))).hom = tensorMap T (𝟙 p.obj) (p.l φ X).hom := by
  rw [← cancel_mono (p.l φ X).hom, p.l_naturality]

/-- The triangle axiom for `Y` of the form `𝟏 ⊗ W`. -/
lemma triangle_tensor (X W : C) :
    (φ.iso X p.obj (T.obj (p.obj, W))).hom ≫ tensorMap T (p.r φ X).hom (𝟙 _) =
      tensorMap T (𝟙 X) (p.l φ (T.obj (p.obj, W))).hom := by
  rw [l_tensor_hom, tensorMap_l, ← cancel_mono (φ.iso X p.obj W).hom, assoc]
  have h₁ := φ.naturality (p.r φ X).hom (𝟙 p.obj) (𝟙 W)
  rw [tensorMap_id] at h₁
  rw [h₁, reassoc_of% (φ.pentagon X p.obj p.obj W), tensorMap_id_comp, assoc,
    φ.naturality (𝟙 X) p.iso.hom (𝟙 W), tensorMap_comp_tensorMap, tensorMap_r,
    Iso.hom_inv_id_assoc]
  simp

lemma triangle (X Y : C) :
    (φ.iso X p.obj Y).hom ≫ tensorMap T (p.r φ X).hom (𝟙 Y) =
      tensorMap T (𝟙 X) (p.l φ Y).hom := by
  have := p.isEquivalence_left
  let i : T.obj (p.obj, (Prod.sectR p.obj C ⋙ T).objPreimage Y) ≅ Y :=
    (Prod.sectR p.obj C ⋙ T).objObjPreimageIso Y
  rw [← cancel_epi (tensorIso T (Iso.refl X) (tensorIso T (Iso.refl p.obj) i)).hom]
  simp only [tensorIso_hom, Iso.refl_hom]
  have e₁ : tensorMap T (tensorMap T (𝟙 X) (𝟙 p.obj)) i.hom ≫ tensorMap T (p.r φ X).hom (𝟙 Y) =
      tensorMap T (p.r φ X).hom (𝟙 _) ≫ tensorMap T (𝟙 X) i.hom := by
    simp
  rw [reassoc_of% (φ.naturality (𝟙 X) (𝟙 p.obj) i.hom), e₁, reassoc_of% (p.triangle_tensor φ X),
    tensorMap_comp_tensorMap, tensorMap_comp_tensorMap, p.l_naturality]

/-- The unit `(𝟏, l, r)` attached to a pair `(𝟏, 1)`. -/
def toUnit : φ.MonoidalUnit where
  obj := p.obj
  l := p.l φ
  r := p.r φ
  l_naturality := p.l_naturality φ
  r_naturality := p.r_naturality φ
  triangle := p.triangle φ

end UnitPair

/-- **Stacks 0HAW.** For a category `C` with a functor `⊗ = T : C × C ⥤ C` and an associativity
constraint `φ`, units `(𝟏, l, r)` correspond one-to-one to pairs `(𝟏, 1)` where
`1 : 𝟏 ⊗ 𝟏 ≅ 𝟏` is an isomorphism such that `X ↦ 𝟏 ⊗ X` and `X ↦ X ⊗ 𝟏` are equivalences.
The correspondence sends `(𝟏, l, r)` to `(𝟏, r_𝟏)` (`unitEquivUnitPair_apply_obj`,
`unitEquivUnitPair_apply_iso`). -/
@[stacks 0HAW "the correspondence sends `(𝟏, l, r)` to `(𝟏, r_𝟏)`; its inverse sends `(𝟏, 1)` to
the unit with `id_𝟏 ⊗ l_X = (1 ⊗ id_X) ∘ φ` and `r_X ⊗ id_𝟏 = (id_X ⊗ 1) ∘ φ⁻¹`"]
def unitEquivUnitPair : φ.MonoidalUnit ≃ UnitPair T where
  toFun u := u.toUnitPair
  invFun p := p.toUnit φ
  left_inv u := by
    change (⟨u.obj, u.toUnitPair.l φ, u.toUnitPair.r φ, _, _, _⟩ : φ.MonoidalUnit) = u
    refine u.mk_eq _ _ _ _ _ (fun X => ?_) (fun X => ?_)
    · apply u.toUnitPair.tensorMap_l_injective
      rw [u.toUnitPair.tensorMap_l φ]
      exact u.triangle u.obj X
    · apply u.toUnitPair.tensorMap_r_injective
      rw [u.toUnitPair.tensorMap_r φ, Iso.inv_comp_eq]
      exact (congrArg (tensorMap T (𝟙 X)) u.l_obj_eq_r_obj).symm.trans (u.triangle X u.obj).symm
  right_inv p := by
    change (⟨p.obj, p.r φ p.obj, _, _⟩ : UnitPair T) = p
    refine p.mk_eq _ _ _ (p.tensorMap_r_injective ((cancel_epi (φ.iso p.obj p.obj p.obj).hom).1 ?_))
    rw [p.triangle φ, p.tensorMap_l φ]

lemma unitEquivUnitPair_apply_obj (u : φ.MonoidalUnit) : (φ.unitEquivUnitPair u).obj = u.obj :=
  rfl

lemma unitEquivUnitPair_apply_iso (u : φ.MonoidalUnit) : (φ.unitEquivUnitPair u).iso = u.r u.obj :=
  rfl

lemma unitEquivUnitPair_symm_apply_obj (p : UnitPair T) :
    (φ.unitEquivUnitPair.symm p).obj = p.obj :=
  rfl

lemma tensorMap_unitEquivUnitPair_symm_apply_l (p : UnitPair T) (X : C) :
    tensorMap T (𝟙 p.obj) ((φ.unitEquivUnitPair.symm p).l X).hom =
      (φ.iso p.obj p.obj X).hom ≫ tensorMap T p.iso.hom (𝟙 X) :=
  p.tensorMap_l φ X

lemma tensorMap_unitEquivUnitPair_symm_apply_r (p : UnitPair T) (X : C) :
    tensorMap T ((φ.unitEquivUnitPair.symm p).r X).hom (𝟙 p.obj) =
      (φ.iso X p.obj p.obj).inv ≫ tensorMap T (𝟙 X) p.iso.hom :=
  p.tensorMap_r φ X

end AssociativityConstraint

end CategoryTheory
