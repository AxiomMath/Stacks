module

public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import StacksFrontier.CategoryTheory.KanExtension.Extend
import StacksCore.Tactic.EgaSgaAttribute

/-! # Extending a tensor functor from compact generators

Let `C` and `D` be monoidal categories, let `P` be a monoidal property of objects of `C` cutting
out a locally small full subcategory of categorically compact objects (Stacks 0FWX) such that
every object of `C` is a filtered colimit of `P`-objects, and assume that tensoring on either
side commutes with filtered colimits in `C` and in `D`. Then the extension `F : C ⥤ D`
commuting with filtered colimits of a functor `F'` out of the `P`-objects (Stacks 0FWY) inherits
a structure of *functor of monoidal categories* (Stacks 0FFL) from one on `F'`, compatibly with
the identification of the restriction of `F` with `F'`. This is the paragraph "since `F` is a
tensor functor and since colimits of modules commute with taking tensor products, also the
extension of `F` is a tensor functor" of the proof of Stacks 0GRJ.

## Main definitions

* `CategoryTheory.MonoidalCategory.IsUnitObject`: a *unit* in the sense of the Stacks project
  (Categories, Section 0FFJ): an object `E` with functorial isomorphisms `E ⊗ X ≅ X` and
  `X ⊗ E ≅ X` satisfying the triangle identity.
* `CategoryTheory.Functor.TensorStructure`: **Stacks 0FFL**, a functor of monoidal categories:
  a natural isomorphism `F X ⊗ F Y ≅ F (X ⊗ Y)` satisfying the associativity diagram, such that
  `F 𝟙` is a unit. No compatibility with unitors is asked for, so this is weaker than Mathlib's
  `CategoryTheory.Functor.Monoidal`; see `CategoryTheory.Functor.Monoidal.toTensorStructure`.

## Main results

* `CategoryTheory.MonoidalCategory.isUnitObject_iff`: a unit is the same as an object isomorphic
  to the monoidal unit (the source's "a unit is unique up to unique isomorphism").
* `CategoryTheory.ObjectProperty.exists_extension_of_locallySmall`: Stacks 0FWY (existence) under
  local smallness of the subcategory only.
* `CategoryTheory.ObjectProperty.tensorStructureExtension`: the tensor structure on the
  extension.
-/

@[expose] public section

open CategoryTheory Category Limits ObjectProperty MonoidalCategory

universe w v v' u u'

namespace CategoryTheory

namespace MonoidalCategory

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

/-- A *unit* of a monoidal category in the sense of the Stacks project (Categories, the
discussion preceding Definition 0FFK): an object `E` together with functorial isomorphisms
`E ⊗ X ≅ X` and `X ⊗ E ≅ X` such that the triangle `X ⊗ (E ⊗ Y) ⟶ (X ⊗ E) ⊗ Y ⟶ X ⊗ Y`
commutes. -/
def IsUnitObject (E : D) : Prop :=
  ∃ (l : tensorLeft E ≅ 𝟭 D) (r : tensorRight E ≅ 𝟭 D),
    ∀ X Y : D, X ◁ l.hom.app Y = (α_ X E Y).inv ≫ r.hom.app X ▷ Y

/-- A unit of a monoidal category is an object isomorphic to its monoidal unit, and conversely
(the source: "a unit is unique up to unique isomorphism if it exists"). -/
theorem isUnitObject_iff (E : D) : IsUnitObject E ↔ Nonempty (E ≅ 𝟙_ D) := by
  constructor
  · rintro ⟨-, r, -⟩
    exact ⟨(λ_ E).symm ≪≫ r.app (𝟙_ D)⟩
  · rintro ⟨e⟩
    refine ⟨NatIso.ofComponents (fun X ↦ whiskerRightIso e X ≪≫ λ_ X) (fun f ↦ ?_),
      NatIso.ofComponents (fun X ↦ whiskerLeftIso X e ≪≫ ρ_ X) (fun f ↦ ?_), fun X Y ↦ ?_⟩
    · simp [whisker_exchange_assoc]
    · simp [← whisker_exchange_assoc]
    · simp only [NatIso.ofComponents_hom_app, Iso.trans_hom, whiskerRightIso_hom,
        whiskerLeftIso_hom, comp_whiskerRight, whiskerLeft_comp]
      rw [← associator_inv_naturality_middle_assoc]
      simp

/-- An object isomorphic to a unit is a unit. -/
theorem IsUnitObject.of_iso {E E' : D} (h : IsUnitObject E) (e : E ≅ E') : IsUnitObject E' :=
  (isUnitObject_iff _).2 (((isUnitObject_iff _).1 h).map (e.symm ≪≫ ·))

/-- The monoidal unit `𝟙_ D` is a unit. -/
theorem isUnitObject_tensorUnit : IsUnitObject (𝟙_ D) :=
  (isUnitObject_iff _).2 ⟨Iso.refl _⟩

end MonoidalCategory

namespace Functor

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  [MonoidalCategory C] [MonoidalCategory D]

/-- **Stacks 0FFL.** A *functor of monoidal categories* `F : C ⥤ D`: an isomorphism
`F(X) ⊗ F(Y) ⟶ F(X ⊗ Y)` functorial in `X` and `Y` such that for all `X, Y, Z` the diagram
```
F(X) ⊗ (F(Y) ⊗ F(Z)) ⟶ F(X) ⊗ F(Y ⊗ Z) ⟶ F(X ⊗ (Y ⊗ Z))
        |                                         |
(F(X) ⊗ F(Y)) ⊗ F(Z) ⟶ F(X ⊗ Y) ⊗ F(Z) ⟶ F((X ⊗ Y) ⊗ Z)
```
commutes (the vertical arrows being the associativity constraints), and such that `F(𝟙)` is a
unit (`CategoryTheory.MonoidalCategory.IsUnitObject`). -/
structure TensorStructure (F : C ⥤ D) where
  /-- The isomorphism `F(X) ⊗ F(Y) ≅ F(X ⊗ Y)`. -/
  μIso (X Y : C) : F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y)
  μIso_natural_left {X X' : C} (f : X ⟶ X') (Y : C) :
    F.map f ▷ F.obj Y ≫ (μIso X' Y).hom = (μIso X Y).hom ≫ F.map (f ▷ Y)
  μIso_natural_right (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    F.obj X ◁ F.map g ≫ (μIso X Y').hom = (μIso X Y).hom ≫ F.map (X ◁ g)
  associativity (X Y Z : C) :
    F.obj X ◁ (μIso Y Z).hom ≫ (μIso X (Y ⊗ Z)).hom ≫ F.map (α_ X Y Z).inv =
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫ (μIso X Y).hom ▷ F.obj Z ≫
        (μIso (X ⊗ Y) Z).hom
  isUnitObject_obj_tensorUnit : IsUnitObject (F.obj (𝟙_ C))

attribute [reassoc] TensorStructure.μIso_natural_left TensorStructure.μIso_natural_right
  TensorStructure.associativity

/-- A (strong) monoidal functor in the sense of Mathlib is a functor of monoidal categories in
the sense of Stacks 0FFL. -/
noncomputable def Monoidal.toTensorStructure (F : C ⥤ D) [F.Monoidal] : F.TensorStructure where
  μIso X Y := Monoidal.μIso F X Y
  μIso_natural_left f Y := by simp
  μIso_natural_right X g := by simp
  associativity X Y Z := by
    simp only [Monoidal.μIso_hom]
    rw [← cancel_epi (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom]
    simp only [Iso.hom_inv_id_assoc]
    rw [← LaxMonoidal.associativity_assoc F X Y Z]
    simp
  isUnitObject_obj_tensorUnit :=
    isUnitObject_tensorUnit.of_iso (Monoidal.εIso F)

/-- An isomorphism `e : F ≅ G` of functors between monoidal categories is compatible with tensor
structures on `F` and `G` when it intertwines their isomorphisms `F X ⊗ F Y ≅ F (X ⊗ Y)` and
`G X ⊗ G Y ≅ G (X ⊗ Y)`. -/
def TensorStructure.IsCompatible {F G : C ⥤ D} (hF : F.TensorStructure) (hG : G.TensorStructure)
    (e : F ≅ G) : Prop :=
  ∀ X Y : C, (hF.μIso X Y).hom ≫ e.hom.app (X ⊗ Y) =
    (e.hom.app X ⊗ₘ e.hom.app Y) ≫ (hG.μIso X Y).hom

/-- Transport of a functor-of-monoidal-categories structure along a natural isomorphism. -/
noncomputable def TensorStructure.ofIso {F G : C ⥤ D} (hG : G.TensorStructure) (e : F ≅ G) :
    F.TensorStructure where
  μIso X Y := (e.app X ⊗ᵢ e.app Y) ≪≫ hG.μIso X Y ≪≫ (e.app (X ⊗ Y)).symm
  μIso_natural_left {X X'} f Y := by
    simp only [Iso.trans_hom, tensorIso_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, assoc]
    rw [← e.inv.naturality (f ▷ Y), reassoc_of% (hG.μIso_natural_left f Y).symm]
    simp only [← assoc]
    congr 2
    rw [← tensorHom_id, tensorHom_comp_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom,
      e.hom.naturality f]
    simp
  μIso_natural_right X {Y Y'} g := by
    simp only [Iso.trans_hom, tensorIso_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, assoc]
    rw [← e.inv.naturality (X ◁ g), reassoc_of% (hG.μIso_natural_right X g).symm]
    simp only [← assoc]
    congr 2
    rw [← id_tensorHom, tensorHom_comp_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom,
      e.hom.naturality g]
    simp
  associativity X Y Z := by
    simp only [Iso.trans_hom, tensorIso_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, assoc]
    have hn : e.inv.app (X ⊗ (Y ⊗ Z)) ≫ F.map (α_ X Y Z).inv =
        G.map (α_ X Y Z).inv ≫ e.inv.app ((X ⊗ Y) ⊗ Z) := (e.inv.naturality _).symm
    have L : F.obj X ◁ ((e.hom.app Y ⊗ₘ e.hom.app Z) ≫ (hG.μIso Y Z).hom ≫ e.inv.app (Y ⊗ Z)) ≫
        (e.hom.app X ⊗ₘ e.hom.app (Y ⊗ Z)) =
          (e.hom.app X ⊗ₘ (e.hom.app Y ⊗ₘ e.hom.app Z)) ≫ G.obj X ◁ (hG.μIso Y Z).hom := by
      rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
      simp
    have R : ((e.hom.app X ⊗ₘ e.hom.app Y) ≫ (hG.μIso X Y).hom ≫ e.inv.app (X ⊗ Y)) ▷ F.obj Z ≫
        (e.hom.app (X ⊗ Y) ⊗ₘ e.hom.app Z) =
          ((e.hom.app X ⊗ₘ e.hom.app Y) ⊗ₘ e.hom.app Z) ≫ (hG.μIso X Y).hom ▷ G.obj Z := by
      rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
      simp
    rw [hn, reassoc_of% L, reassoc_of% R, hG.associativity_assoc,
      ← associator_inv_naturality_assoc]
  isUnitObject_obj_tensorUnit := hG.isUnitObject_obj_tensorUnit.of_iso (e.app _).symm

/-- Restriction of a functor-of-monoidal-categories structure to a full monoidal subcategory. -/
def TensorStructure.restrict {F : C ⥤ D} (hF : F.TensorStructure) (P : ObjectProperty C)
    [P.IsMonoidal] : (P.ι ⋙ F).TensorStructure where
  μIso X Y := hF.μIso X.obj Y.obj
  μIso_natural_left f Y := hF.μIso_natural_left f.hom Y.obj
  μIso_natural_right X _ _ g := hF.μIso_natural_right X.obj g.hom
  associativity X Y Z := hF.associativity X.obj Y.obj Z.obj
  isUnitObject_obj_tensorUnit := hF.isUnitObject_obj_tensorUnit

/-- The isomorphism `F X ⊗ F Y ≅ F (X ⊗ Y)` of the transported structure `hG.ofIso e` is
`e X ⊗ e Y`, followed by the one of `G`, followed by the inverse of `e (X ⊗ Y)`. -/
theorem TensorStructure.ofIso_μIso_hom {F G : C ⥤ D} (hG : G.TensorStructure) (e : F ≅ G)
    (X Y : C) : ((hG.ofIso e).μIso X Y).hom =
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫ (hG.μIso X Y).hom ≫ e.inv.app (X ⊗ Y) := rfl

end Functor

namespace ObjectProperty

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (P : ObjectProperty C)

section Uniqueness

variable [LocallySmall.{w} P.FullSubcategory]
  (hP : P ≤ isFinitelyPresentable.{w} C) (hgen : ∀ X : C, P.ind.{w} X)

include hP hgen

/-- Two natural transformations out of a functor commuting with filtered colimits agree as soon
as they agree on the `P`-objects. -/
theorem natTrans_ext_of_preservesFilteredColimits {F₁ F₂ : C ⥤ D}
    [PreservesFilteredColimitsOfSize.{w, w} F₁] {α β : F₁ ⟶ F₂}
    (h : ∀ X : P.FullSubcategory, α.app X.obj = β.app X.obj) : α = β :=
  (existsUnique_natTrans_of_preservesFilteredColimits.{w} P hP hgen F₁ F₂
    (Functor.whiskerLeft P.ι α)).unique rfl (by ext X; exact (h X).symm)

/-- Two natural families of maps out of a functor commuting with filtered colimits agree as soon
as they agree on the `P`-objects. -/
theorem app_eq_of_preservesFilteredColimits (F₁ F₂ : C ⥤ D)
    [PreservesFilteredColimitsOfSize.{w, w} F₁] (a b : ∀ X, F₁.obj X ⟶ F₂.obj X)
    (ha : ∀ {X Y : C} (f : X ⟶ Y), F₁.map f ≫ a Y = a X ≫ F₂.map f)
    (hb : ∀ {X Y : C} (f : X ⟶ Y), F₁.map f ≫ b Y = b X ≫ F₂.map f)
    (h : ∀ X : P.FullSubcategory, a X.obj = b X.obj) (X : C) : a X = b X :=
  congr_arg (fun α : F₁ ⟶ F₂ ↦ α.app X)
    (natTrans_ext_of_preservesFilteredColimits (α := ⟨a, @ha⟩) (β := ⟨b, @hb⟩) P hP hgen h)

/-- A natural isomorphism between the restrictions to the `P`-objects of two functors commuting
with filtered colimits extends to a natural isomorphism between the functors. -/
@[sga "4 I 8.7.2" "Existence clause"]
noncomputable def natIsoOfPreservesFilteredColimits (F₁ F₂ : C ⥤ D)
    [PreservesFilteredColimitsOfSize.{w, w} F₁] [PreservesFilteredColimitsOfSize.{w, w} F₂]
    (τ : P.ι ⋙ F₁ ≅ P.ι ⋙ F₂) : F₁ ≅ F₂ :=
  let u := (existsUnique_natTrans_of_preservesFilteredColimits.{w} P hP hgen F₁ F₂ τ.hom).exists
  let v := (existsUnique_natTrans_of_preservesFilteredColimits.{w} P hP hgen F₂ F₁ τ.inv).exists
  have hu (X : P.FullSubcategory) : u.choose.app X.obj = τ.hom.app X :=
    congr_arg (fun α ↦ α.app X) u.choose_spec
  have hv (X : P.FullSubcategory) : v.choose.app X.obj = τ.inv.app X :=
    congr_arg (fun α ↦ α.app X) v.choose_spec
  { hom := u.choose
    inv := v.choose
    hom_inv_id := natTrans_ext_of_preservesFilteredColimits P hP hgen fun X ↦ by
      rw [NatTrans.comp_app, hu, hv]
      exact congr_arg (fun α ↦ α.app X) τ.hom_inv_id
    inv_hom_id := natTrans_ext_of_preservesFilteredColimits P hP hgen fun X ↦ by
      rw [NatTrans.comp_app, hu, hv]
      exact congr_arg (fun α ↦ α.app X) τ.inv_hom_id }

/-- On a `P`-object, the extended natural isomorphism `natIsoOfPreservesFilteredColimits` agrees
with the given isomorphism `τ`. -/
@[simp]
theorem natIsoOfPreservesFilteredColimits_hom_app (F₁ F₂ : C ⥤ D)
    [PreservesFilteredColimitsOfSize.{w, w} F₁] [PreservesFilteredColimitsOfSize.{w, w} F₂]
    (τ : P.ι ⋙ F₁ ≅ P.ι ⋙ F₂) (X : P.FullSubcategory) :
    (natIsoOfPreservesFilteredColimits P hP hgen F₁ F₂ τ).hom.app X.obj = τ.hom.app X :=
  congr_arg (fun α ↦ α.app X)
    (existsUnique_natTrans_of_preservesFilteredColimits.{w} P hP hgen F₁ F₂
      τ.hom).exists.choose_spec

/-- **Stacks 0FWY** (existence), with the subcategory only assumed locally small. -/
theorem exists_extension_of_locallySmall [HasFilteredColimitsOfSize.{w, w} D]
    (F' : P.FullSubcategory ⥤ D) :
    ∃ F : C ⥤ D, PreservesFilteredColimitsOfSize.{w, w} F ∧ Nonempty (P.ι ⋙ F ≅ F') := by
  have hpt : P.ι.HasPointwiseLeftKanExtension F' :=
    hasPointwiseLeftKanExtension_ι P hP hgen F'
  have hEx := Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension P.ι F'
  refine ⟨P.ι.pointwiseLeftKanExtension F', ?_, ?_⟩
  · exact preservesFilteredColimitsOfSize_right P hP
      (Functor.LeftExtension.mk _ (Functor.pointwiseLeftKanExtensionUnit P.ι F')) hEx
  · have : IsIso (Functor.pointwiseLeftKanExtensionUnit P.ι F') := hEx.isIso_hom
    exact ⟨(asIso (Functor.pointwiseLeftKanExtensionUnit P.ι F')).symm⟩

end Uniqueness

section TensorExtension

variable [MonoidalCategory C] [MonoidalCategory D] [P.IsMonoidal]
  [LocallySmall.{w} P.FullSubcategory]
  (hP : P ≤ isFinitelyPresentable.{w} C) (hgen : ∀ X : C, P.ind.{w} X)
  [∀ X : C, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ X : C, PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]
  [∀ X : D, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ X : D, PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]
  (F : C ⥤ D) [PreservesFilteredColimitsOfSize.{w, w} F]
  {F' : P.FullSubcategory ⥤ D} (e : P.ι ⋙ F ≅ F') (hF' : F'.TensorStructure)

/-- The tensor isomorphism of the extension, for `X` and `Y` both `P`-objects: transport of the
one of `F'` along `e`. -/
noncomputable def tensorExtensionAux (Y : P.FullSubcategory) :
    P.ι ⋙ (F ⋙ tensorRight (F.obj Y.obj)) ≅ P.ι ⋙ (tensorRight Y.obj ⋙ F) :=
  NatIso.ofComponents
    (fun X ↦ (e.app X ⊗ᵢ e.app Y) ≪≫ hF'.μIso X Y ≪≫ (e.app (X ⊗ Y)).symm)
    (fun {X X'} f ↦ by
      have h₁ : F.map f.hom ≫ e.hom.app X' = e.hom.app X ≫ F'.map f := e.hom.naturality f
      have h₂ : F'.map (f ▷ Y) ≫ e.inv.app (X' ⊗ Y) =
          e.inv.app (X ⊗ Y) ≫ F.map (f.hom ▷ Y.obj) := e.inv.naturality (f ▷ Y)
      have h₃ := hF'.μIso_natural_left f Y
      change F.map f.hom ▷ _ ≫ (e.hom.app X' ⊗ₘ e.hom.app Y) ≫ (hF'.μIso X' Y).hom ≫
          e.inv.app (X' ⊗ Y) =
        ((e.hom.app X ⊗ₘ e.hom.app Y) ≫ (hF'.μIso X Y).hom ≫ e.inv.app (X ⊗ Y)) ≫
          F.map (f.hom ▷ Y.obj)
      rw [assoc, assoc, ← h₂, reassoc_of% h₃.symm]
      simp only [← assoc]
      congr 2
      rw [← tensorHom_id, tensorHom_comp_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom,
        h₁]
      simp)

/-- The tensor isomorphism of the extension, extended in the first variable. -/
noncomputable def tensorExtensionLeft (Y : P.FullSubcategory) :
    F ⋙ tensorRight (F.obj Y.obj) ≅ tensorRight Y.obj ⋙ F :=
  natIsoOfPreservesFilteredColimits P hP hgen _ _ (tensorExtensionAux P F e hF' Y)

omit [∀ X : C, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ X : D, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)] in
/-- On two `P`-objects, `tensorExtensionLeft` is the tensor isomorphism of `F'` transported
along `e`. -/
theorem tensorExtensionLeft_hom_app (X Y : P.FullSubcategory) :
    (tensorExtensionLeft P hP hgen F e hF' Y).hom.app X.obj =
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫ (hF'.μIso X Y).hom ≫ e.inv.app (X ⊗ Y) := by
  simp [tensorExtensionLeft, tensorExtensionAux]

omit [∀ X : C, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ X : D, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)] in
/-- The isomorphisms `tensorExtensionLeft` are natural in the second variable, ranging over the
`P`-objects. -/
theorem tensorExtensionLeft_naturality_right (X : C) {Y Y' : P.FullSubcategory} (g : Y ⟶ Y') :
    F.obj X ◁ F.map g.hom ≫ (tensorExtensionLeft P hP hgen F e hF' Y').hom.app X =
      (tensorExtensionLeft P hP hgen F e hF' Y).hom.app X ≫ F.map (X ◁ g.hom) := by
  refine app_eq_of_preservesFilteredColimits P hP hgen (F ⋙ tensorRight (F.obj Y.obj))
    (tensorRight Y'.obj ⋙ F) (fun X ↦ F.obj X ◁ F.map g.hom ≫
      (tensorExtensionLeft P hP hgen F e hF' Y').hom.app X)
    (fun X ↦ (tensorExtensionLeft P hP hgen F e hF' Y).hom.app X ≫ F.map (X ◁ g.hom))
    (fun {X₁ X₂} f ↦ ?_) (fun {X₁ X₂} f ↦ ?_) (fun X ↦ ?_) X
  · have : F.map f ▷ F.obj Y'.obj ≫ (tensorExtensionLeft P hP hgen F e hF' Y').hom.app X₂ =
        (tensorExtensionLeft P hP hgen F e hF' Y').hom.app X₁ ≫ F.map (f ▷ Y'.obj) :=
      (tensorExtensionLeft P hP hgen F e hF' Y').hom.naturality f
    change F.map f ▷ _ ≫ _ ◁ F.map g.hom ≫ _ = (_ ◁ F.map g.hom ≫ _) ≫ F.map (f ▷ Y'.obj)
    rw [← whisker_exchange_assoc, this, assoc]
  · have : F.map f ▷ F.obj Y.obj ≫ (tensorExtensionLeft P hP hgen F e hF' Y).hom.app X₂ =
        (tensorExtensionLeft P hP hgen F e hF' Y).hom.app X₁ ≫ F.map (f ▷ Y.obj) :=
      (tensorExtensionLeft P hP hgen F e hF' Y).hom.naturality f
    change F.map f ▷ _ ≫ _ ≫ F.map (X₂ ◁ g.hom) = (_ ≫ F.map (X₁ ◁ g.hom)) ≫ F.map (f ▷ Y'.obj)
    rw [reassoc_of% this, assoc, ← F.map_comp, ← F.map_comp, whisker_exchange]
  · change _ ◁ F.map g.hom ≫ (tensorExtensionLeft P hP hgen F e hF' Y').hom.app X.obj =
      (tensorExtensionLeft P hP hgen F e hF' Y).hom.app X.obj ≫ F.map (X.obj ◁ g.hom)
    simp only [tensorExtensionLeft_hom_app]
    exact (hF'.ofIso e).μIso_natural_right X g

/-- The tensor isomorphism of the extension, for `X` arbitrary and `Y` a `P`-object, as a natural
isomorphism in `Y`. -/
noncomputable def tensorExtensionAux' (X : C) :
    P.ι ⋙ (F ⋙ tensorLeft (F.obj X)) ≅ P.ι ⋙ (tensorLeft X ⋙ F) :=
  NatIso.ofComponents (fun Y ↦ (tensorExtensionLeft P hP hgen F e hF' Y).app X)
    (fun g ↦ tensorExtensionLeft_naturality_right P hP hgen F e hF' X g)

/-- The tensor isomorphism of the extension, extended in both variables. -/
noncomputable def tensorExtensionRight (X : C) :
    F ⋙ tensorLeft (F.obj X) ≅ tensorLeft X ⋙ F :=
  natIsoOfPreservesFilteredColimits P hP hgen _ _ (tensorExtensionAux' P hP hgen F e hF' X)

/-- The tensor isomorphism `F X ⊗ F Y ≅ F (X ⊗ Y)` of the extension. -/
noncomputable def tensorExtensionμIso (X Y : C) : F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y) :=
  (tensorExtensionRight P hP hgen F e hF' X).app Y

/-- When `Y` is a `P`-object, the tensor isomorphism `tensorExtensionμIso` of the extension is
`tensorExtensionLeft` evaluated at `X`. -/
theorem tensorExtensionμIso_hom_of_right (X : C) (Y : P.FullSubcategory) :
    (tensorExtensionμIso P hP hgen F e hF' X Y.obj).hom =
      (tensorExtensionLeft P hP hgen F e hF' Y).hom.app X := by
  simp [tensorExtensionμIso, tensorExtensionRight, tensorExtensionAux']

/-- On two `P`-objects the tensor isomorphism of the extension is the one of `F'`, transported
along `e`. -/
theorem tensorExtensionμIso_hom (X Y : P.FullSubcategory) :
    (tensorExtensionμIso P hP hgen F e hF' X.obj Y.obj).hom =
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫ (hF'.μIso X Y).hom ≫ e.inv.app (X ⊗ Y) := by
  rw [tensorExtensionμIso_hom_of_right, tensorExtensionLeft_hom_app]

/-- The tensor isomorphism `tensorExtensionμIso` of the extension is natural in the second
variable. -/
@[reassoc]
theorem tensorExtensionμIso_natural_right (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    F.obj X ◁ F.map g ≫ (tensorExtensionμIso P hP hgen F e hF' X Y').hom =
      (tensorExtensionμIso P hP hgen F e hF' X Y).hom ≫ F.map (X ◁ g) :=
  (tensorExtensionRight P hP hgen F e hF' X).hom.naturality g

/-- The tensor isomorphism `tensorExtensionμIso` of the extension is natural in the first
variable. -/
@[reassoc]
theorem tensorExtensionμIso_natural_left {X X' : C} (f : X ⟶ X') (Y : C) :
    F.map f ▷ F.obj Y ≫ (tensorExtensionμIso P hP hgen F e hF' X' Y).hom =
      (tensorExtensionμIso P hP hgen F e hF' X Y).hom ≫ F.map (f ▷ Y) := by
  refine app_eq_of_preservesFilteredColimits P hP hgen (F ⋙ tensorLeft (F.obj X))
    (tensorLeft X' ⋙ F) (fun Y ↦ F.map f ▷ F.obj Y ≫
      (tensorExtensionμIso P hP hgen F e hF' X' Y).hom)
    (fun Y ↦ (tensorExtensionμIso P hP hgen F e hF' X Y).hom ≫ F.map (f ▷ Y))
    (fun {Y₁ Y₂} g ↦ ?_) (fun {Y₁ Y₂} g ↦ ?_) (fun Y ↦ ?_) Y
  · change _ ◁ F.map g ≫ F.map f ▷ _ ≫ _ = (F.map f ▷ _ ≫ _) ≫ F.map (X' ◁ g)
    rw [whisker_exchange_assoc, tensorExtensionμIso_natural_right, assoc]
  · change _ ◁ F.map g ≫ _ ≫ F.map (f ▷ Y₂) = (_ ≫ F.map (f ▷ Y₁)) ≫ F.map (X' ◁ g)
    rw [tensorExtensionμIso_natural_right_assoc, assoc, ← F.map_comp, ← F.map_comp,
      whisker_exchange]
  · change F.map f ▷ _ ≫ (tensorExtensionμIso P hP hgen F e hF' X' Y.obj).hom =
      (tensorExtensionμIso P hP hgen F e hF' X Y.obj).hom ≫ F.map (f ▷ Y.obj)
    simp only [tensorExtensionμIso_hom_of_right]
    exact (tensorExtensionLeft P hP hgen F e hF' Y).hom.naturality f

/-- The associativity diagram for `tensorExtensionμIso` commutes when `X`, `Y` and `Z` are all
`P`-objects. -/
theorem tensorExtension_associativity_mem (X Y Z : P.FullSubcategory) :
    F.obj X.obj ◁ (tensorExtensionμIso P hP hgen F e hF' Y.obj Z.obj).hom ≫
        (tensorExtensionμIso P hP hgen F e hF' X.obj (Y.obj ⊗ Z.obj)).hom ≫
          F.map (α_ X.obj Y.obj Z.obj).inv =
      (α_ (F.obj X.obj) (F.obj Y.obj) (F.obj Z.obj)).inv ≫
        (tensorExtensionμIso P hP hgen F e hF' X.obj Y.obj).hom ▷ F.obj Z.obj ≫
          (tensorExtensionμIso P hP hgen F e hF' (X.obj ⊗ Y.obj) Z.obj).hom := by
  have key := tensorExtensionμIso_hom P hP hgen F e hF'
  erw [key X (Y ⊗ Z), key (X ⊗ Y) Z, key Y Z, key X Y]
  exact (hF'.ofIso e).associativity X Y Z

/-- The associativity diagram for `tensorExtensionμIso` commutes when `Y` and `Z` are
`P`-objects and `X` is arbitrary. -/
theorem tensorExtension_associativity_mem₂ (X : C) (Y Z : P.FullSubcategory) :
    F.obj X ◁ (tensorExtensionμIso P hP hgen F e hF' Y.obj Z.obj).hom ≫
        (tensorExtensionμIso P hP hgen F e hF' X (Y.obj ⊗ Z.obj)).hom ≫
          F.map (α_ X Y.obj Z.obj).inv =
      (α_ (F.obj X) (F.obj Y.obj) (F.obj Z.obj)).inv ≫
        (tensorExtensionμIso P hP hgen F e hF' X Y.obj).hom ▷ F.obj Z.obj ≫
          (tensorExtensionμIso P hP hgen F e hF' (X ⊗ Y.obj) Z.obj).hom := by
  refine app_eq_of_preservesFilteredColimits P hP hgen
    (F ⋙ tensorRight (F.obj Y.obj ⊗ F.obj Z.obj)) (tensorRight Y.obj ⋙ tensorRight Z.obj ⋙ F)
    (fun X ↦ F.obj X ◁ (tensorExtensionμIso P hP hgen F e hF' Y.obj Z.obj).hom ≫
        (tensorExtensionμIso P hP hgen F e hF' X (Y.obj ⊗ Z.obj)).hom ≫
          F.map (α_ X Y.obj Z.obj).inv)
    (fun X ↦ (α_ (F.obj X) (F.obj Y.obj) (F.obj Z.obj)).inv ≫
        (tensorExtensionμIso P hP hgen F e hF' X Y.obj).hom ▷ F.obj Z.obj ≫
          (tensorExtensionμIso P hP hgen F e hF' (X ⊗ Y.obj) Z.obj).hom)
    (fun {X₁ X₂} f ↦ ?_) (fun {X₁ X₂} f ↦ ?_)
    (fun X ↦ tensorExtension_associativity_mem P hP hgen F e hF' X Y Z) X
  · change F.map f ▷ _ ≫ F.obj X₂ ◁ _ ≫ _ ≫ F.map (α_ X₂ Y.obj Z.obj).inv =
      (F.obj X₁ ◁ _ ≫ _ ≫ F.map (α_ X₁ Y.obj Z.obj).inv) ≫ F.map ((f ▷ Y.obj) ▷ Z.obj)
    rw [← whisker_exchange_assoc, tensorExtensionμIso_natural_left_assoc, assoc, assoc,
      ← F.map_comp, ← F.map_comp, associator_inv_naturality_left]
  · change F.map f ▷ _ ≫ (α_ _ _ _).inv ≫
        (tensorExtensionμIso P hP hgen F e hF' X₂ Y.obj).hom ▷ _ ≫ _ =
      ((α_ _ _ _).inv ≫ (tensorExtensionμIso P hP hgen F e hF' X₁ Y.obj).hom ▷ _ ≫ _) ≫
        F.map ((f ▷ Y.obj) ▷ Z.obj)
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc,
      tensorExtensionμIso_natural_left, comp_whiskerRight_assoc,
      tensorExtensionμIso_natural_left, assoc, assoc]

/-- The associativity diagram for `tensorExtensionμIso` commutes when `Z` is a `P`-object and
`X` and `Y` are arbitrary. -/
theorem tensorExtension_associativity_mem₁ (X Y : C) (Z : P.FullSubcategory) :
    F.obj X ◁ (tensorExtensionμIso P hP hgen F e hF' Y Z.obj).hom ≫
        (tensorExtensionμIso P hP hgen F e hF' X (Y ⊗ Z.obj)).hom ≫ F.map (α_ X Y Z.obj).inv =
      (α_ (F.obj X) (F.obj Y) (F.obj Z.obj)).inv ≫
        (tensorExtensionμIso P hP hgen F e hF' X Y).hom ▷ F.obj Z.obj ≫
          (tensorExtensionμIso P hP hgen F e hF' (X ⊗ Y) Z.obj).hom := by
  refine app_eq_of_preservesFilteredColimits P hP hgen
    (F ⋙ tensorRight (F.obj Z.obj) ⋙ tensorLeft (F.obj X))
    (tensorLeft X ⋙ tensorRight Z.obj ⋙ F)
    (fun Y ↦ F.obj X ◁ (tensorExtensionμIso P hP hgen F e hF' Y Z.obj).hom ≫
      (tensorExtensionμIso P hP hgen F e hF' X (Y ⊗ Z.obj)).hom ≫ F.map (α_ X Y Z.obj).inv)
    (fun Y ↦ (α_ (F.obj X) (F.obj Y) (F.obj Z.obj)).inv ≫
        (tensorExtensionμIso P hP hgen F e hF' X Y).hom ▷ F.obj Z.obj ≫
          (tensorExtensionμIso P hP hgen F e hF' (X ⊗ Y) Z.obj).hom)
    (fun {Y₁ Y₂} g ↦ ?_) (fun {Y₁ Y₂} g ↦ ?_)
    (fun Y ↦ tensorExtension_associativity_mem₂ P hP hgen F e hF' X Y Z) Y
  · change F.obj X ◁ (F.map g ▷ _) ≫ F.obj X ◁ _ ≫ _ ≫ F.map (α_ X Y₂ Z.obj).inv =
      (F.obj X ◁ _ ≫ _ ≫ F.map (α_ X Y₁ Z.obj).inv) ≫ F.map ((X ◁ g) ▷ Z.obj)
    rw [← whiskerLeft_comp_assoc, tensorExtensionμIso_natural_left, whiskerLeft_comp_assoc,
      tensorExtensionμIso_natural_right_assoc, assoc, assoc, ← F.map_comp, ← F.map_comp,
      associator_inv_naturality_middle]
  · change F.obj X ◁ (F.map g ▷ _) ≫ (α_ _ _ _).inv ≫
        (tensorExtensionμIso P hP hgen F e hF' X Y₂).hom ▷ _ ≫ _ =
      ((α_ _ _ _).inv ≫ (tensorExtensionμIso P hP hgen F e hF' X Y₁).hom ▷ _ ≫ _) ≫
        F.map ((X ◁ g) ▷ Z.obj)
    rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
      tensorExtensionμIso_natural_right, comp_whiskerRight_assoc,
      tensorExtensionμIso_natural_left, assoc, assoc]

/-- The associativity diagram for the tensor isomorphism `tensorExtensionμIso` of the extension
commutes for all `X`, `Y` and `Z`. -/
theorem tensorExtension_associativity (X Y Z : C) :
    F.obj X ◁ (tensorExtensionμIso P hP hgen F e hF' Y Z).hom ≫
        (tensorExtensionμIso P hP hgen F e hF' X (Y ⊗ Z)).hom ≫ F.map (α_ X Y Z).inv =
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫
        (tensorExtensionμIso P hP hgen F e hF' X Y).hom ▷ F.obj Z ≫
          (tensorExtensionμIso P hP hgen F e hF' (X ⊗ Y) Z).hom := by
  refine app_eq_of_preservesFilteredColimits P hP hgen
    (F ⋙ tensorLeft (F.obj Y) ⋙ tensorLeft (F.obj X)) (tensorLeft (X ⊗ Y) ⋙ F)
    (fun Z ↦ F.obj X ◁ (tensorExtensionμIso P hP hgen F e hF' Y Z).hom ≫
      (tensorExtensionμIso P hP hgen F e hF' X (Y ⊗ Z)).hom ≫ F.map (α_ X Y Z).inv)
    (fun Z ↦ (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫
        (tensorExtensionμIso P hP hgen F e hF' X Y).hom ▷ F.obj Z ≫
          (tensorExtensionμIso P hP hgen F e hF' (X ⊗ Y) Z).hom)
    (fun {Z₁ Z₂} h ↦ ?_) (fun {Z₁ Z₂} h ↦ ?_)
    (fun Z ↦ tensorExtension_associativity_mem₁ P hP hgen F e hF' X Y Z) Z
  · change F.obj X ◁ (F.obj Y ◁ F.map h) ≫ F.obj X ◁ _ ≫ _ ≫ F.map (α_ X Y Z₂).inv =
      (F.obj X ◁ _ ≫ _ ≫ F.map (α_ X Y Z₁).inv) ≫ F.map ((X ⊗ Y) ◁ h)
    rw [← whiskerLeft_comp_assoc, tensorExtensionμIso_natural_right, whiskerLeft_comp_assoc,
      tensorExtensionμIso_natural_right_assoc, assoc, assoc, ← F.map_comp, ← F.map_comp,
      associator_inv_naturality_right]
  · change F.obj X ◁ (F.obj Y ◁ F.map h) ≫ (α_ _ _ _).inv ≫
        (tensorExtensionμIso P hP hgen F e hF' X Y).hom ▷ _ ≫ _ =
      ((α_ _ _ _).inv ≫ (tensorExtensionμIso P hP hgen F e hF' X Y).hom ▷ _ ≫ _) ≫
        F.map ((X ⊗ Y) ◁ h)
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
      tensorExtensionμIso_natural_right, assoc, assoc]

/-- **The extension of a tensor functor is a tensor functor.** If `F : C ⥤ D` commutes with
filtered colimits and its restriction to the `P`-objects is identified by `e` with a functor of
monoidal categories `F'` (Stacks 0FFL), then `F` is a functor of monoidal categories. -/
noncomputable def tensorStructureExtension : F.TensorStructure where
  μIso := tensorExtensionμIso P hP hgen F e hF'
  μIso_natural_left := tensorExtensionμIso_natural_left P hP hgen F e hF'
  μIso_natural_right := tensorExtensionμIso_natural_right P hP hgen F e hF'
  associativity := tensorExtension_associativity P hP hgen F e hF'
  isUnitObject_obj_tensorUnit := hF'.isUnitObject_obj_tensorUnit.of_iso (e.app (𝟙_ _)).symm

/-- The identification `e` of the restriction of the extension with `F'` is compatible with the
tensor structures. -/
theorem isCompatible_tensorStructureExtension :
    ((tensorStructureExtension P hP hgen F e hF').restrict P).IsCompatible hF' e := by
  intro X Y
  change (tensorExtensionμIso P hP hgen F e hF' X.obj Y.obj).hom ≫ _ = _
  rw [tensorExtensionμIso_hom]
  simp

end TensorExtension

section TensorUniqueness

variable [MonoidalCategory C] [MonoidalCategory D]
  [LocallySmall.{w} P.FullSubcategory]
  (hP : P ≤ isFinitelyPresentable.{w} C) (hgen : ∀ X : C, P.ind.{w} X)
  [∀ X : C, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ X : C, PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]
  [∀ X : D, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ X : D, PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]

omit [∀ X : C, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ X : C, PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)] in
include hP hgen in
/-- An isomorphism between two functors of monoidal categories commuting with filtered colimits
is compatible with their tensor structures as soon as it is so on pairs of `P`-objects. -/
theorem isCompatible_of_preservesFilteredColimits {F G : C ⥤ D}
    [PreservesFilteredColimitsOfSize.{w, w} F] [PreservesFilteredColimitsOfSize.{w, w} G]
    (hF : F.TensorStructure) (hG : G.TensorStructure) (φ : F ≅ G)
    (h : ∀ X Y : P.FullSubcategory, (hF.μIso X.obj Y.obj).hom ≫ φ.hom.app (X.obj ⊗ Y.obj) =
      (φ.hom.app X.obj ⊗ₘ φ.hom.app Y.obj) ≫ (hG.μIso X.obj Y.obj).hom) :
    hF.IsCompatible hG φ := by
  have hb : ∀ {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C), F.map f ▷ F.obj Y ≫
      (φ.hom.app X₂ ⊗ₘ φ.hom.app Y) = (φ.hom.app X₁ ⊗ₘ φ.hom.app Y) ≫ G.map f ▷ G.obj Y := by
    intro X₁ X₂ f Y
    rw [← tensorHom_id, tensorHom_comp_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom,
      φ.hom.naturality]
    simp
  have hb' : ∀ (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂), F.obj X ◁ F.map g ≫
      (φ.hom.app X ⊗ₘ φ.hom.app Y₂) = (φ.hom.app X ⊗ₘ φ.hom.app Y₁) ≫ G.obj X ◁ G.map g := by
    intro X Y₁ Y₂ g
    rw [← id_tensorHom, tensorHom_comp_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom,
      φ.hom.naturality]
    simp
  have step₁ : ∀ (X : C) (Y : P.FullSubcategory), (hF.μIso X Y.obj).hom ≫
      φ.hom.app (X ⊗ Y.obj) = (φ.hom.app X ⊗ₘ φ.hom.app Y.obj) ≫ (hG.μIso X Y.obj).hom := by
    intro X Y
    refine app_eq_of_preservesFilteredColimits P hP hgen (F ⋙ tensorRight (F.obj Y.obj))
      (tensorRight Y.obj ⋙ G)
      (fun X ↦ (hF.μIso X Y.obj).hom ≫ φ.hom.app (X ⊗ Y.obj))
      (fun X ↦ (φ.hom.app X ⊗ₘ φ.hom.app Y.obj) ≫ (hG.μIso X Y.obj).hom)
      (fun {X₁ X₂} f ↦ ?_) (fun {X₁ X₂} f ↦ ?_) (fun X ↦ h X Y) X
    · change F.map f ▷ _ ≫ _ ≫ _ = (_ ≫ _) ≫ G.map (f ▷ Y.obj)
      rw [hF.μIso_natural_left_assoc, assoc]
      exact congr_arg _ (φ.hom.naturality (f ▷ Y.obj))
    · change F.map f ▷ _ ≫ _ ≫ _ = (_ ≫ _) ≫ G.map (f ▷ Y.obj)
      rw [reassoc_of% (hb f Y.obj), hG.μIso_natural_left, assoc]
  intro X Y
  refine app_eq_of_preservesFilteredColimits P hP hgen (F ⋙ tensorLeft (F.obj X))
    (tensorLeft X ⋙ G)
    (fun Y ↦ (hF.μIso X Y).hom ≫ φ.hom.app (X ⊗ Y))
    (fun Y ↦ (φ.hom.app X ⊗ₘ φ.hom.app Y) ≫ (hG.μIso X Y).hom)
    (fun {Y₁ Y₂} g ↦ ?_) (fun {Y₁ Y₂} g ↦ ?_) (fun Y ↦ step₁ X Y) Y
  · change _ ◁ F.map g ≫ _ ≫ _ = (_ ≫ _) ≫ G.map (X ◁ g)
    rw [hF.μIso_natural_right_assoc, assoc]
    exact congr_arg _ (φ.hom.naturality (X ◁ g))
  · change _ ◁ F.map g ≫ _ ≫ _ = (_ ≫ _) ≫ G.map (X ◁ g)
    rw [reassoc_of% (hb' X g), hG.μIso_natural_right, assoc]

end TensorUniqueness

end ObjectProperty

end CategoryTheory
