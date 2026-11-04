module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion

/-!
# Equivalences of categories over a base form a groupoid

`StacksRepresentableCFG.EquivalenceOver p q` is an equivalence in the 2-category of
categories over a fixed base `C`: 1-morphisms over `C` in both directions together with
unit and counit 2-isomorphisms whose components are vertical. This file records that these
equivalences are reflexive, symmetric and transitive, and that an equivalence over `C` is
an equivalence over `C'` after composing the structure functors with a functor `C ⥤ C'`.

`EquivalenceOver` is *data*, not a proposition, so these three are definitions and the
groupoid laws hold only up to isomorphism of the data; `EquivalenceOver.symm_symm` is the
one of them that is an equality on the nose.

## Main definitions

* `StacksRepresentableCFG.EquivalenceOver.refl`: the identity equivalence over `C`.
* `StacksRepresentableCFG.EquivalenceOver.symm`: an equivalence over `C` read backwards.
* `StacksRepresentableCFG.EquivalenceOver.trans`: composition of equivalences over `C`.
* `StacksRepresentableCFG.EquivalenceOver.compRight`: an equivalence over `C` read over `C'`,
  along a functor `C ⥤ C'`.

## Main results

* `StacksRepresentableCFG.whiskerRight_eq_eqToHom`: whiskering a natural transformation with
  vertical components into the structure functor gives the canonical `eqToHom`.
* `StacksRepresentableCFG.isHomLift_comp_of_isHomLift_id`: a morphism lying over an identity
  still lies over an identity after the structure functor is composed with a functor on the
  base.
* `StacksRepresentableCFG.EquivalenceOver.isHomLift_counitIso_inv_app`: the inverse counit of
  an equivalence over `C` is again vertical.
* `StacksRepresentableCFG.EquivalenceOver.isEquivalence_hom_functor`: the forward
  1-morphism of an equivalence over `C` is an equivalence of the underlying categories.
-/

@[expose] public section

open CategoryTheory

namespace StacksRepresentableCFG

universe v u v₁ u₁ v₂ u₂ v₃ u₃

variable {C : Type u} [Category.{v} C]

/-- Whiskering a natural transformation with vertical components into the structure functor
gives the canonical `eqToHom`. -/
theorem whiskerRight_eq_eqToHom {D₁ : Type u₁} [Category.{v₁} D₁] {D₂ : Type u₂}
    [Category.{v₂} D₂] (p : D₁ ⥤ C) {F G : D₂ ⥤ D₁} (h : F ⋙ p = G ⋙ p) (α : F ⟶ G)
    (hα : ∀ x, p.IsHomLift (𝟙 (p.obj (F.obj x))) (α.app x)) :
    Functor.whiskerRight α p = eqToHom h := by
  ext x
  have := hα x
  simpa using IsHomLift.fac' p (𝟙 (p.obj (F.obj x))) (α.app x)

/-- The inverse of the counit of an equivalence over `C` is again vertical. -/
lemma EquivalenceOver.isHomLift_counitIso_inv_app {D₁ : Type u₁} [Category.{v₁} D₁]
    {D₂ : Type u₂} [Category.{v₂} D₂] {p : D₁ ⥤ C} {q : D₂ ⥤ C}
    (e : EquivalenceOver p q) (t : D₂) :
    q.IsHomLift (𝟙 (q.obj t)) (e.counitIso.inv.app t) := by
  have := e.isHomLift_counitIso_hom_app t
  rw [show e.counitIso.inv.app t = CategoryTheory.inv (e.counitIso.hom.app t) by simp]
  exact IsHomLift.lift_id_inv_isIso q (q.obj t) (e.counitIso.hom.app t)

/-- The identity equivalence over `C`: a category over `C` is equivalent over `C` to itself,
with both 1-morphisms the identity functor and both 2-cells the identity. -/
def EquivalenceOver.refl {D₁ : Type u₁} [Category.{v₁} D₁] (p : D₁ ⥤ C) :
    EquivalenceOver p p where
  hom := ⟨𝟭 D₁, Functor.id_comp p⟩
  inv := ⟨𝟭 D₁, Functor.id_comp p⟩
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  unit_over := whiskerRight_eq_eqToHom _ _ _ fun _ => IsHomLift.id rfl
  counit_over := whiskerRight_eq_eqToHom _ _ _ fun _ => IsHomLift.id rfl

/-- An equivalence over `C` read backwards: the two 1-morphisms are exchanged, and the unit
of the new equivalence is the inverse of the old counit (and conversely). -/
def EquivalenceOver.symm {D₁ : Type u₁} [Category.{v₁} D₁] {D₂ : Type u₂} [Category.{v₂} D₂]
    {p : D₁ ⥤ C} {q : D₂ ⥤ C} (e : EquivalenceOver p q) : EquivalenceOver q p where
  hom := e.inv
  inv := e.hom
  unitIso := e.counitIso.symm
  counitIso := e.unitIso.symm
  unit_over := whiskerRight_eq_eqToHom _ _ _ e.isHomLift_counitIso_inv_app
  counit_over := by
    apply whiskerRight_eq_eqToHom
    intro x
    have hx : p.obj ((e.hom.functor ⋙ e.inv.functor).obj x) = p.obj x :=
      Functor.congr_obj (show (e.hom.functor ⋙ e.inv.functor) ⋙ p = p by
        rw [Functor.assoc, e.inv.w, e.hom.w]) x
    exact (congrArg (fun U => p.IsHomLift (𝟙 U) (e.unitIso.inv.app x)) hx).mpr
      (e.isHomLift_unitIso_inv_app x)

/-- The forward functor of the identity equivalence over `C` is the identity functor. -/
@[simp] lemma EquivalenceOver.refl_hom {D₁ : Type u₁} [Category.{v₁} D₁] (p : D₁ ⥤ C) :
    (EquivalenceOver.refl p).hom.functor = 𝟭 D₁ := rfl

/-- The backward functor of the identity equivalence over `C` is the identity functor. -/
@[simp] lemma EquivalenceOver.refl_inv {D₁ : Type u₁} [Category.{v₁} D₁] (p : D₁ ⥤ C) :
    (EquivalenceOver.refl p).inv.functor = 𝟭 D₁ := rfl

/-- The forward 1-morphism of the reversed equivalence is the backward 1-morphism of `e`. -/
@[simp] lemma EquivalenceOver.symm_hom {D₁ : Type u₁} [Category.{v₁} D₁] {D₂ : Type u₂}
    [Category.{v₂} D₂] {p : D₁ ⥤ C} {q : D₂ ⥤ C} (e : EquivalenceOver p q) :
    e.symm.hom = e.inv := rfl

/-- The backward 1-morphism of the reversed equivalence is the forward 1-morphism of `e`. -/
@[simp] lemma EquivalenceOver.symm_inv {D₁ : Type u₁} [Category.{v₁} D₁] {D₂ : Type u₂}
    [Category.{v₂} D₂] {p : D₁ ⥤ C} {q : D₂ ⥤ C} (e : EquivalenceOver p q) :
    e.symm.inv = e.hom := rfl

/-- Reversing an equivalence over `C` twice gives back the original equivalence. -/
@[simp] lemma EquivalenceOver.symm_symm {D₁ : Type u₁} [Category.{v₁} D₁] {D₂ : Type u₂}
    [Category.{v₂} D₂] {p : D₁ ⥤ C} {q : D₂ ⥤ C} (e : EquivalenceOver p q) :
    e.symm.symm = e := rfl

/-- The forward 1-morphism of an equivalence over `C` is an equivalence of the underlying
categories. -/
lemma EquivalenceOver.isEquivalence_hom_functor {D₁ : Type u₁} [Category.{v₁} D₁]
    {D₂ : Type u₂} [Category.{v₂} D₂] {p : D₁ ⥤ C} {q : D₂ ⥤ C} (e : EquivalenceOver p q) :
    e.hom.functor.IsEquivalence :=
  e.toEquivalence.isEquivalence_functor

/-- The backward 1-morphism of an equivalence over `C` is an equivalence of the underlying
categories. -/
lemma EquivalenceOver.isEquivalence_inv_functor {D₁ : Type u₁} [Category.{v₁} D₁]
    {D₂ : Type u₂} [Category.{v₂} D₂] {p : D₁ ⥤ C} {q : D₂ ⥤ C} (e : EquivalenceOver p q) :
    e.inv.functor.IsEquivalence :=
  e.symm.toEquivalence.isEquivalence_functor

/-- Composition of equivalences over `C`. -/
def EquivalenceOver.trans {D₁ : Type u₁} [Category.{v₁} D₁] {D₂ : Type u₂} [Category.{v₂} D₂]
    {D₃ : Type u₃} [Category.{v₃} D₃] {p₁ : D₁ ⥤ C} {p₂ : D₂ ⥤ C} {p₃ : D₃ ⥤ C}
    (e : EquivalenceOver p₁ p₂) (f : EquivalenceOver p₂ p₃) : EquivalenceOver p₁ p₃ where
  hom := ⟨e.hom.functor ⋙ f.hom.functor, by rw [Functor.assoc, f.hom.w, e.hom.w]⟩
  inv := ⟨f.inv.functor ⋙ e.inv.functor, by rw [Functor.assoc, e.inv.w, f.inv.w]⟩
  unitIso := e.unitIso ≪≫ Functor.isoWhiskerLeft e.hom.functor
    (Functor.isoWhiskerRight f.unitIso e.inv.functor)
  counitIso := Functor.isoWhiskerLeft f.inv.functor
    (Functor.isoWhiskerRight e.counitIso f.hom.functor) ≪≫ f.counitIso
  unit_over := by
    apply whiskerRight_eq_eqToHom
    intro x
    have he := e.isHomLift_unitIso_hom_app x
    have hf := f.isHomLift_unitIso_hom_app (e.hom.functor.obj x)
    have hf' := Functor.isHomLift_map_of_comp_eq e.inv.w
      (𝟙 (p₂.obj (e.hom.functor.obj x))) (f.unitIso.hom.app (e.hom.functor.obj x))
    have hh : p₁.IsHomLift (𝟙 (p₁.obj x))
        (e.inv.functor.map (f.unitIso.hom.app (e.hom.functor.obj x))) :=
      (congrArg (fun U => p₁.IsHomLift (𝟙 U)
        (e.inv.functor.map (f.unitIso.hom.app (e.hom.functor.obj x))))
        (Functor.congr_obj e.hom.w x)).mp hf'
    exact @IsHomLift.comp_of_lift_id _ _ _ _ p₁ (p₁.obj x) _ _ _ _ _ he hh
  counit_over := by
    apply whiskerRight_eq_eqToHom
    intro x
    have he := e.isHomLift_counitIso_hom_app (f.inv.functor.obj x)
    have hf := f.isHomLift_counitIso_hom_app x
    have he' := Functor.isHomLift_map_of_comp_eq f.hom.w
      (𝟙 (p₂.obj (f.inv.functor.obj x))) (e.counitIso.hom.app (f.inv.functor.obj x))
    have hh : p₃.IsHomLift (𝟙 (p₃.obj x))
        (f.hom.functor.map (e.counitIso.hom.app (f.inv.functor.obj x))) :=
      (congrArg (fun U => p₃.IsHomLift (𝟙 U)
        (f.hom.functor.map (e.counitIso.hom.app (f.inv.functor.obj x))))
        (Functor.congr_obj f.inv.w x)).mp he'
    have hx : p₃.obj ((f.inv.functor ⋙ e.inv.functor ⋙
        (e.hom.functor ⋙ f.hom.functor)).obj x) = p₃.obj x := by
      change ((f.inv.functor ⋙ e.inv.functor ⋙ e.hom.functor ⋙ f.hom.functor) ⋙ p₃).obj x = _
      simp only [Functor.assoc, f.hom.w, e.hom.w, e.inv.w, f.inv.w]
    exact (congrArg (fun U => p₃.IsHomLift (𝟙 U) _) hx).mpr <|
      @IsHomLift.comp_of_lift_id _ _ _ _ p₃ (p₃.obj x) _ _ _ _ _ hh hf

/-- The forward functor of a composite equivalence over `C` is the composite of the forward
functors. -/
@[simp] lemma EquivalenceOver.trans_hom {D₁ : Type u₁} [Category.{v₁} D₁] {D₂ : Type u₂}
    [Category.{v₂} D₂] {D₃ : Type u₃} [Category.{v₃} D₃] {p₁ : D₁ ⥤ C} {p₂ : D₂ ⥤ C}
    {p₃ : D₃ ⥤ C} (e : EquivalenceOver p₁ p₂) (f : EquivalenceOver p₂ p₃) :
    (e.trans f).hom.functor = e.hom.functor ⋙ f.hom.functor := rfl

/-- The backward functor of a composite equivalence over `C` is the composite, in the reverse
order, of the backward functors. -/
@[simp] lemma EquivalenceOver.trans_inv {D₁ : Type u₁} [Category.{v₁} D₁] {D₂ : Type u₂}
    [Category.{v₂} D₂] {D₃ : Type u₃} [Category.{v₃} D₃] {p₁ : D₁ ⥤ C} {p₂ : D₂ ⥤ C}
    {p₃ : D₃ ⥤ C} (e : EquivalenceOver p₁ p₂) (f : EquivalenceOver p₂ p₃) :
    (e.trans f).inv.functor = f.inv.functor ⋙ e.inv.functor := rfl

section CompRight

universe v' u'

variable {C' : Type u'} [Category.{v'} C']

/-- A morphism lying over an identity of `C` lies over an identity of `C'` after the structure
functor is composed with `T : C ⥤ C'`. -/
lemma isHomLift_comp_of_isHomLift_id {D₁ : Type u₁} [Category.{v₁} D₁] (p : D₁ ⥤ C)
    (T : C ⥤ C') {x y : D₁} (φ : x ⟶ y) {U : C} (h : p.IsHomLift (𝟙 U) φ) :
    (p ⋙ T).IsHomLift (𝟙 (T.obj U)) φ := by
  refine IsHomLift.of_fac' (p ⋙ T) (𝟙 (T.obj U)) φ
    (congrArg T.obj (IsHomLift.domain_eq p (𝟙 U) φ))
    (congrArg T.obj (IsHomLift.codomain_eq p (𝟙 U) φ)) ?_
  rw [Functor.comp_map, IsHomLift.fac' p (𝟙 U) φ]
  simp [eqToHom_map]

/-- An equivalence in the 2-category of categories over `C` is one in the 2-category of
categories over `C'`, for any functor `T : C ⥤ C'`, with the same 1-morphisms and 2-cells. -/
def EquivalenceOver.compRight {D₁ : Type u₁} [Category.{v₁} D₁] {D₂ : Type u₂}
    [Category.{v₂} D₂] {p : D₁ ⥤ C} {q : D₂ ⥤ C} (e : EquivalenceOver p q) (T : C ⥤ C') :
    EquivalenceOver (p ⋙ T) (q ⋙ T) where
  hom := ⟨e.hom.functor, by rw [← Functor.assoc, e.hom.w]⟩
  inv := ⟨e.inv.functor, by rw [← Functor.assoc, e.inv.w]⟩
  unitIso := e.unitIso
  counitIso := e.counitIso
  unit_over := whiskerRight_eq_eqToHom _ _ _ fun x =>
    isHomLift_comp_of_isHomLift_id p T _ (e.isHomLift_unitIso_hom_app x)
  counit_over := by
    apply whiskerRight_eq_eqToHom
    intro x
    have hq : (e.inv.functor ⋙ e.hom.functor) ⋙ q = q := by
      rw [Functor.assoc, e.hom.w, e.inv.w]
    have hx : (q ⋙ T).obj ((e.inv.functor ⋙ e.hom.functor).obj x) = (q ⋙ T).obj x :=
      congrArg T.obj (Functor.congr_obj hq x)
    exact (congrArg (fun V => (q ⋙ T).IsHomLift (𝟙 V) (e.counitIso.hom.app x)) hx).mpr <|
      isHomLift_comp_of_isHomLift_id q T _ (e.isHomLift_counitIso_hom_app x)

/-- The forward functor of `e.compRight T` is the forward functor of `e`. -/
@[simp] lemma EquivalenceOver.compRight_hom {D₁ : Type u₁} [Category.{v₁} D₁] {D₂ : Type u₂}
    [Category.{v₂} D₂] {p : D₁ ⥤ C} {q : D₂ ⥤ C} (e : EquivalenceOver p q) (T : C ⥤ C') :
    (e.compRight T).hom.functor = e.hom.functor := rfl

/-- The backward functor of `e.compRight T` is the backward functor of `e`. -/
@[simp] lemma EquivalenceOver.compRight_inv {D₁ : Type u₁} [Category.{v₁} D₁] {D₂ : Type u₂}
    [Category.{v₂} D₂] {p : D₁ ⥤ C} {q : D₂ ⥤ C} (e : EquivalenceOver p q) (T : C ⥤ C') :
    (e.compRight T).inv.functor = e.inv.functor := rfl

end CompRight

end StacksRepresentableCFG

end
