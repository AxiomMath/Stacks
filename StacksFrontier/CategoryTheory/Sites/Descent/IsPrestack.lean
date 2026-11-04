module

public import Mathlib.CategoryTheory.Sites.Descent.IsPrestack

/-! # Fully faithful 1-morphisms of stacks

A 1-morphism of stacks is fully faithful exactly when it induces isomorphisms on the sheaves of
morphisms. This file states that for the split presentation of a stack over a site: the underlying
data of a stack is a functor `Cᵒᵖ ⥤ Cat`, and its sheaves of morphisms and the identification of
their sections with hom-sets in the fibres are carried as data.

That presentation is provisional. At this Mathlib pin the faithful notions are
`CategoryTheory.Pseudofunctor.IsStack` (which carries tag 026F) for a stack,
`CategoryTheory.Pseudofunctor.sheafHom` for the sheaf of morphisms, and
`CategoryTheory.Pseudofunctor.CoGrothendieck.map` for the functor on total categories along which
full faithfulness of a 1-morphism is measured. `CategoryTheory.Functor.toPseudofunctor'` sends the
split data used here to a pseudofunctor.

## Main results

* `CategoryTheory.Stack.Hom.isFullyFaithful_iff_morSheafIso`.
-/

@[expose] public section

namespace CategoryTheory

open Opposite

universe v u

variable {C : Type u} [Category.{v} C]

/-- The underlying data of a stack in the split presentation: a functor `Cᵒᵖ ⥤ Cat`, equivalently a
split category fibred in categories over `C`. -/
abbrev PrestackData (C : Type u) [Category.{v} C] : Type _ := Cᵒᵖ ⥤ Cat.{v, v}

namespace PrestackData

variable (S : PrestackData C)

/-- Pullback along `f : V ⟶ U`, as a functor between the fibres. -/
abbrev pb {V U : C} (f : V ⟶ U) : (S.obj (op U)).α ⥤ (S.obj (op V)).α := (S.map f.op).toFunctor

/-- Pullback is strictly functorial on objects: `(h ≫ g)^* x = h^* (g^* x)`. -/
lemma pb_factor {V W U : C} (g : W ⟶ U) (h : V ⟶ W) (x : (S.obj (op U)).α) :
    (S.pb (h ≫ g)).obj x = (S.pb h).obj ((S.pb g).obj x) := by
  unfold PrestackData.pb
  conv_lhs => rw [op_comp, S.map_comp]
  rfl

/-- Pullback along the identity is the identity on objects. -/
lemma pb_id_obj (U : C) (x : (S.obj (op U)).α) : (S.pb (𝟙 U)).obj x = x := by
  unfold PrestackData.pb
  rw [op_id, S.map_id]
  rfl

/-- A 1-morphism of the underlying data commutes with pullback on objects. -/
lemma nat_obj {S S' : PrestackData C} (η : S ⟶ S') {V U : C} (f : V ⟶ U) (x : (S.obj (op U)).α) :
    (S'.pb f).obj ((η.app (op U)).toFunctor.obj x) =
      (η.app (op V)).toFunctor.obj ((S.pb f).obj x) := by
  unfold PrestackData.pb
  rw [← Functor.comp_obj, ← Cat.Hom.comp_toFunctor, ← η.naturality f.op]
  rfl

end PrestackData

/-- A stack over the site `(C, J)` in the split presentation: prestack data together with, for
every pair of objects of a fibre, a sheaf of morphisms on `C/U` and an identification of its
sections over `f : V ⟶ U` with the hom-set between the pullbacks, natural in `f`.

This is weaker than Stacks 026F: effectivity of descent, condition (3), is not required, and
`PrestackData` restricts to split fibrations. -/
structure Stack (C : Type u) [Category.{v} C] (J : GrothendieckTopology C) where
  /-- The underlying prestack data. -/
  data : PrestackData C
  /-- The sheaf of morphisms on `C/U`, Stacks 02ZB. -/
  morSheaf : ∀ (U : C) (_ _ : (data.obj (op U)).α), Sheaf (J.over U) (Type v)
  /-- Its sections over `f : V ⟶ U` are the morphisms `f^* x ⟶ f^* y` of the fibre over `V`. -/
  sections : ∀ (U : C) (x y : (data.obj (op U)).α) (f : Over U),
    (morSheaf U x y).obj.obj (op f) ≃
      ((data.pb f.hom).obj x ⟶ (data.pb f.hom).obj y)
  /-- The identification is natural in `f`. -/
  sections_naturality : ∀ (U : C) (x y : (data.obj (op U)).α)
    (f g : Over U) (φ : f ⟶ g) (ψ : (morSheaf U x y).obj.obj (op g)),
    sections U x y f ((morSheaf U x y).obj.map (op φ) ψ) =
    eqToHom (by
        rw [show f.hom = φ.left ≫ g.hom from (Over.w φ).symm]
        exact data.pb_factor g.hom φ.left x)
      ≫ (data.map φ.left.op).toFunctor.map (sections U x y g ψ)
      ≫ eqToHom (by
        rw [show f.hom = φ.left ≫ g.hom from (Over.w φ).symm]
        exact (data.pb_factor g.hom φ.left y).symm)

variable {J : GrothendieckTopology C}

/-- A 1-morphism of stacks: a morphism of the underlying data together with the induced morphisms
of sheaves of morphisms, compatible with the identifications of their sections. -/
structure Stack.Hom (T T' : Stack C J) where
  /-- The morphism of underlying data. -/
  η : T.data ⟶ T'.data
  /-- The induced morphism on sheaves of morphisms. -/
  onMor : ∀ (U : C) (x y : (T.data.obj (op U)).α),
    T.morSheaf U x y ⟶
      T'.morSheaf U ((η.app (op U)).toFunctor.obj x)
                    ((η.app (op U)).toFunctor.obj y)
  /-- On sections it is the map induced by `η` on hom-sets of the fibres. -/
  onMor_sections : ∀ (U : C) (x y : (T.data.obj (op U)).α) (f : Over U)
    (ψ : (T.morSheaf U x y).obj.obj (op f)),
    T'.sections U _ _ f ((onMor U x y).hom.app (op f) ψ) =
    eqToHom (PrestackData.nat_obj η f.hom x)
    ≫ (η.app (op f.left)).toFunctor.map (T.sections U x y f ψ)
    ≫ eqToHom (PrestackData.nat_obj η f.hom y).symm

namespace Stack.Hom

variable {T T' : Stack C J}

/-- Condition (1) of Stacks 04WQ, read fibrewise: every induced functor between fibres is full and
faithful. Stacks asks instead that the 1-morphism be fully faithful on the total categories, which
for these data is `CategoryTheory.Pseudofunctor.CoGrothendieck.map`. -/
def IsFullyFaithful (F : Stack.Hom T T') : Prop :=
  ∀ (U : C),
    Functor.Full (F.η.app (op U)).toFunctor ∧
      Functor.Faithful (F.η.app (op U)).toFunctor

/-- Condition (2) of Stacks 04WQ: every induced morphism of sheaves of morphisms is an
isomorphism. -/
def MorSheafIso (F : Stack.Hom T T') : Prop :=
  ∀ (U : C) (x y : (T.data.obj (op U)).α), IsIso (F.onMor U x y)

/-! ### Transport of hom-sets -/

/-- Transport of a hom-set along equalities of its two endpoints. -/
def homCongrEq {D : Type*} [Category D] {a a' b b' : D} (ha : a = a') (hb : b = b') :
    (a ⟶ b) ≃ (a' ⟶ b') :=
  Iso.homCongr (eqToIso ha) (eqToIso hb)

/-- Transporting a morphism along equalities of its endpoints is conjugation by the corresponding
`eqToHom`s. -/
@[simp] lemma homCongrEq_apply {D : Type*} [Category D] {a a' b b' : D}
    (ha : a = a') (hb : b = b') (φ : a ⟶ b) :
    homCongrEq ha hb φ = eqToHom ha.symm ≫ φ ≫ eqToHom hb := rfl

/-- Conjugating a fully faithful functor's action on a hom-set by `eqToHom`s is a bijection. -/
lemma bijective_eqToHom_map_eqToHom {D₁ D₂ : Type*} [Category D₁] [Category D₂] (G : D₁ ⥤ D₂)
    [G.Full] [G.Faithful] {X Y : D₁} {A B : D₂} (h1 : A = G.obj X) (h2 : G.obj Y = B) :
    Function.Bijective (fun φ : X ⟶ Y => eqToHom h1 ≫ G.map φ ≫ eqToHom h2) := by
  subst h1 h2
  simpa using (Functor.FullyFaithful.ofFullyFaithful G).map_bijective X Y

/-! ### (1) implies (2) -/

/-- If `F` is fully faithful fibrewise, every component of the induced morphism of presheaves of
morphisms is bijective. -/
lemma bijective_onMor_app (F : Stack.Hom T T') (h : F.IsFullyFaithful) (U : C)
    (x y : (T.data.obj (op U)).α) (f : Over U) :
    Function.Bijective ((F.onMor U x y).hom.app (op f)) := by
  obtain ⟨_, _⟩ := h f.left
  set θ := fun φ : (T.data.pb f.hom).obj x ⟶ (T.data.pb f.hom).obj y =>
    eqToHom (PrestackData.nat_obj F.η f.hom x)
      ≫ (F.η.app (op f.left)).toFunctor.map φ
      ≫ eqToHom (PrestackData.nat_obj F.η f.hom y).symm
  have hθ : Function.Bijective θ :=
    bijective_eqToHom_map_eqToHom (F.η.app (op f.left)).toFunctor _ _
  have hcomp : Function.Bijective
      ((T'.sections U _ _ f : _ → _) ∘ (F.onMor U x y).hom.app (op f)) := by
    have key : (T'.sections U _ _ f : _ → _) ∘ (F.onMor U x y).hom.app (op f) =
               θ ∘ (T.sections U x y f : _ → _) :=
      funext fun ψ => F.onMor_sections U x y f ψ
    rw [key]
    exact hθ.comp (T.sections U x y f).bijective
  simpa using (T'.sections U _ _ f).symm.bijective.comp hcomp

/-- Stacks 04WQ, (1) implies (2). -/
lemma morSheafIso_of_isFullyFaithful (F : Stack.Hom T T') (h : F.IsFullyFaithful) :
    F.MorSheafIso := by
  intro U x y
  have hcomp : ∀ X, IsIso ((F.onMor U x y).hom.app X) := by
    rintro ⟨f⟩
    exact (isIso_iff_bijective _).mpr (bijective_onMor_app F h U x y f)
  have hval : IsIso (F.onMor U x y).hom := NatIso.isIso_of_isIso_app _
  have : IsIso ((sheafToPresheaf (J.over U) (Type v)).map (F.onMor U x y)) := hval
  exact isIso_of_reflects_iso (F.onMor U x y) (sheafToPresheaf (J.over U) (Type v))

/-! ### (2) implies (1) -/

/-- `Stack.Hom.onMor_sections` read at `Over.mk (𝟙 U)`, transported along `sections`. -/
lemma sections_onMor_app_sections_symm (F : Stack.Hom T T') (U : C)
    (x y : (T.data.obj (op U)).α)
    (φ : (T.data.pb (𝟙 U)).obj x ⟶ (T.data.pb (𝟙 U)).obj y) :
    (T'.sections U ((F.η.app (op U)).toFunctor.obj x)
                   ((F.η.app (op U)).toFunctor.obj y) (Over.mk (𝟙 U)))
      ((F.onMor U x y).hom.app (op (Over.mk (𝟙 U)))
        ((T.sections U x y (Over.mk (𝟙 U))).symm φ)) =
    eqToHom (PrestackData.nat_obj F.η (𝟙 U) x)
      ≫ ((F.η.app (op U)).toFunctor).map φ
      ≫ eqToHom (PrestackData.nat_obj F.η (𝟙 U) y).symm := by
  have h := F.onMor_sections U x y (Over.mk (𝟙 U)) ((T.sections U x y (Over.mk (𝟙 U))).symm φ)
  rwa [Equiv.apply_symm_apply] at h

/-- The action of `F` on a hom-set of a fibre is a conjugate of the component of the induced
morphism of presheaves at `Over.mk (𝟙 U)`. -/
lemma map_eq_homCongrEq (F : Stack.Hom T T') (U : C) (x y : (T.data.obj (op U)).α) (φ : x ⟶ y) :
    ((F.η.app (op U)).toFunctor).map φ =
      homCongrEq (T'.data.pb_id_obj U _) (T'.data.pb_id_obj U _)
        ((T'.sections U ((F.η.app (op U)).toFunctor.obj x)
                        ((F.η.app (op U)).toFunctor.obj y) (Over.mk (𝟙 U)))
          ((F.onMor U x y).hom.app (op (Over.mk (𝟙 U)))
            ((T.sections U x y (Over.mk (𝟙 U))).symm
              (homCongrEq (T.data.pb_id_obj U x).symm (T.data.pb_id_obj U y).symm φ)))) := by
  rw [sections_onMor_app_sections_symm F U x y
    (homCongrEq (T.data.pb_id_obj U x).symm (T.data.pb_id_obj U y).symm φ),
    homCongrEq_apply, homCongrEq_apply]
  simp only [Functor.map_comp]
  simp [eqToHom_map]

/-- Under (2), the action of `F` on every hom-set of every fibre is bijective. -/
lemma bijective_map (F : Stack.Hom T T') (h : F.MorSheafIso) (U : C)
    (x y : (T.data.obj (op U)).α) :
    Function.Bijective (fun (φ : x ⟶ y) => ((F.η.app (op U)).toFunctor).map φ) := by
  have hbij : Function.Bijective ((F.onMor U x y).hom.app (op (Over.mk (𝟙 U)))) := by
    have : IsIso (F.onMor U x y) := h U x y
    have : IsIso (F.onMor U x y).hom :=
      (sheafToPresheaf (J.over U) (Type v)).map_isIso (F.onMor U x y)
    exact (isIso_iff_bijective _).mp (NatIso.isIso_app_of_isIso _ _)
  set tT := homCongrEq (T.data.pb_id_obj U x).symm (T.data.pb_id_obj U y).symm
  set tT' := homCongrEq (T'.data.pb_id_obj U _) (T'.data.pb_id_obj U _)
  set eT := T.sections U x y (Over.mk (𝟙 U))
  set eT' := T'.sections U _ _ (Over.mk (𝟙 U))
  convert tT'.bijective.comp <| eT'.bijective.comp <| hbij.comp <|
    eT.symm.bijective.comp tT.bijective using 1
  exact funext fun φ => map_eq_homCongrEq F U x y φ

/-- Stacks 04WQ, (2) implies (1). -/
lemma isFullyFaithful_of_morSheafIso (F : Stack.Hom T T') (h : F.MorSheafIso) :
    F.IsFullyFaithful := fun U =>
  ⟨⟨fun {x y} g => (bijective_map F h U x y).2 g⟩,
   ⟨fun {x y} _ _ hEq => (bijective_map F h U x y).1 hEq⟩⟩

/-- **Stacks 04WQ**. A 1-morphism of stacks is fully faithful if and only if it induces
isomorphisms on the sheaves of morphisms.

Condition (1) is read fibrewise here rather than on the total categories, which is what makes the
implication from (2) available without the reduction to strongly cartesian morphisms of the Stacks
proof; see `Stack.Hom.IsFullyFaithful`. -/
@[stacks 04WQ]
theorem isFullyFaithful_iff_morSheafIso (F : Stack.Hom T T') :
    F.IsFullyFaithful ↔ F.MorSheafIso :=
  ⟨morSheafIso_of_isFullyFaithful F, isFullyFaithful_of_morSheafIso F⟩

end Stack.Hom

end CategoryTheory
