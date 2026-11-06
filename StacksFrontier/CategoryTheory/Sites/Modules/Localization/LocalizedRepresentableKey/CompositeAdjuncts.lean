module

public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.LocalizedRepresentableTwoIso
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.SliceBeckChevalley

@[expose] public section

/-!
# Composites, adjuncts and localized inverse images

The general lemmas behind the transposed comparison of Stacks 04J7: reassociation and congruence
of composites of morphisms, the adjunct of a composite of two or three morphisms, the inverse
units and counits of composites of equivalences, the fibre transpose of a localized ringed topos,
and the comparison of the inverse image of a morphism of ringed topoi with localization.
-/

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedToposHom

universe u

namespace CategoryTheory

/-- Reassociation of a composite of three morphisms whose last factor is followed by an
identity, which is the shape a composite of whiskered isomorphisms with a unitor as its last
factor has. -/
theorem comp_comp_comp_id {C : Type*} [Category C] {W X Y Z : C} (a : W ⟶ X) (b : X ⟶ Y)
    (c : Y ⟶ Z) : a ≫ b ≫ (c ≫ 𝟙 Z) = (a ≫ b) ≫ c := by simp

/-- Congruence in the first factor of a composite, with the second factor an argument rather
than part of a motive.

This and `CategoryTheory.comp_left_of_eq` are what let one step of a long computation be applied
with the surrounding factors left to unification. Writing those factors into a `congrArg` motive
instead re-elaborates them, and a term elaborated in one place can carry a different instance
argument from the same term elaborated in another — two subterms that print identically and do
not match. -/
theorem comp_right_of_eq {C : Type*} [Category C] {W X Y : C} {a b : W ⟶ X} (h : a = b)
    (c : X ⟶ Y) : a ≫ c = b ≫ c :=
  congrArg (fun z => z ≫ c) h

/-- Congruence in the second factor of a composite, with the first factor an argument rather
than part of a motive. -/
theorem comp_left_of_eq {C : Type*} [Category C] {W X Y : C} (a : W ⟶ X) {b c : X ⟶ Y}
    (h : b = c) : a ≫ b = a ≫ c :=
  congrArg (fun z => a ≫ z) h

/-- Congruence in the first two factors of a three-factor composite, with the last factor an
argument. Reassociation, congruence and reassociation back in one step: all five morphisms are
arguments, so cancelling a shared last factor costs one unification against the goal instead of
three, which is the difference between fitting in a declaration's heartbeats and not. -/
theorem comp₂_comp_right_of_eq {C : Type*} [Category C] {W X X' Y Z : C} {a : W ⟶ X}
    {b : X ⟶ Y} {d : W ⟶ X'} {e : X' ⟶ Y} (h : a ≫ b = d ≫ e) (c : Y ⟶ Z) :
    a ≫ b ≫ c = d ≫ e ≫ c :=
  Eq.trans (Category.assoc a b c).symm
    (Eq.trans (congrArg (fun z => z ≫ c) h) (Category.assoc d e c))

/-- Congruence under a functor, with the functor an argument rather than part of a motive: the
same precaution as `CategoryTheory.comp_right_of_eq`, one level down. -/
theorem map_of_eq {C : Type*} [Category C] {D : Type*} [Category D] (F : C ⥤ D) {X Y : C}
    {a b : X ⟶ Y} (h : a = b) : F.map a = F.map b :=
  congrArg F.map h

/-- Reassociation of a composite whose last factor is followed by an identity, with the first
two factors in the image of a functor: the shape the comparison of Stacks 04J7 has once its
unitor is read off. -/
theorem map_comp_comp_id {C : Type*} [Category C] {D : Type*} [Category D] (F : C ⥤ D)
    {W X Y : C} (a : W ⟶ X) (b : X ⟶ Y) {Z : D} (c : F.obj Y ⟶ Z) :
    F.map a ≫ F.map b ≫ (c ≫ 𝟙 Z) = F.map (a ≫ b) ≫ c := by simp

/-- Collapsing three consecutive factors in the image of a functor into one, after a composite
of three morphisms whose last lands in that image: the shape the 04IE-level residue of Stacks
04J7 has once its fibre transpose has been evaluated. As with
`CategoryTheory.comp₄_comp_assoc`, every morphism is an argument. -/
theorem comp₃_map₃_comp {C : Type*} [Category C] {D : Type*} [Category D] (F : D ⥤ C)
    {X₀ X₁ X₂ X₃ : C} {Y₀ Y₁ Y₂ Y₃ : D} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ F.obj Y₀)
    (n : Y₀ ⟶ Y₁) (h₁ : Y₁ ⟶ Y₂) (h₂ : Y₂ ⟶ Y₃) (z : F.obj Y₃ ⟶ X₃) :
    (a ≫ b ≫ c ≫ F.map n) ≫ F.map h₁ ≫ F.map h₂ ≫ z =
      a ≫ b ≫ c ≫ F.map (n ≫ h₁ ≫ h₂) ≫ z := by simp

/-- Collapsing two consecutive factors in the image of a functor into one. -/
theorem comp₂_map₂_comp {C : Type*} [Category C] {D : Type*} [Category D] (F : D ⥤ C)
    {X₀ X₁ X₂ : C} {Y₀ Y₁ Y₂ : D} (a : X₀ ⟶ X₁) (b : X₁ ⟶ F.obj Y₀) (n : Y₀ ⟶ Y₁)
    (h : Y₁ ⟶ Y₂) (z : F.obj Y₂ ⟶ X₂) :
    a ≫ b ≫ F.map n ≫ F.map h ≫ z = a ≫ b ≫ F.map (n ≫ h) ≫ z := by simp

/-- Reassociation moving the first factor of a composite's second half onto its first half, for
a first half of four factors: the shape a transposed four-factor comparison has once the
transpose of the opposite side has been split off. All six morphisms are arguments, so the step
costs one unification against the goal rather than a search inside nested metavariables. -/
theorem comp₄_comp_assoc {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : C} (a : X₀ ⟶ X₁)
    (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) (e : X₄ ⟶ X₅) (k : X₅ ⟶ X₆) :
    (a ≫ b ≫ c ≫ d) ≫ e ≫ k = (a ≫ b ≫ c ≫ (d ≫ e)) ≫ k := by simp

/-- Reassociation gathering the last factor of a six-factor composite onto the outside, so that
a morphism standing at the end of both sides of an equation can be cancelled. All six morphisms
are arguments, so the step costs one unification against the goal rather than a search inside
nested metavariables. -/
theorem comp₅_comp_assoc {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : C} (a : X₀ ⟶ X₁)
    (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) (e : X₄ ⟶ X₅) (k : X₅ ⟶ X₆) :
    a ≫ b ≫ c ≫ d ≫ e ≫ k = (a ≫ b ≫ c ≫ d ≫ e) ≫ k := by simp

/-- Reassociation gathering the last factor of a seven-factor composite onto the outside. All
seven morphisms are arguments, so the step costs one unification against the goal rather than a
search inside nested metavariables. -/
theorem comp₆_comp_assoc {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ : C} (a : X₀ ⟶ X₁)
    (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) (e : X₄ ⟶ X₅) (g : X₅ ⟶ X₆) (k : X₆ ⟶ X₇) :
    a ≫ b ≫ c ≫ d ≫ e ≫ g ≫ k = (a ≫ b ≫ c ≫ d ≫ e ≫ g) ≫ k := by simp

/-- **Base change along the inverse of an isomorphism, read through `Over.forget`.** The
comparison of `Over.pullback e.inv` with `Over.map e.hom` is, on underlying objects, the
projection out of the pullback: both the comparison and that projection are the counit of the
adjunction `Over.map e.inv ⊣ Over.pullback e.inv` read through uniqueness of right adjoints. -/
theorem Over.mapIso_counit_app_left {E : Type*} [Category E] {K H : E} (e : K ≅ H)
    (Z : Over K) : ((Over.mapIso e.symm).counit.app Z).left = 𝟙 Z.left := by
  simp only [mapIso, Comma.mapRightIso, Comma.mapRightId, Functor.id_obj,
    Comma.mapRight_obj_right, Comma.mapRight_obj_left, Comma.mapRightEq, Comma.mapRightComp,
    Functor.comp_obj, Equivalence.counit, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    NatIso.ofComponents'_inv_app, NatIso.ofComponents'_hom_app, Comma.comp_left]
  exact Eq.trans (Category.id_comp _) (Eq.trans (Category.id_comp _) rfl)

/-- On underlying objects, the comparison `Over.pullbackIsoMap e` of `Over.pullback e.inv` with
`Over.map e.hom` is the projection `pullback.fst : Z ×_H K ⟶ Z`. -/
theorem Over.forget_map_pullbackIsoMap_hom_app {E : Type*} [Category E] [Limits.HasPullbacks E]
    {K H : E} (e : K ≅ H) (Z : Over K) :
    ((Over.pullbackIsoMap e).hom.app Z).left = Limits.pullback.fst Z.hom e.inv := by
  have h := congrArg Over.Hom.left (Adjunction.rightAdjointUniq_hom_app_counit
    (Over.mapPullbackAdj e.inv) (Over.mapIso e.symm).toAdjunction Z)
  simpa [Over.pullbackIsoMap, Over.mapPullbackAdj_counit_app,
    Over.mapIso_counit_app_left] using h

/-- An isomorphism's inverse, recognised from a composite that is the identity. -/
theorem eq_inv_of_hom_comp_eq_id {C : Type*} [Category C] {X Y : C} (α : X ≅ Y) {g : Y ⟶ X}
    (h : α.hom ≫ g = 𝟙 X) : g = α.inv := by
  rw [← Category.id_comp g, ← α.inv_hom_id, Category.assoc, h, Category.comp_id]

/-- Naturality of a transformation out of a composite, with the composite's action written as
two successive `Functor.map`s — the spelling a goal that applied the two functors in turn
carries, and which the composite's own `map` does not match syntactically. -/
theorem map_naturality {C₁ : Type*} [Category C₁] {C₂ : Type*} [Category C₂] {C₂' : Type*}
    [Category C₂'] {C₃ : Type*} [Category C₃] (L : C₁ ⥤ C₂) (M : C₂ ⥤ C₃) (L' : C₁ ⥤ C₂')
    (M' : C₂' ⥤ C₃) (η : L ⋙ M ⟶ L' ⋙ M') {A B : C₁} (φ : A ⟶ B) :
    M.map (L.map φ) ≫ η.app B = η.app A ≫ M'.map (L'.map φ) :=
  η.naturality φ

/-- Naturality of a transformation from a composite to the identity, with the composite's action
written as two successive `Functor.map`s. -/
theorem map_naturality_toId {C₁ : Type*} [Category C₁] {C₂ : Type*} [Category C₂]
    (L : C₁ ⥤ C₂) (M : C₂ ⥤ C₁) (η : L ⋙ M ⟶ 𝟭 C₁) {A B : C₁} (φ : A ⟶ B) :
    M.map (L.map φ) ≫ η.app B = η.app A ≫ φ :=
  η.naturality φ

/-- **A functor's action on a morphism, solved out of a natural isomorphism's naturality
square.** For `α : F ≅ G`, the square at `χ : A ⟶ B` read as a description of `F χ`: the
component of `α` at the source, then `G χ`, then the inverse component at the target.

Every object and morphism is a variable, so instantiating this costs one unification against the
goal. `Iso.eq_comp_inv` applied to `α.app B` inside the goal instead has to recognise the
component `α.app B` of a `CategoryTheory.Iso.app` as the naturality square's own component at the
target of `χ`, and that identification, at the composites a long computation carries, is worth
more than a whole declaration's heartbeats. -/
theorem map_eq_naturality_comp_inv_app {C : Type*} [Category C] {D : Type*} [Category D]
    {F G : C ⥤ D} (α : F ≅ G) {A B : C} (χ : A ⟶ B) :
    F.map χ = (α.hom.app A ≫ G.map χ) ≫ α.inv.app B :=
  (Iso.eq_comp_inv (α.app B)).2 (α.hom.naturality χ)

/-- Reassociation splitting a five-factor composite after its third factor. -/
theorem comp₃_comp₂_assoc {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ : C} (a : X₀ ⟶ X₁)
    (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) (e : X₄ ⟶ X₅) :
    a ≫ b ≫ c ≫ d ≫ e = (a ≫ b ≫ c) ≫ d ≫ e := by simp

/-- Three factors, each the image of a morphism under one functor, collected into one image. -/
theorem map₃_comp {C : Type*} [Category C] {D : Type*} [Category D] (F : D ⥤ C)
    {Y₀ Y₁ Y₂ Y₃ : D} (a : Y₀ ⟶ Y₁) (b : Y₁ ⟶ Y₂) (c : Y₂ ⟶ Y₃) :
    F.map a ≫ F.map b ≫ F.map c = F.map (a ≫ b ≫ c) := by simp

/-- Reassociation gathering the last factor of a four-factor composite onto the outside. -/
theorem comp₃_comp_assoc {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ : C} (a : X₀ ⟶ X₁)
    (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (k : X₃ ⟶ X₄) :
    a ≫ b ≫ c ≫ k = (a ≫ b ≫ c) ≫ k := by simp

/-- Six factors, each the image of a morphism under one functor, collected into a single image,
at the bracketing a comparison split into a head, a middle block and a tail arrives in. All six
morphisms and the functor are arguments. -/
theorem map₆_comp {C : Type*} [Category C] {D : Type*} [Category D] (F : D ⥤ C)
    {Y₀ Y₁ Y₂ Y₃ Y₄ Y₅ Y₆ : D} (a : Y₀ ⟶ Y₁) (b : Y₁ ⟶ Y₂) (c : Y₂ ⟶ Y₃) (d : Y₃ ⟶ Y₄)
    (e : Y₄ ⟶ Y₅) (g : Y₅ ⟶ Y₆) :
    F.map a ≫ (F.map b ≫ F.map c ≫ F.map d) ≫ F.map e ≫ F.map g =
      F.map (a ≫ b ≫ c ≫ d ≫ e ≫ g) := by simp

/-- A functor carries the inverse and then the forward component of an isomorphism of functors
at an object to the identity. -/
private theorem map_inv_app_comp_map_hom_app {C : Type*} [Category C] {D : Type*} [Category D]
    {E : Type*} [Category E] {F G : C ⥤ D} (α : F ≅ G) (H : D ⥤ E) (A : C) :
    H.map (α.inv.app A) ≫ H.map (α.hom.app A) = 𝟙 _ := by
  rw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]

end CategoryTheory

namespace CategoryTheory.Adjunction

/-- **The adjunct of a composite of two morphisms.** Under `L ⊣ R`, the morphism adjoint to
`d ≫ e : W ⟶ R T` is `L d` followed by the morphism adjoint to `e`, which is `L e` followed by
the counit at `T`. -/
theorem homEquiv_symm_comp₂ {C : Type*} [Category C] {D : Type*} [Category D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) {W Z : C} {T : D} (d : W ⟶ Z) (e : Z ⟶ R.obj T) :
    (adj.homEquiv W T).symm (d ≫ e) = L.map d ≫ L.map e ≫ adj.counit.app T := by
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_counit]

/-- **The adjunct of a composite of three morphisms**, in the form an equation between two
composites is transposed in. -/
theorem homEquiv_symm_comp₃ {C : Type*} [Category C] {D : Type*} [Category D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) {W Z Z' : C} {T : D} (a : W ⟶ Z) (b : Z ⟶ Z')
    (c : Z' ⟶ R.obj T) :
    (adj.homEquiv W T).symm (a ≫ b ≫ c) =
      L.map a ≫ L.map b ≫ L.map c ≫ adj.counit.app T := by
  rw [Adjunction.homEquiv_naturality_left_symm, homEquiv_symm_comp₂]

end CategoryTheory.Adjunction

namespace CategoryTheory.Equivalence

/-- **The inverse unit of a composite of two equivalences.** For `e : C ≌ D` and `g : D ≌ E`,
the inverse unit of `e.trans g` at `T` is `e⁻¹` of the inverse unit of `g` at `e T`, followed by
the inverse unit of `e` at `T`.

This is what splits an inverse unit of a composite equivalence into one factor for each of the
two equivalences it is composed from, which is how such a factor is reached by a lemma about a
single equivalence. -/
theorem trans_unitInv_app {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*}
    [Category E] (e : C ≌ D) (g : D ≌ E) (T : C) :
    (e.trans g).unitInv.app T =
      e.inverse.map (g.unitInv.app (e.functor.obj T)) ≫ e.unitInv.app T := by
  simp [Equivalence.trans]

/-- The inverse counit of the inverse equivalence is the unit. -/
theorem symm_counitInv_app {C : Type*} [Category C] {D : Type*} [Category D] (e : C ≌ D)
    (Z : C) : e.symm.counitInv.app Z = e.unit.app Z :=
  rfl

/-- **The inverse counit of a composite equivalence, split.** The counterpart of
`trans_unitInv_app` on the other side: one factor for each of the two equivalences the composite
is built from, which is how such a factor is reached by a lemma about a single equivalence. -/
theorem trans_counitInv_app {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*}
    [Category E] (e : C ≌ D) (g : D ≌ E) (T : E) :
    (e.trans g).counitInv.app T =
      g.counitInv.app T ≫ g.functor.map (e.counitInv.app (g.inverse.obj T)) := by
  simp [Equivalence.trans]

/-- **A morphism read through the inverse of an equivalence and followed by its inverse unit.**
Carried back by the functor it becomes the counit followed by the morphism itself: this is what
turns a computation in the localization of a ringed topos into one in the slice topos. -/
theorem functor_map_inverse_map_comp_unitInv {C : Type*} [Category C] {D : Type*} [Category D]
    (e : C ≌ D) {P : D} {Z : C} (m : P ⟶ e.functor.obj Z) :
    e.functor.map (e.inverse.map m ≫ e.unitInv.app Z) = e.counit.app P ≫ m := by simp

end CategoryTheory.Equivalence

namespace AlgebraicGeometry.RingedTopos

/-- Congruence in the transposed morphism, with the slice object and the target an argument
rather than part of a motive: the same precaution as `CategoryTheory.map_of_eq`, for the fibre
transpose. -/
theorem fibreTranspose_of_eq (X : RingedTopos.{u, u, u}) (F : X.Topos) (T : Over F) (G : X.Topos)
    {β β' : T.left ⟶ G} (h : β = β') :
    fibreTranspose X F T G β = fibreTranspose X F T G β' :=
  congrArg _ h

/-- **The fibre transpose of the projection out of `toOver F` is Stacks 04IE's comparison
undone.** `localizationInverseImageIso` identifies `j_F^{-1}G` carried into `Sh(C)/F` with
`toOver F G`, and `forget_localizationInverseImageIso_hom_app` says that identification is
compatible with the projection to `G` and the counit of the lower shriek; so the transpose of the
projection itself is that identification inverted, followed by the inverse unit of Stacks 04IE's
equivalence. -/
theorem fibreTranspose_toOver_counit (X : RingedTopos.{u, u, u}) (F : X.Topos) (G : X.Topos) :
    fibreTranspose X F ((CategoryTheory.toOver F).obj G) G
        ((CategoryTheory.forgetAdjToOver F).counit.app G) =
      (localizationEquivalence X F).inverse.map
          ((localizationInverseImageIso X F).inv.app G) ≫
        (localizationEquivalence X F).unitInv.app
          ((X.localizationMorphism F).toToposHom.inverseImage.obj G) := by
  have key : (localizationEquivalence X F).unitInv.app
        ((X.localizationMorphism F).toToposHom.inverseImage.obj G) =
      (localizationEquivalence X F).inverse.map
          ((localizationInverseImageIso X F).hom.app G) ≫
        fibreTranspose X F ((CategoryTheory.toOver F).obj G) G
          ((CategoryTheory.forgetAdjToOver F).counit.app G) :=
    Eq.trans (fibreTranspose_shriek_counit X F G).symm
      (Eq.trans (fibreTranspose_of_eq X F _ G
          (forget_localizationInverseImageIso_hom_app X F G).symm)
        (fibreTranspose_forget_map_comp X F G ((localizationInverseImageIso X F).hom.app G)
          ((CategoryTheory.forgetAdjToOver F).counit.app G)))
  rw [key, ← Category.assoc, CategoryTheory.map_inv_app_comp_map_hom_app, Category.id_comp]

/-- **The fibre transpose, evaluated.** Every morphism out of the sheaf underlying a slice object
is the adjunct of a morphism of `Sh(C)/F` into `toOver F G`, by `CategoryTheory.forgetAdjToOver`;
so its fibre transpose is that adjunct read through Stacks 04IE's equivalence, followed by Stacks
04IE's comparison undone and by the inverse unit.

This removes the fibre transpose from a computation entirely: what is left is a morphism of
`Sh(C)/F` and two canonical factors. -/
theorem fibreTranspose_eq (X : RingedTopos.{u, u, u}) (F : X.Topos) (T : Over F) (G : X.Topos)
    (β : T.left ⟶ G) :
    fibreTranspose X F T G β =
      (localizationEquivalence X F).inverse.map
          ((CategoryTheory.forgetAdjToOver F).homEquiv T G β) ≫
        (localizationEquivalence X F).inverse.map
            ((localizationInverseImageIso X F).inv.app G) ≫
          (localizationEquivalence X F).unitInv.app
            ((X.localizationMorphism F).toToposHom.inverseImage.obj G) := by
  refine Eq.trans (fibreTranspose_of_eq X F T G
    (Eq.trans (CategoryTheory.Adjunction.homEquiv_counit
        (CategoryTheory.forgetAdjToOver F) T G
        ((CategoryTheory.forgetAdjToOver F).homEquiv T G β)).symm
      (Equiv.symm_apply_apply ((CategoryTheory.forgetAdjToOver F).homEquiv T G) β)).symm) ?_
  refine Eq.trans (fibreTranspose_forget_map_comp X F G
    ((CategoryTheory.forgetAdjToOver F).homEquiv T G β)
    ((CategoryTheory.forgetAdjToOver F).counit.app G)) ?_
  exact CategoryTheory.comp_left_of_eq _ (fibreTranspose_toOver_counit X F G)

/-- **Stacks 04IE's comparison at `H`, inverted, split by Stacks 04J4.** By
`localizationInverseImageIso_eq_relocalization` the comparison at `H` is Stacks 04J4's comparison
with base change along `a`, then Stacks 04IE at `K` base-changed, then Stacks 03EH; so its
inverse ends in Stacks 04J4's comparison inverted.

That last factor is what an equation which reached `H` through the relocalization carries on its
other side, so naming this is what lets the two occurrences of Stacks 04J4 cancel. -/
theorem localizationInverseImageIso_inv_app_eq_relocalization (X : RingedTopos.{u, u, u})
    {H K : X.Topos} (a : H ⟶ K) (G : X.Topos) :
    (localizationInverseImageIso X H).inv.app G =
      ((CategoryTheory.toOverCompPullbackIso a).inv.app G ≫
          (Over.pullback a).map ((localizationInverseImageIso X K).inv.app G)) ≫
        (X.relocalizationInverseImageSliceIso a).inv.app
          ((X.localizationMorphism K).toToposHom.inverseImage.obj G) := by
  rw [localizationInverseImageIso_eq_relocalization X a]
  rfl

end AlgebraicGeometry.RingedTopos

namespace AlgebraicGeometry.RingedToposHom

variable {X Y : RingedTopos.{u, u, u}} (f : RingedToposHom X Y) (G : Y.Topos)

/-- The components of Stacks 04IF's characterization of `f'`: the identification is a whiskering
by the counit of Stacks 04IE at `F = f^{-1}G` followed by a unitor, so the component is that
counit. -/
theorem localizedInverseImageIso_hom_app'
    (Z : (RingedTopos.localizedRingedTopos Y G).Topos) :
    (f.localizedInverseImageIso G).hom.app Z =
      (RingedTopos.localizationEquivalence X
              (f.toToposHom.inverseImage.obj G)).counit.app
            ((f.toToposHom.over G).inverseImage.obj
              ((RingedTopos.localizationEquivalence Y G).functor.obj Z)) ≫
        𝟙 _ :=
  rfl

/-- **The two comparisons of Stacks 04IF agree.** Stacks 04IF supplies both the commutativity of
its square on inverse images, `f^{-1}j_F^{-1} ≅ j_G^{-1}(f')^{-1}`, and the characterization
`(f')^{-1} = Over.post f^{-1}` of `f'`; this says the first read into the slice topos and
followed by the second is the composite of Stacks 04IE at `F`, the identification of `f^{-1}` with
`Over.post f^{-1}` on `toOver`, and Stacks 04IE at `G`, out of which both were built.

It is the internal coherence of one tag's two comparisons, and it is what lets a computation that
enters through one of them leave through the other. -/
theorem map_inverseImageCompLocalizationIso_hom_app_comp_localizedInverseImageIso
    (A : Y.Topos) :
    (RingedTopos.localizationEquivalence X
              (f.toToposHom.inverseImage.obj G)).functor.map
          ((f.inverseImageCompLocalizationIso G).hom.app A) ≫
        (f.localizedInverseImageIso G).hom.app
          ((RingedTopos.localizationMorphism Y G).toToposHom.inverseImage.obj A) =
      (RingedTopos.localizationInverseImageIso X
              (f.toToposHom.inverseImage.obj G)).hom.app
            (f.toToposHom.inverseImage.obj A) ≫
        (f.toToposHom.inverseImageCompToOverIso G).hom.app A ≫
          (f.toToposHom.over G).inverseImage.map
            ((RingedTopos.localizationInverseImageIso Y G).inv.app A) := by
  refine Eq.trans (CategoryTheory.comp_right_of_eq (CategoryTheory.map_of_eq
    (RingedTopos.localizationEquivalence X (f.toToposHom.inverseImage.obj G)).functor
    (inverseImageCompLocalizationIso_hom_app f G A)) _) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _
    (localizedInverseImageIso_hom_app' f G _)) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _ (Category.comp_id _)) ?_
  refine Eq.trans (CategoryTheory.comp_right_of_eq
    ((RingedTopos.localizationEquivalence X
      (f.toToposHom.inverseImage.obj G)).functor.map_comp _ _) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _
    ((RingedTopos.localizationEquivalence X
      (f.toToposHom.inverseImage.obj G)).counit.naturality _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (CategoryTheory.comp_right_of_eq
    (CategoryTheory.Equivalence.functor_unit_comp _ _) _) ?_
  exact Category.id_comp _

/-- **Stacks 04IF's square on inverse images, inverted and read into the slice topos.** The
inverse of `inverseImageCompLocalizationIso`, carried by Stacks 04IE's equivalence at
`F = f^{-1}G`, is Stacks 04IF's characterization of `f'` followed by Stacks 04IE at `G` read
through `(f')^{-1}`, Stacks 04H1's comparison inverted, and Stacks 04IE at `F` inverted.

This is `map_inverseImageCompLocalizationIso_hom_app_comp_localizedInverseImageIso` with every
factor inverted, which is the direction a computation arriving at the comparison from Stacks
04J0's side needs. -/
theorem map_inverseImageCompLocalizationIso_inv_app (A : Y.Topos) :
    (RingedTopos.localizationEquivalence X
          (f.toToposHom.inverseImage.obj G)).functor.map
        ((f.inverseImageCompLocalizationIso G).inv.app A) =
      (f.localizedInverseImageIso G).hom.app
          ((RingedTopos.localizationMorphism Y G).toToposHom.inverseImage.obj A) ≫
        (f.toToposHom.over G).inverseImage.map
            ((RingedTopos.localizationInverseImageIso Y G).hom.app A) ≫
          (f.toToposHom.inverseImageCompToOverIso G).inv.app A ≫
            (RingedTopos.localizationInverseImageIso X
              (f.toToposHom.inverseImage.obj G)).inv.app
                (f.toToposHom.inverseImage.obj A) := by
  refine (CategoryTheory.eq_inv_of_hom_comp_eq_id
    ((RingedTopos.localizationEquivalence X
      (f.toToposHom.inverseImage.obj G)).functor.mapIso
        ((f.inverseImageCompLocalizationIso G).app A)) ?_).symm
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (CategoryTheory.comp_right_of_eq
    (map_inverseImageCompLocalizationIso_hom_app_comp_localizedInverseImageIso f G A) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _ (CategoryTheory.comp_left_of_eq _
    (Eq.trans (Category.assoc _ _ _).symm (CategoryTheory.comp_right_of_eq
      (CategoryTheory.map_inv_app_comp_map_hom_app _ _ _) _)))) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _ (CategoryTheory.comp_left_of_eq _
    (Category.id_comp _))) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _
    (Eq.trans (Category.assoc _ _ _).symm
      (CategoryTheory.comp_right_of_eq (Iso.hom_inv_id_app _ _) _))) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _ (Category.id_comp _)) ?_
  exact Iso.hom_inv_id_app _ _

end AlgebraicGeometry.RingedToposHom

end
