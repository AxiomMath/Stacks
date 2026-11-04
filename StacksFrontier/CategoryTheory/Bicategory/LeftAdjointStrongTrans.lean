module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# Strong transformations between pseudofunctors of left adjoints

Let `C` be a category and let `F` and `G` be pseudofunctors `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` whose
transition functors are left adjoints: for every `p : Y ⟶ X` in `C` there are adjunctions
`F.map p ⊣ RF p` and `G.map p ⊣ RG p`. This is the situation of a system of morphisms of topoi,
the transition functors being inverse images and their right adjoints direct images.

Suppose given functors `τ X : F X ⥤ G X`, each an equivalence, together with comparisons
`σ p : RF p ⋙ τ X ⟶ τ Y ⋙ RG p` of the *right* adjoints which are isomorphisms. The adjoint mate
of `σ p` is a comparison `τ X ⋙ G.map p ⟶ F.map p ⋙ τ Y` of the left adjoints, and it is an
isomorphism because the `τ` are equivalences. This file shows that these mates are the strong
naturality constraints of a strong transformation `F ⟶ G` with components `τ`, as soon as the `σ`
are compatible with the composition and identity constraints of `F` and `G`, read on the right
adjoints through `CategoryTheory.conjugateEquiv`.

The compatibilities are stated on the right adjoints because that is where they can be checked
in practice: direct images are restriction of sections along functors of sites, and the
compatibilities become identities between morphisms of sites.

## Main definitions

* `CategoryTheory.Pseudofunctor.leftAdjointNaturality`: the mate of `σ p`, as an isomorphism
  `F.map p ≫ τ Y ≅ τ X ≫ G.map p` in `Cat`;
* `CategoryTheory.Pseudofunctor.strongTransOfLeftAdjoints`: the strong transformation.

## Main results

* `CategoryTheory.isIso_mateEquiv_symm_of_isEquivalence`: the mate of an isomorphism between
  right adjoints along two equivalences is an isomorphism.

## Implementation notes

The three axioms of a strong transformation are proved in their inverse form, as equations of
`2`-squares between left adjoints. Mathlib's `CategoryTheory.mateEquiv_hcomp`,
`CategoryTheory.mateEquiv_conjugateEquiv_vcomp` and `CategoryTheory.conjugateEquiv_mateEquiv_vcomp`
turn each into the corresponding compatibility of the `σ`, and injectivity of the mate
correspondence finishes.
-/

@[expose] public section

universe v u v' u' v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open Bicategory Opposite TwoSquare

section Mates

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}

/-- **The mate of an isomorphism of right adjoints along two equivalences is an isomorphism.** -/
lemma isIso_mateEquiv_symm_of_isEquivalence (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    [G.IsEquivalence] [H.IsEquivalence] (β : TwoSquare R₁ H G R₂) [IsIso β.natTrans] :
    IsIso ((mateEquiv adj₁ adj₂).symm β).natTrans := by
  let adj₃ : G ⊣ G.inv := G.asEquivalence.toAdjunction
  let adj₄ : H ⊣ H.inv := H.asEquivalence.toAdjunction
  have : IsIso adj₃.unit := inferInstanceAs (IsIso G.asEquivalence.unitIso.hom)
  have : IsIso adj₄.counit := inferInstanceAs (IsIso H.asEquivalence.counitIso.hom)
  let γ := mateEquiv adj₄ adj₃ β
  have hγ : IsIso γ.natTrans := by
    simp only [γ, mateEquiv_apply]
    infer_instance
  have hβ : β = (mateEquiv adj₄ adj₃).symm γ := ((mateEquiv adj₄ adj₃).symm_apply_apply β).symm
  have e' : ((mateEquiv adj₁ adj₂).symm β).natTrans =
      (conjugateEquiv (adj₁.comp adj₄) (adj₃.comp adj₂)).symm γ.natTrans := by
    rw [hβ, iterated_mateEquiv_conjugateEquiv_symm adj₁ adj₂ adj₃ adj₄ γ]
    rfl
  rw [e']
  infer_instance

/-- The mate of the vertical identity square along identity adjunctions is the horizontal
identity square. -/
lemma mateEquiv_id_id_vId (T : A ⥤ C) :
    mateEquiv Adjunction.id Adjunction.id (TwoSquare.vId T) = TwoSquare.hId T := by
  ext X
  simp [TwoSquare.vId, TwoSquare.hId, mateEquiv]

/-- Inverting an equation between composites of isomorphisms. -/
lemma hom_comp_eq_of_inv_comp_eq {P Q R S T : A} (i₁ : P ≅ Q) (i₂ : Q ≅ R) (j₁ : P ≅ S)
    (j₂ : S ≅ T) (j₃ : T ≅ R) (h : i₂.inv ≫ i₁.inv = j₃.inv ≫ j₂.inv ≫ j₁.inv) :
    i₁.hom ≫ i₂.hom = j₁.hom ≫ j₂.hom ≫ j₃.hom := by
  simpa using (Iso.inv_eq_inv (i₁ ≪≫ i₂) (j₁ ≪≫ j₂ ≪≫ j₃)).1 (by simpa using h)

end Mates

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C]
  {F G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
  (RF : ∀ {X Y : C} (_ : Y ⟶ X), F.obj (.mk (op Y)) ⥤ F.obj (.mk (op X)))
  (adjF : ∀ {X Y : C} (p : Y ⟶ X), (F.map p.op.toLoc).toFunctor ⊣ RF p)
  (RG : ∀ {X Y : C} (_ : Y ⟶ X), G.obj (.mk (op Y)) ⥤ G.obj (.mk (op X)))
  (adjG : ∀ {X Y : C} (p : Y ⟶ X), (G.map p.op.toLoc).toFunctor ⊣ RG p)
  (τ : ∀ X : C, F.obj (.mk (op X)) ⥤ G.obj (.mk (op X)))
  (σ : ∀ {X Y : C} (p : Y ⟶ X), TwoSquare (RF p) (τ Y) (τ X) (RG p))

variable (F) in
/-- The inverse of the composition constraint of `F`, as a natural transformation of functors. -/
def mapCompInvNatTrans {X Y Z : C} (p : Y ⟶ X) (q : Z ⟶ Y) :
    (F.map p.op.toLoc).toFunctor ⋙ (F.map q.op.toLoc).toFunctor ⟶
      (F.map (q ≫ p).op.toLoc).toFunctor :=
  (F.mapComp p.op.toLoc q.op.toLoc).inv.toNatTrans

variable (F) in
/-- The inverse of the identity constraint of `F`, as a natural transformation of functors. -/
def mapIdInvNatTrans (X : C) : 𝟭 _ ⟶ (F.map (𝟙 X).op.toLoc).toFunctor :=
  (F.mapId (.mk (op X))).inv.toNatTrans

/-- The composition constraint of `F`, read on the right adjoints. -/
noncomputable abbrev rightAdjointComp {X Y Z : C} (p : Y ⟶ X) (q : Z ⟶ Y) :
    RF (q ≫ p) ⟶ RF q ⋙ RF p :=
  conjugateEquiv (adjF (q ≫ p)) ((adjF p).comp (adjF q)) (mapCompInvNatTrans F p q)

/-- The identity constraint of `F`, read on the right adjoints. -/
noncomputable abbrev rightAdjointId (X : C) : RF (𝟙 X) ⟶ 𝟭 _ :=
  conjugateEquiv (adjF (𝟙 X)) Adjunction.id (mapIdInvNatTrans F X)

/-- The inverse of the strong naturality constraint: the adjoint mate of `σ p`. -/
noncomputable def leftAdjointNaturalityInv {X Y : C} (p : Y ⟶ X) :
    TwoSquare (τ X) (F.map p.op.toLoc).toFunctor (G.map p.op.toLoc).toFunctor (τ Y) :=
  (mateEquiv (adjF p) (adjG p)).symm (σ p)

variable [∀ X, (τ X).IsEquivalence] (hσ : ∀ {X Y : C} (p : Y ⟶ X), IsIso (σ p).natTrans)

include hσ in
/-- The adjoint mate `leftAdjointNaturalityInv` of `σ p` is an isomorphism. -/
lemma isIso_leftAdjointNaturalityInv {X Y : C} (p : Y ⟶ X) :
    IsIso (leftAdjointNaturalityInv RF adjF RG adjG τ σ p).natTrans :=
  have := hσ p
  isIso_mateEquiv_symm_of_isEquivalence (adjF p) (adjG p) (σ p)

/-- The component of the strong transformation, as a one-morphism of `Cat`. -/
abbrev leftAdjointApp (X : C) : F.obj (.mk (op X)) ⟶ G.obj (.mk (op X)) :=
  Cat.Hom.ofFunctor (τ X)

/-- **The strong naturality constraint**: the adjoint mate of `σ p`, inverted. -/
noncomputable def leftAdjointNaturality {X Y : C} (p : Y ⟶ X) :
    F.map p.op.toLoc ≫ leftAdjointApp τ Y ≅ leftAdjointApp τ X ≫ G.map p.op.toLoc :=
  have := isIso_leftAdjointNaturalityInv RF adjF RG adjG τ σ hσ p
  Cat.Hom.isoMk (asIso (leftAdjointNaturalityInv RF adjF RG adjG τ σ p).natTrans).symm

/-- The inverse of `leftAdjointNaturality` is the natural transformation underlying
`leftAdjointNaturalityInv`. -/
@[simp]
lemma leftAdjointNaturality_inv_toNatTrans {X Y : C} (p : Y ⟶ X) :
    (leftAdjointNaturality RF adjF RG adjG τ σ hσ p).inv.toNatTrans =
      (leftAdjointNaturalityInv RF adjF RG adjG τ σ p).natTrans :=
  rfl

variable
  (hcomp : ∀ {X Y Z : C} (p : Y ⟶ X) (q : Z ⟶ Y),
    (σ (q ≫ p)).whiskerBottom (rightAdjointComp RG adjG p q) =
      (σ q ≫ₕ σ p).whiskerTop (rightAdjointComp RF adjF p q))
  (hid : ∀ X : C,
    (σ (𝟙 X)).whiskerBottom (rightAdjointId RG adjG X) =
      (TwoSquare.hId (τ X)).whiskerTop (rightAdjointId RF adjF X))

omit [∀ (X : C), (τ X).IsEquivalence] in
include hcomp in
/-- The composition axiom, in the inverse form, as an equation of `2`-squares. -/
lemma leftAdjointNaturalityInv_comp {X Y Z : C} (p : Y ⟶ X) (q : Z ⟶ Y) :
    (leftAdjointNaturalityInv RF adjF RG adjG τ σ (q ≫ p)).whiskerRight
        (mapCompInvNatTrans G p q) =
      (leftAdjointNaturalityInv RF adjF RG adjG τ σ p ≫ᵥ
        leftAdjointNaturalityInv RF adjF RG adjG τ σ q).whiskerLeft
        (mapCompInvNatTrans F p q) := by
  apply (mateEquiv (adjF (q ≫ p)) ((adjG p).comp (adjG q))).injective
  dsimp only [leftAdjointNaturalityInv]
  rw [mateEquiv_conjugateEquiv_vcomp (adjF (q ≫ p)) (adjG (q ≫ p)) ((adjG p).comp (adjG q)),
    conjugateEquiv_mateEquiv_vcomp (adjF (q ≫ p)) ((adjF p).comp (adjF q))
      ((adjG p).comp (adjG q)),
    mateEquiv_hcomp, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact hcomp p q

omit [∀ (X : C), (τ X).IsEquivalence] in
include hid in
/-- The identity axiom, in the inverse form, as an equation of `2`-squares. -/
lemma leftAdjointNaturalityInv_id (X : C) :
    (leftAdjointNaturalityInv RF adjF RG adjG τ σ (𝟙 X)).whiskerRight
        (mapIdInvNatTrans G X) =
      (TwoSquare.vId (τ X)).whiskerLeft (mapIdInvNatTrans F X) := by
  apply (mateEquiv (adjF (𝟙 X)) Adjunction.id).injective
  dsimp only [leftAdjointNaturalityInv]
  rw [mateEquiv_conjugateEquiv_vcomp (adjF (𝟙 X)) (adjG (𝟙 X)) Adjunction.id,
    conjugateEquiv_mateEquiv_vcomp (adjF (𝟙 X)) Adjunction.id Adjunction.id,
    mateEquiv_id_id_vId, Equiv.apply_symm_apply]
  exact hid X

include hid in
/-- The identity axiom of the strong transformation. -/
lemma leftAdjointNaturality_id (X : C) :
    (leftAdjointNaturality RF adjF RG adjG τ σ hσ (𝟙 X)).hom ≫
        leftAdjointApp τ X ◁ (G.mapId (.mk (op X))).hom =
      (F.mapId (.mk (op X))).hom ▷ leftAdjointApp τ X ≫
        (λ_ (leftAdjointApp τ X)).hom ≫ (ρ_ (leftAdjointApp τ X)).inv := by
  refine (Iso.inv_eq_inv
    (leftAdjointNaturality RF adjF RG adjG τ σ hσ (𝟙 X) ≪≫
      whiskerLeftIso (leftAdjointApp τ X) (G.mapId (.mk (op X))))
    (whiskerRightIso (F.mapId (.mk (op X))) (leftAdjointApp τ X) ≪≫
      λ_ (leftAdjointApp τ X) ≪≫ (ρ_ (leftAdjointApp τ X)).symm)).1 ?_
  ext M
  have k := NatTrans.congr_app (leftAdjointNaturalityInv_id RF adjF RG adjG τ σ hid X) M
  simp only [TwoSquare.vId, mapIdInvNatTrans] at k
  simp only [Iso.trans_inv, Cat.Hom₂.comp_app, leftAdjointNaturality_inv_toNatTrans]
  exact k

include hcomp in
/-- The composition axiom of the strong transformation. -/
lemma leftAdjointNaturality_comp {X Y Z : C} (p : Y ⟶ X) (q : Z ⟶ Y) :
    (leftAdjointNaturality RF adjF RG adjG τ σ hσ (q ≫ p)).hom ≫
        leftAdjointApp τ X ◁ (G.mapComp p.op.toLoc q.op.toLoc).hom =
      (F.mapComp p.op.toLoc q.op.toLoc).hom ▷ leftAdjointApp τ Z ≫
        (α_ _ _ _).hom ≫ F.map p.op.toLoc ◁ (leftAdjointNaturality RF adjF RG adjG τ σ hσ q).hom ≫
        (α_ _ _ _).inv ≫ (leftAdjointNaturality RF adjF RG adjG τ σ hσ p).hom ▷
          G.map q.op.toLoc ≫ (α_ _ _ _).hom := by
  ext M
  have k := NatTrans.congr_app (leftAdjointNaturalityInv_comp RF adjF RG adjG τ σ hcomp p q) M
  simp only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp, mapCompInvNatTrans,
    TwoSquare.natTrans, NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] at k
  simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Cat.associator_inv_app, Cat.associator_hom_app, eqToHom_refl, Category.id_comp,
    Category.comp_id]
  exact hom_comp_eq_of_inv_comp_eq
    ((Cat.Hom.toNatIso (leftAdjointNaturality RF adjF RG adjG τ σ hσ (q ≫ p))).app M)
    ((Cat.Hom.toNatIso (G.mapComp p.op.toLoc q.op.toLoc)).app ((τ X).obj M))
    ((τ Z).mapIso ((Cat.Hom.toNatIso (F.mapComp p.op.toLoc q.op.toLoc)).app M))
    ((Cat.Hom.toNatIso (leftAdjointNaturality RF adjF RG adjG τ σ hσ q)).app
      ((F.map p.op.toLoc).toFunctor.obj M))
    ((G.map q.op.toLoc).toFunctor.mapIso
      ((Cat.Hom.toNatIso (leftAdjointNaturality RF adjF RG adjG τ σ hσ p)).app M))
    (by rwa [← Category.assoc])

include hcomp hid in
/-- **The strong transformation between pseudofunctors of left adjoints** induced by a family of
equivalences `τ X` and a compatible family of isomorphisms `σ p` of right adjoints. Its strong
naturality constraints are the adjoint mates of the `σ p`. -/
noncomputable def strongTransOfLeftAdjoints : F.StrongTrans G where
  app a := leftAdjointApp τ a.as.unop
  naturality {_ _} f := leftAdjointNaturality RF adjF RG adjG τ σ hσ f.as.unop
  naturality_naturality := by
    intro a b f g η
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl : η = 𝟙 _ := Subsingleton.elim _ _
    simp
  naturality_id a := leftAdjointNaturality_id RF adjF RG adjG τ σ hσ hid a.as.unop
  naturality_comp f g :=
    leftAdjointNaturality_comp RF adjF RG adjG τ σ hσ hcomp f.as.unop g.as.unop

/-- The component of `strongTransOfLeftAdjoints` at `X` is `leftAdjointApp τ X`. -/
@[simp]
lemma strongTransOfLeftAdjoints_app (X : C) :
    (strongTransOfLeftAdjoints RF adjF RG adjG τ σ hσ hcomp hid).app (.mk (op X)) =
      leftAdjointApp τ X :=
  rfl

end Pseudofunctor

end CategoryTheory

end
