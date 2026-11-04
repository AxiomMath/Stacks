module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Iso

/-!
# Conjugating a morphism by a comparison of a functor with a composite

Let `P₁ : C ⥤ D₁` and `P₂ : C ⥤ D₂` be functors and let `e : P₂ ≅ P₁ ⋙ L` compare `P₂` with
`P₁` followed by a further functor `L : D₁ ⥤ D₂`.  A morphism `α : P₁ M ⟶ P₁ N` between two
values of `P₁` then has a *conjugate* `P₂ M ⟶ P₂ N`: the image of `α` under `L`, read through
`e` at both ends.

This is the shape of every "base change of a morphism" construction indexed by a category of
test objects, where `P₂` is the pullback to the base change at `U`, `P₁` the pullback at `T`,
and `L` the pullback along the induced map of base changes.  The two results below are what
make such a construction functorial in the test object: the conjugate by a comparison that is
whiskering with an isomorphism `𝟭 ≅ L` is the morphism itself, and the conjugate by a
comparison factoring through two others is the composite of the two conjugates.

## Main definitions

* `CategoryTheory.Functor.conjHom`: the conjugate of a morphism by a comparison.

## Main results

* `CategoryTheory.Functor.conjHom_id`: the unit law.
* `CategoryTheory.Functor.conjHom_comp`: the composition law.
* `CategoryTheory.Functor.conjHom_isoWhiskerLeft`: whiskering the comparison on the left by a
  further functor does not change the conjugate.
* `CategoryTheory.Functor.transportHomEquiv`: transport along an isomorphism of functors is a
  bijection of Hom sets.
* `CategoryTheory.Functor.transportHom_conjHom`: conjugation commutes with transport along a
  commuting square of comparisons.  This is what makes a comparison of two relative Hom
  functors natural.

## Implementation notes

Both results take the factorisation of the comparison as a hypothesis rather than rewriting
with it, so that a consumer applies them to a comparison it has already named: the conclusion
then matches the consumer's goal with no unfolding, which matters when the categories involved
are expensive to compare.
-/

@[expose] public section

namespace CategoryTheory.Functor

variable {C : Type*} {D₀ : Type*} {D₁ : Type*} {D₂ : Type*}
  [Category* C] [Category* D₀] [Category* D₁] [Category* D₂]

/-- The conjugate of a morphism `α : P₁ M ⟶ P₁ N` by a comparison `e : P₂ ≅ P₁ ⋙ L`: the image
of `α` under `L`, read through `e` at both ends. -/
def conjHom {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (e : P₂ ≅ P₁ ⋙ L) {M N : C}
    (α : P₁.obj M ⟶ P₁.obj N) : P₂.obj M ⟶ P₂.obj N :=
  e.hom.app M ≫ L.map α ≫ e.inv.app N

/-- **The unit law for conjugation.**  Conjugating by a comparison that is whiskering `P` with
an isomorphism `𝟭 ≅ L` is the identity. -/
theorem conjHom_id {P : C ⥤ D₁} {L : D₁ ⥤ D₁} (γ : 𝟭 D₁ ≅ L) (e : P ≅ P ⋙ L)
    (hfac : e = (rightUnitor P).symm ≪≫ isoWhiskerLeft P γ) {M N : C}
    (α : P.obj M ⟶ P.obj N) : conjHom e α = α := by
  subst hfac
  simp only [conjHom, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerLeft_inv, whiskerLeft_app,
    rightUnitor_hom_app, rightUnitor_inv_app, Category.id_comp]
  rw [← Category.assoc, ← γ.hom.naturality α]
  simp

/-- **The composition law for conjugation.**  If the comparison `c : P₂ ≅ P₀ ⋙ L` factors
through comparisons `c₁ : P₁ ≅ P₀ ⋙ L₁` and `c₂ : P₂ ≅ P₁ ⋙ L₂` and an identification
`τ : L ≅ L₁ ⋙ L₂`, then conjugating by `c` is conjugating by `c₁` and then by `c₂`. -/
theorem conjHom_comp {P₀ : C ⥤ D₀} {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂}
    {L₁ : D₀ ⥤ D₁} {L₂ : D₁ ⥤ D₂} {L : D₀ ⥤ D₂}
    (c₁ : P₁ ≅ P₀ ⋙ L₁) (c₂ : P₂ ≅ P₁ ⋙ L₂) (c : P₂ ≅ P₀ ⋙ L) (τ : L ≅ L₁ ⋙ L₂)
    (hfac : c = (c₂ ≪≫ isoWhiskerRight c₁ L₂ ≪≫ associator P₀ L₁ L₂) ≪≫
      (isoWhiskerLeft P₀ τ).symm)
    {M N : C} (α : P₀.obj M ⟶ P₀.obj N) :
    conjHom c α = conjHom c₂ (conjHom c₁ α) := by
  subst hfac
  simp only [conjHom, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerRight_inv, whiskerRight_app,
    isoWhiskerLeft_hom, isoWhiskerLeft_inv, whiskerLeft_app, associator_hom_app,
    associator_inv_app, Category.id_comp, Category.assoc, Functor.map_comp]
  rw [← reassoc_of% (τ.inv.naturality α)]
  simp

/-- Conjugating by a comparison whiskered on the left by a further functor is conjugating by
the comparison itself. -/
theorem conjHom_isoWhiskerLeft {C' : Type*} [Category* C'] (Q : C' ⥤ C)
    {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (e : P₂ ≅ P₁ ⋙ L) {M N : C'}
    (α : (Q ⋙ P₁).obj M ⟶ (Q ⋙ P₁).obj N) :
    conjHom (isoWhiskerLeft Q e ≪≫ (associator Q P₁ L).symm) α = conjHom e α := by
  simp [conjHom]

/-- Transport of a morphism between two values of `P` along an isomorphism `R ≅ P`: the case
of `CategoryTheory.Functor.conjHom` in which the further functor is the identity. -/
abbrev transportHom {P R : C ⥤ D₁} (u : R ≅ P) {M N : C} (α : P.obj M ⟶ P.obj N) :
    R.obj M ⟶ R.obj N :=
  conjHom (L := 𝟭 D₁) u α

/-- Transport along an isomorphism of functors is a bijection of Hom sets. -/
def transportHomEquiv {P R : C ⥤ D₁} (u : R ≅ P) (M N : C) :
    (P.obj M ⟶ P.obj N) ≃ (R.obj M ⟶ R.obj N) where
  toFun := transportHom u
  invFun := transportHom u.symm
  left_inv α := by simp [transportHom, conjHom]
  right_inv α := by simp [transportHom, conjHom]

/-- **Conjugation commutes with transport.**  Given comparisons `a : P₁ ≅ P₀ ⋙ L` and
`b : R₁ ≅ R₀ ⋙ L` and transports `u₀ : R₀ ≅ P₀`, `u₁ : R₁ ≅ P₁` whose square commutes,
conjugating and then transporting is transporting and then conjugating. -/
theorem transportHom_conjHom {P₀ R₀ : C ⥤ D₁} {P₁ R₁ : C ⥤ D₂} {L : D₁ ⥤ D₂}
    (a : P₁ ≅ P₀ ⋙ L) (b : R₁ ≅ R₀ ⋙ L) (u₀ : R₀ ≅ P₀) (u₁ : R₁ ≅ P₁)
    (h : u₁ ≪≫ a = b ≪≫ isoWhiskerRight u₀ L)
    {M N : C} (α : P₀.obj M ⟶ P₀.obj N) :
    transportHom u₁ (conjHom a α) = conjHom b (transportHom u₀ α) := by
  have hM := NatTrans.congr_app (congrArg Iso.hom h) M
  have hN := NatTrans.congr_app (congrArg Iso.inv h) N
  simp only [Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app, isoWhiskerRight_hom,
    isoWhiskerRight_inv, whiskerRight_app] at hM hN
  simp only [transportHom, conjHom, Functor.id_map, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hM, hN]

end CategoryTheory.Functor

end
