module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
public import StacksFrontier.CategoryTheory.Sites.Descent.OfRefinement

/-!
# Descent data under a restriction of the ambient category

Let `ι : C' ⥤ C` be a functor and let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a pseudofunctor.
Restricting `F` along `ι` gives a pseudofunctor `F.restrict ι` on `LocallyDiscrete C'ᵒᵖ` whose
fibre over `U` is the fibre of `F` over `ι.obj U`. A family of morphisms `g i : X i ⟶ S` in `C'`
therefore has two categories of descent data: `(F.restrict ι).DescentData g`, whose gluing
morphisms are indexed by the objects of `C'` lying over `S`, and `F.DescentData (ι.map ∘ g)`,
whose gluing morphisms are indexed by *all* objects of `C` lying over `ι.obj S`. This file
compares them.

Restricting the gluing morphisms of a descent datum of the second kind to the objects coming
from `C'` is a functor `F.DescentData (ι.map ∘ g) ⥤ (F.restrict ι).DescentData g` compatible
with the canonical descent datum of an object. It is an equivalence as soon as the family
`g` admits chosen pullbacks and chosen threefold wide pullbacks in `C'` whose images under `ι`
are again pullbacks: a gluing morphism over an arbitrary object of `C` over `ι.obj S` is then
the pullback of its value on the image of the chosen pullback, which lies in `C'`. This is
exactly the statement that Mathlib's `CategoryTheory.Pseudofunctor.DescentData'` — the variant
of descent data phrased on chosen pullbacks — does not see the difference between the two
ambient categories.

## Main definitions

* `CategoryTheory.Pseudofunctor.restrict`, the restriction of a pseudofunctor on
  `LocallyDiscrete Cᵒᵖ` along a functor `ι : C' ⥤ C`;
* `CategoryTheory.Pseudofunctor.restrictDescentData`, the restriction functor on descent data;
* `CategoryTheory.Limits.ChosenPullback.map` and
  `CategoryTheory.Limits.ChosenPullback₃.map`, the image of a chosen pullback, respectively of
  a chosen threefold wide pullback, under a functor preserving it.

## Main results

* `CategoryTheory.Pseudofunctor.toDescentDataCompRestrictDescentDataIso`: restriction of
  descent data is compatible with `CategoryTheory.Pseudofunctor.toDescentData`;
* `CategoryTheory.Pseudofunctor.isEquivalence_restrictDescentData`: the restriction functor is
  an equivalence;
* `CategoryTheory.Pseudofunctor.isEquivalence_toDescentData_restrict_iff` and
  `CategoryTheory.Pseudofunctor.isEquivalence_toDescentData_restrict_iff_of_preserves`:
  effective descent for a family of `C'` is the same condition in both ambient categories.

## Implementation notes

`CategoryTheory.Pseudofunctor.restrict` is `reducible` and is spelled out field by field
rather than as `CategoryTheory.Pseudofunctor.comp` with the locally discrete lift of `ι`: the
categories of descent data over `S` and over `ι.obj S` have the same objects, and the
comparisons below are only well formed once that identification holds at the transparency the
tactic framework uses. Its coherence axioms are those of the composite, to which it is equal
by definition.

`CategoryTheory.Limits.ChosenPullback₃.ofHasPullbacks` produces the chosen threefold wide
pullback from the existence of pullbacks; it belongs beside
`CategoryTheory.Limits.ChosenPullback₃` and is proved here because that is where it is needed.

Nothing here carries a Stacks attribute: this is the category-theoretic substrate of the
comparison, and the source states none of it.
-/

@[expose] public section

universe t v' v u' u v₁ u₁ w₂ v₂ u₂

namespace CategoryTheory

open Opposite Bicategory Limits

namespace Limits

variable {C₀ : Type u} [Category.{v} C₀] {C₁ : Type u₁} [Category.{v₁} C₁]

/-- The image of a chosen pullback under a functor that carries it to a pullback square. -/
noncomputable def ChosenPullback.map (ι : C₀ ⥤ C₁) {X₁ X₂ S : C₀} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S}
    (h : ChosenPullback f₁ f₂)
    (hι : IsPullback (ι.map h.p₁) (ι.map h.p₂) (ι.map f₁) (ι.map f₂)) :
    ChosenPullback (ι.map f₁) (ι.map f₂) where
  pullback := ι.obj h.pullback
  p₁ := ι.map h.p₁
  p₂ := ι.map h.p₂
  condition := hι.w
  isLimit := hι.isLimit
  p := ι.map h.p
  hp₁ := by rw [← ι.map_comp, h.hp₁]

/-- The image of a chosen threefold wide pullback under a functor that carries the three
chosen pullbacks and the defining square to pullback squares. -/
noncomputable def ChosenPullback₃.map (ι : C₀ ⥤ C₁) {X₁ X₂ X₃ S : C₀} {f₁ : X₁ ⟶ S}
    {f₂ : X₂ ⟶ S} {f₃ : X₃ ⟶ S} {h₁₂ : ChosenPullback f₁ f₂} {h₂₃ : ChosenPullback f₂ f₃}
    {h₁₃ : ChosenPullback f₁ f₃} (h : ChosenPullback₃ h₁₂ h₂₃ h₁₃)
    (k₁₂ : IsPullback (ι.map h₁₂.p₁) (ι.map h₁₂.p₂) (ι.map f₁) (ι.map f₂))
    (k₂₃ : IsPullback (ι.map h₂₃.p₁) (ι.map h₂₃.p₂) (ι.map f₂) (ι.map f₃))
    (k₁₃ : IsPullback (ι.map h₁₃.p₁) (ι.map h₁₃.p₂) (ι.map f₁) (ι.map f₃))
    (k : IsPullback (ι.map h.p₁₂) (ι.map h.p₂₃) (ι.map h₁₂.p₂) (ι.map h₂₃.p₁)) :
    ChosenPullback₃ (h₁₂.map ι k₁₂) (h₂₃.map ι k₂₃) (h₁₃.map ι k₁₃) where
  chosenPullback := h.chosenPullback.map ι k
  p := ι.map h.p
  p₁ := ι.map h.p₁
  p₃ := ι.map h.p₃
  l := { f := ι.map h.p₁₃
         f_p₁ := show ι.map h.p₁₃ ≫ ι.map h₁₃.p₁ = _ by
           rw [← ι.map_comp, ChosenPullback₃.p₁₃_p₁]
         f_p₂ := show ι.map h.p₁₃ ≫ ι.map h₁₃.p₂ = _ by
           rw [← ι.map_comp, ChosenPullback₃.p₁₃_p₃]
         f_p := show ι.map h.p₁₃ ≫ ι.map h₁₃.p = _ by
           rw [← ι.map_comp, ChosenPullback₃.p₁₃_p] }
  hp₁ := show ι.map h.p₁₂ ≫ ι.map h₁₂.p₁ = _ by rw [← ι.map_comp, ChosenPullback₃.p₁₂_p₁]
  hp₃ := show ι.map h.p₂₃ ≫ ι.map h₂₃.p₂ = _ by rw [← ι.map_comp, ChosenPullback₃.p₂₃_p₃]

/-- The chosen threefold wide pullback of three morphisms to a common target, given three
chosen pullbacks of the pairs and the existence of pullbacks. -/
noncomputable def ChosenPullback₃.ofHasPullbacks [HasPullbacks C₀] {X₁ X₂ X₃ S : C₀}
    {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S} {f₃ : X₃ ⟶ S}
    (h₁₂ : ChosenPullback f₁ f₂) (h₂₃ : ChosenPullback f₂ f₃) (h₁₃ : ChosenPullback f₁ f₃) :
    ChosenPullback₃ h₁₂ h₂₃ h₁₃ where
  chosenPullback := ChosenPullback.ofHasPullback h₁₂.p₂ h₂₃.p₁
  l := (ChosenPullback.LiftStruct.nonempty (h := h₁₃)
      (show (Limits.pullback.fst h₁₂.p₂ h₂₃.p₁ ≫ h₁₂.p₁) ≫ f₁ =
          (Limits.pullback.snd h₁₂.p₂ h₂₃.p₁ ≫ h₂₃.p₂) ≫ f₃ by
        rw [Category.assoc, Category.assoc, h₁₂.hp₁, h₂₃.hp₂, ← h₂₃.hp₁,
          ← Limits.pullback.condition_assoc, h₁₂.hp₂])
      (show (Limits.pullback.fst h₁₂.p₂ h₂₃.p₁ ≫ h₁₂.p₁) ≫ f₁ = _ by
        rw [Category.assoc, h₁₂.hp₁]; rfl)).some

end Limits

namespace Pseudofunctor

/-! ### Two-cells of a pseudofunctor out of a locally discrete bicategory -/

section

variable {B₀ : Type u} [Category.{v} B₀] {D : Type u₂} [Bicategory.{w₂, v₂} D]

/-- A pseudofunctor out of a locally discrete bicategory sends a two-morphism to the
identification of the images of its (equal) source and target. -/
lemma map₂_eq_eqToHom (P : Pseudofunctor (LocallyDiscrete B₀) D)
    {a b : LocallyDiscrete B₀} {x y : a ⟶ b} (α : x ⟶ y) :
    P.map₂ α = eqToHom (congrArg P.map (LocallyDiscrete.eq_of_hom α)) := by
  obtain rfl := LocallyDiscrete.eq_of_hom α
  obtain rfl : α = 𝟙 _ := Subsingleton.elim _ _
  simp

/-- For a pseudofunctor out of a locally discrete bicategory, the flexible composition
constraint is the strict one preceded by the identification of the two composites. -/
lemma mapComp'_hom_eq (P : Pseudofunctor (LocallyDiscrete B₀) D)
    {a b c : LocallyDiscrete B₀} (x : a ⟶ b) (y : b ⟶ c) (xy : a ⟶ c) (h : x ≫ y = xy) :
    (P.mapComp' x y xy h).hom =
      eqToHom (congrArg P.map h.symm) ≫ (P.mapComp x y).hom :=
  congrArg (· ≫ (P.mapComp x y).hom) (map₂_eq_eqToHom P (eqToHom (by rw [h])))

end

/-! ### Restriction of a pseudofunctor along a functor of the base -/

open LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] {C' : Type u₁} [Category.{v₁} C']
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) (ι : C' ⥤ C)

/-- **The restriction of a pseudofunctor along a functor of the base.** For
`ι : C' ⥤ C` and a pseudofunctor `F` on `LocallyDiscrete Cᵒᵖ`, this is the pseudofunctor on
`LocallyDiscrete C'ᵒᵖ` whose fibre over `U` is the fibre of `F` over `ι.obj U` and whose
inverse image along `φ` is that of `F` along `ι.map φ`. -/
@[reducible] def restrict : Pseudofunctor (LocallyDiscrete C'ᵒᵖ) Cat.{v', u'} where
  obj a := F.obj ⟨op (ι.obj a.as.unop)⟩
  map {_ _} φ := F.map ⟨(ι.map φ.as.unop).op⟩
  map₂ {_ _ _ _} α := F.map₂ (ι.op.toPseudofunctor.map₂ α)
  map₂_id := (Pseudofunctor.comp ι.op.toPseudofunctor F).map₂_id
  map₂_comp := (Pseudofunctor.comp ι.op.toPseudofunctor F).map₂_comp
  mapId := (Pseudofunctor.comp ι.op.toPseudofunctor F).mapId
  mapComp := (Pseudofunctor.comp ι.op.toPseudofunctor F).mapComp
  map₂_whisker_left := (Pseudofunctor.comp ι.op.toPseudofunctor F).map₂_whisker_left
  map₂_whisker_right := (Pseudofunctor.comp ι.op.toPseudofunctor F).map₂_whisker_right
  map₂_associator := (Pseudofunctor.comp ι.op.toPseudofunctor F).map₂_associator
  map₂_left_unitor := (Pseudofunctor.comp ι.op.toPseudofunctor F).map₂_left_unitor
  map₂_right_unitor := (Pseudofunctor.comp ι.op.toPseudofunctor F).map₂_right_unitor

/-- The images under `ι` of two composable morphisms compose, as one-morphisms of the locally
discrete bicategory on the opposite category. -/
lemma map_op_toLoc_comp {X Y Z : C'} (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X) (h : g ≫ f = gf) :
    (ι.map f).op.toLoc ≫ (ι.map g).op.toLoc = (ι.map gf).op.toLoc := by
  subst h; rw [← Quiver.Hom.comp_toLoc, ← op_comp, ι.map_comp]

/-- The composition constraint of the restricted pseudofunctor is that of the original one
at the images of the two morphisms, preceded by the identification of the two composites. -/
lemma restrict_mapComp_hom {X Y Z : C'} (f : Y ⟶ X) (g : Z ⟶ Y) :
    ((F.restrict ι).mapComp f.op.toLoc g.op.toLoc).hom =
      eqToHom (congrArg F.map (LocallyDiscrete.eq_of_hom
        (ι.op.toPseudofunctor.mapComp f.op.toLoc g.op.toLoc).hom)) ≫
        (F.mapComp (ι.map f).op.toLoc (ι.map g).op.toLoc).hom :=
  congrArg (· ≫ (F.mapComp (ι.map f).op.toLoc (ι.map g).op.toLoc).hom) (map₂_eq_eqToHom F _)

/-- **The composition constraints of a pseudofunctor and of its restriction agree.** The
flexible composition constraint of `F.restrict ι` at a composable pair of `C'` is the one of
`F` at the images of that pair. -/
lemma restrict_mapComp' {X Y Z : C'} (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X) (h : g ≫ f = gf) :
    (F.restrict ι).mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc (by subst h; simp) =
      F.mapComp' (ι.map f).op.toLoc (ι.map g).op.toLoc (ι.map gf).op.toLoc
        (map_op_toLoc_comp ι f g gf h) := by
  subst h
  apply Iso.ext
  rw [mapComp'_hom_eq, mapComp'_hom_eq, restrict_mapComp_hom]
  exact eqToHom_trans_assoc rfl _ _

/-- `CategoryTheory.Pseudofunctor.restrict_mapComp'`, evaluated at an object. -/
lemma restrict_mapComp'_hom_app {X Y Z : C'} (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X)
    (h : g ≫ f = gf) (M : F.obj (.mk (op (ι.obj X)))) :
    ((F.restrict ι).mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
        (by subst h; simp)).hom.toNatTrans.app M =
      (F.mapComp' (ι.map f).op.toLoc (ι.map g).op.toLoc (ι.map gf).op.toLoc
        (map_op_toLoc_comp ι f g gf h)).hom.toNatTrans.app M := by
  rw [restrict_mapComp' F ι f g gf h]

/-- The inverse of `CategoryTheory.Pseudofunctor.restrict_mapComp'`, evaluated at an object. -/
lemma restrict_mapComp'_inv_app {X Y Z : C'} (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X)
    (h : g ≫ f = gf) (M : F.obj (.mk (op (ι.obj X)))) :
    ((F.restrict ι).mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
        (by subst h; simp)).inv.toNatTrans.app M =
      (F.mapComp' (ι.map f).op.toLoc (ι.map g).op.toLoc (ι.map gf).op.toLoc
        (map_op_toLoc_comp ι f g gf h)).inv.toNatTrans.app M := by
  rw [restrict_mapComp' F ι f g gf h]

/-- **Pulling back a gluing morphism is the same in the restricted pseudofunctor.** -/
lemma restrict_pullHom {X₁ X₂ : C'} {M₁ : F.obj (.mk (op (ι.obj X₁)))}
    {M₂ : F.obj (.mk (op (ι.obj X₂)))} {Y : C'} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (F.map (ι.map f₁).op.toLoc).toFunctor.obj M₁ ⟶
      (F.map (ι.map f₂).op.toLoc).toFunctor.obj M₂)
    {Y' : C'} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom (F := F.restrict ι) φ g gf₁ gf₂ hgf₁ hgf₂ =
      pullHom (F := F) φ (ι.map g) (ι.map gf₁) (ι.map gf₂)
        (by rw [← ι.map_comp, hgf₁]) (by rw [← ι.map_comp, hgf₂]) := by
  dsimp only [pullHom]
  rw [restrict_mapComp' F ι f₁ g gf₁ hgf₁, restrict_mapComp' F ι f₂ g gf₂ hgf₂]
  rfl

/-- Pulling back an identity gluing morphism gives an identity. -/
lemma pullHom_id_of_comp_eq {X₁ : C} {M : F.obj (.mk (op X₁))} {Y Y' : C} {f₁ : Y ⟶ X₁}
    (h : Y' ⟶ Y) (hf₁ : Y' ⟶ X₁) (w : h ≫ f₁ = hf₁) :
    pullHom (𝟙 ((F.map f₁.op.toLoc).toFunctor.obj M)) h hf₁ hf₁ w w = 𝟙 _ := by
  simp [pullHom]

/-- Auxiliary commutation lemma: a square whose two parallel sides are identities commutes as
soon as the other two agree. -/
private lemma comm_of_eq_of_isId {C₀ : Type*} [Category C₀] {A Bb : C₀} {P Q : A ⟶ Bb}
    (α : A ⟶ A) (β : Bb ⟶ Bb) (hα : α = 𝟙 A) (hβ : β = 𝟙 Bb) (h : P = Q) :
    α ≫ Q = P ≫ β := by
  subst hα; subst hβ; subst h; simp

/-! ### Restriction of descent data -/

section

variable {I : Type t} {S : C'} {X : I → C'} (g : ∀ i, X i ⟶ S)

/-- **The restriction of a descent datum along a functor of the base.** The gluing morphisms
of the restricted datum are those of the original one at the objects coming from `C'`. -/
@[simps]
def restrictDescentDataObj (D : F.DescentData (fun i ↦ ι.map (g i))) :
    (F.restrict ι).DescentData g where
  obj i := D.obj i
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
    D.hom (ι.map q) (ι.map f₁) (ι.map f₂) (by rw [← ι.map_comp, hf₁]) (by rw [← ι.map_comp, hf₂])
  pullHom_hom Y' Y h q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    rw [restrict_pullHom]
    exact D.pullHom_hom (ι.map h) (ι.map q) (ι.map q') (by rw [← ι.map_comp, hq])
      (ι.map f₁) (ι.map f₂) (by rw [← ι.map_comp, hf₁]) (by rw [← ι.map_comp, hf₂])
      (ι.map gf₁) (ι.map gf₂)
      (by rw [← ι.map_comp, hgf₁]) (by rw [← ι.map_comp, hgf₂])
  hom_self Y q i h hq := D.hom_self (ι.map q) (ι.map h) (by rw [← ι.map_comp, hq])
  hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := D.hom_comp (ι.map q) _ _ _ _ _ _

/-- **The restriction functor on descent data.** -/
@[simps]
def restrictDescentData :
    F.DescentData (fun i ↦ ι.map (g i)) ⥤ (F.restrict ι).DescentData g where
  obj D := restrictDescentDataObj F ι g D
  map {D₁ D₂} φ :=
    { hom i := φ.hom i
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := φ.comm (ι.map q) (ι.map f₁) (ι.map f₂)
        (by rw [← ι.map_comp, hf₁]) (by rw [← ι.map_comp, hf₂]) }

/-- **Restriction of descent data is compatible with the canonical descent datum of an
object**: the two descent data attached to an object of the fibre over `S` agree. -/
def toDescentDataCompRestrictDescentDataIso :
    F.toDescentData (fun i ↦ ι.map (g i)) ⋙ restrictDescentData F ι g ≅
      (F.restrict ι).toDescentData g :=
  NatIso.ofComponents (fun M ↦ DescentData.isoMk (fun _ ↦ Iso.refl _) (by
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    exact comm_of_eq_of_isId _ _ (CategoryTheory.Functor.map_id _ _)
      (CategoryTheory.Functor.map_id _ _)
      (congrArg₂ (· ≫ ·) (restrict_mapComp'_inv_app F ι (g i₁) f₁ q hf₁ M)
        (restrict_mapComp'_hom_app F ι (g i₂) f₂ q hf₂ M)).symm)) (by
    intros; ext i
    exact (comm_of_eq_of_isId _ _ (DescentData.isoMk_hom_hom _ _ i)
      (DescentData.isoMk_hom_hom _ _ i) rfl).symm)

end

/-! ### Chosen pullbacks and the comparison of the two categories of descent data -/

section

variable {I : Type t} {S : C'} {X : I → C'} {g : ∀ i, X i ⟶ S}
  (sq : ∀ i j, ChosenPullback (g i) (g j))
  (hsq : ∀ i j, IsPullback (ι.map (sq i j).p₁) (ι.map (sq i j).p₂) (ι.map (g i)) (ι.map (g j)))

/-- The images under `ι` of a family of chosen pullbacks of the family `g`. -/
noncomputable abbrev mapSq (i j : I) : ChosenPullback (ι.map (g i)) (ι.map (g j)) :=
  (sq i j).map ι (hsq i j)

/-- **Pulling back a gluing morphism to a chosen pullback is the same in the restricted
pseudofunctor.** -/
lemma restrict_pullHom' {obj obj' : ∀ i, F.obj (.mk (op (ι.obj (X i))))}
    (hom : ∀ i j, (F.map (ι.map (sq i j).p₁).op.toLoc).toFunctor.obj (obj i) ⟶
      (F.map (ι.map (sq i j).p₂).op.toLoc).toFunctor.obj (obj' j))
    ⦃Y : C'⦄ (q : Y ⟶ S) ⦃i₁ i₂ : I⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ g i₁ = q) (hf₂ : f₂ ≫ g i₂ = q) :
    DescentData'.pullHom' (F := F.restrict ι) (sq := sq) hom q f₁ f₂ hf₁ hf₂ =
      DescentData'.pullHom' (F := F) (sq := mapSq ι sq hsq) hom (ι.map q) (ι.map f₁) (ι.map f₂)
        (by rw [← ι.map_comp, hf₁]) (by rw [← ι.map_comp, hf₂]) := by
  rw [DescentData'.pullHom'_eq_pullHom (sq := mapSq ι sq hsq) hom (ι.map q) (ι.map f₁)
      (ι.map f₂) (ι.map ((sq i₁ i₂).isPullback.lift f₁ f₂ (by rw [hf₁, hf₂])))
      (by rw [← ι.map_comp, hf₁]) (by rw [← ι.map_comp, hf₂])
      (show ι.map _ ≫ ι.map (sq i₁ i₂).p₁ = ι.map f₁ by
        rw [← ι.map_comp, IsPullback.lift_fst])
      (show ι.map _ ≫ ι.map (sq i₁ i₂).p₂ = ι.map f₂ by
        rw [← ι.map_comp, IsPullback.lift_snd])]
  exact restrict_pullHom F ι (hom i₁ i₂) _ _ _ _ _

variable (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
  (hsq₃ : ∀ i j k, IsPullback (ι.map (sq₃ i j k).p₁₂) (ι.map (sq₃ i j k).p₂₃)
      (ι.map (sq i j).p₂) (ι.map (sq j k).p₁))

/-- The images under `ι` of a family of chosen threefold wide pullbacks of the family `g`. -/
noncomputable abbrev mapSq₃ (i j k : I) :
    ChosenPullback₃ (mapSq ι sq hsq i j) (mapSq ι sq hsq j k) (mapSq ι sq hsq i k) :=
  (sq₃ i j k).map ι (hsq i j) (hsq j k) (hsq i k) (hsq₃ i j k)

/-- A descent datum of `F` on the images of the chosen pullbacks, read as a descent datum of
the restricted pseudofunctor on the chosen pullbacks themselves. -/
noncomputable def descentDataPrimeRestrict
    (D : F.DescentData' (mapSq ι sq hsq) (mapSq₃ ι sq hsq sq₃ hsq₃)) :
    (F.restrict ι).DescentData' sq sq₃ where
  obj := D.obj
  hom := D.hom
  pullHom'_hom_self i := by
    rw [restrict_pullHom' F ι sq hsq D.hom (g i) (𝟙 (X i)) (𝟙 (X i))]
    exact D.pullHom'_self (ι.map (g i)) (ι.map (𝟙 (X i))) (by rw [← ι.map_comp]; simp)
  pullHom'_hom_comp i₁ i₂ i₃ := by
    rw [restrict_pullHom' F ι sq hsq D.hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂,
      restrict_pullHom' F ι sq hsq D.hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃,
      restrict_pullHom' F ι sq hsq D.hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃]
    exact D.comp_pullHom' (ι.map (sq₃ i₁ i₂ i₃).p) _ _ _ _ _ _

/-- A descent datum of the restricted pseudofunctor on the chosen pullbacks, read as a descent
datum of `F` on their images. -/
noncomputable def descentDataPrimeUnrestrict (D : (F.restrict ι).DescentData' sq sq₃) :
    F.DescentData' (mapSq ι sq hsq) (mapSq₃ ι sq hsq sq₃ hsq₃) where
  obj := D.obj
  hom := D.hom
  pullHom'_hom_self i := by
    have h1 : DescentData'.pullHom' (F := F) (sq := mapSq ι sq hsq) D.hom (ι.map (g i))
        (ι.map (𝟙 (X i))) (ι.map (𝟙 (X i))) (by rw [← ι.map_comp]; simp)
        (by rw [← ι.map_comp]; simp) = 𝟙 _ := by
      rw [← restrict_pullHom' F ι sq hsq D.hom (g i) (𝟙 (X i)) (𝟙 (X i))]
      exact D.pullHom'_hom_self i
    have h2 := DescentData'.pullHom_pullHom' (F := F) (sq := mapSq ι sq hsq) D.hom
      (𝟙 (ι.obj (X i))) (ι.map (g i)) (ι.map (g i)) (ι.map (𝟙 (X i))) (ι.map (𝟙 (X i)))
      (𝟙 (ι.obj (X i))) (𝟙 (ι.obj (X i))) (by simp)
      (by rw [← ι.map_comp]; simp) (by rw [← ι.map_comp]; simp) (by simp) (by simp)
    rw [← h2, h1, pullHom_id_of_comp_eq]
  pullHom'_hom_comp i₁ i₂ i₃ := by
    have key := D.pullHom'_hom_comp i₁ i₂ i₃
    rw [restrict_pullHom' F ι sq hsq D.hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂,
      restrict_pullHom' F ι sq hsq D.hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃,
      restrict_pullHom' F ι sq hsq D.hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁
        (sq₃ i₁ i₂ i₃).p₃] at key
    exact key

/-- **Descent data on chosen pullbacks do not see the restriction of the ambient category.**
The descent data of `F` on the images of the chosen pullbacks are the descent data of the
restricted pseudofunctor on the chosen pullbacks themselves. -/
noncomputable def descentDataPrimeRestrictEquivalence :
    F.DescentData' (mapSq ι sq hsq) (mapSq₃ ι sq hsq sq₃ hsq₃) ≌
      (F.restrict ι).DescentData' sq sq₃ where
  functor :=
    { obj D := descentDataPrimeRestrict F ι sq hsq sq₃ hsq₃ D
      map φ := { hom := φ.hom, comm := φ.comm } }
  inverse :=
    { obj D := descentDataPrimeUnrestrict F ι sq hsq sq₃ hsq₃ D
      map φ := { hom := φ.hom, comm := φ.comm } }
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (fun _ ↦ by ext i; exact (Category.comp_id _).trans (Category.id_comp _).symm)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (fun _ ↦ by ext i; exact (Category.comp_id _).trans (Category.id_comp _).symm)
  functor_unitIso_comp _ := by ext i; exact Category.comp_id _

/-- Restricting a descent datum and then reading it on the chosen pullbacks is reading it on
the images of the chosen pullbacks and then restricting. -/
noncomputable def restrictDescentDataCompFromDescentDataFunctorIso :
    restrictDescentData F ι g ⋙ DescentData'.fromDescentDataFunctor (F.restrict ι) sq sq₃ ≅
      DescentData'.fromDescentDataFunctor F (mapSq ι sq hsq) (mapSq₃ ι sq hsq sq₃ hsq₃) ⋙
        (descentDataPrimeRestrictEquivalence F ι sq hsq sq₃ hsq₃).functor :=
  Iso.refl _

include hsq hsq₃ in
/-- **Restriction of descent data along a functor of the base is an equivalence**, as soon as
the family has chosen pullbacks and chosen threefold wide pullbacks whose images are again
pullbacks. -/
theorem isEquivalence_restrictDescentData : (restrictDescentData F ι g).IsEquivalence := by
  have h1 : (DescentData'.fromDescentDataFunctor F (mapSq ι sq hsq)
      (mapSq₃ ι sq hsq sq₃ hsq₃)).IsEquivalence :=
    (DescentData'.descentDataEquivalence F (mapSq ι sq hsq)
      (mapSq₃ ι sq hsq sq₃ hsq₃)).isEquivalence_inverse
  have h3 : (DescentData'.fromDescentDataFunctor (F.restrict ι) sq sq₃).IsEquivalence :=
    (DescentData'.descentDataEquivalence (F.restrict ι) sq sq₃).isEquivalence_inverse
  have h2 : (restrictDescentData F ι g ⋙
      DescentData'.fromDescentDataFunctor (F.restrict ι) sq sq₃).IsEquivalence :=
    Functor.isEquivalence_of_iso
      (restrictDescentDataCompFromDescentDataFunctorIso F ι sq hsq sq₃ hsq₃).symm
  exact Functor.isEquivalence_of_comp_right (restrictDescentData F ι g)
    (DescentData'.fromDescentDataFunctor (F.restrict ι) sq sq₃)

include hsq hsq₃ in
/-- **Effective descent along a family of the smaller ambient category is the same condition in
both ambient categories.** -/
theorem isEquivalence_toDescentData_restrict_iff :
    ((F.restrict ι).toDescentData g).IsEquivalence ↔
      (F.toDescentData (fun i ↦ ι.map (g i))).IsEquivalence := by
  have := isEquivalence_restrictDescentData F ι sq hsq sq₃ hsq₃
  refine ⟨fun _ ↦ ?_, fun _ ↦
    Functor.isEquivalence_of_iso (toDescentDataCompRestrictDescentDataIso F ι g)⟩
  have := Functor.isEquivalence_of_iso (toDescentDataCompRestrictDescentDataIso F ι g).symm
  exact Functor.isEquivalence_of_comp_right (F.toDescentData (fun i ↦ ι.map (g i)))
    (restrictDescentData F ι g)

end

/-- **Effective descent along a family of the smaller ambient category is the same condition in
both ambient categories**, for a functor of the base that preserves pullbacks. -/
theorem isEquivalence_toDescentData_restrict_iff_of_preserves {I : Type t} {S : C'}
    {X : I → C'} (g : ∀ i, X i ⟶ S) [HasPullbacks C']
    [PreservesLimitsOfShape WalkingCospan ι] :
    ((F.restrict ι).toDescentData g).IsEquivalence ↔
      (F.toDescentData (fun i ↦ ι.map (g i))).IsEquivalence :=
  isEquivalence_toDescentData_restrict_iff F ι
    (fun i j ↦ ChosenPullback.ofHasPullback (g i) (g j))
    (fun i j ↦ (ChosenPullback.ofHasPullback (g i) (g j)).isPullback.map ι)
    (fun _ _ _ ↦ ChosenPullback₃.ofHasPullbacks _ _ _)
    (fun i j k ↦ (ChosenPullback₃.ofHasPullbacks
      (ChosenPullback.ofHasPullback (g i) (g j))
      (ChosenPullback.ofHasPullback (g j) (g k))
      (ChosenPullback.ofHasPullback (g i) (g k))).isPullback₂.map ι)

end Pseudofunctor

end CategoryTheory

end
