module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# Descent data along a fibrewise equivalence of pseudofunctors

Let `C` be a category, let `F` and `G` be pseudofunctors from `LocallyDiscrete Cᵒᵖ` to `Cat`,
and let `τ : F.StrongTrans G` be a strong transformation whose components `τ.app a` are
equivalences of categories. This file transports descent data from `F` to `G`: for every
family of morphisms `f i : X i ⟶ S` there is an induced functor
`F.DescentData f ⥤ G.DescentData f`, it is an equivalence, and it is compatible with the
canonical descent datum of an object. Consequently `F` has effective descent for a family
of morphisms if and only if `G` does.

The transport sends a descent datum `(M i, φ)` to the datum whose objects are the
`τ (M i)` and whose gluing morphisms are obtained from the `φ` by conjugating with the
comparison isomorphisms `τ (f ^* M) ≅ f ^* (τ M)` supplied by the strong naturality
constraint of `τ`. That the result again satisfies the compatibility
`Pseudofunctor.DescentData.pullHom_hom` is exactly the composition coherence of `τ`.

## Main definitions

* `CategoryTheory.Pseudofunctor.mapCompIsoApp`, the comparison isomorphism
  `gf ^* M ≅ g ^* (f ^* M)` attached to a composable pair of morphisms;
* `CategoryTheory.Pseudofunctor.StrongTrans.pullIso`, the comparison isomorphism
  `τ (f ^* M) ≅ f ^* (τ M)` attached to a strong transformation;
* `CategoryTheory.Pseudofunctor.StrongTrans.descentDataObj` and
  `CategoryTheory.Pseudofunctor.StrongTrans.descentDataFunctor`, the transport of a descent
  datum and the induced functor between the categories of descent data;
* `CategoryTheory.Pseudofunctor.StrongTrans.descentDataEquivalence`, the induced equivalence
  of categories of descent data when the components of `τ` are equivalences.

## Main results

* `CategoryTheory.Pseudofunctor.StrongTrans.naturality_comp'` and
  `CategoryTheory.Pseudofunctor.StrongTrans.app_naturality_comp'`, the composition coherence
  of a strong transformation in the flexible `mapComp'` form, and its evaluation at an object
  when the target bicategory is `Cat`;
* `CategoryTheory.Pseudofunctor.StrongTrans.toDescentDataCompDescentDataFunctorIso`, the
  compatibility of the transport with `Pseudofunctor.toDescentData`;
* `CategoryTheory.Pseudofunctor.StrongTrans.isEquivalence_toDescentData_iff`, the invariance
  of effective descent along a family;
* `CategoryTheory.Pseudofunctor.StrongTrans.isStackFor_iff_of_app_isEquivalence`, the
  invariance of `Pseudofunctor.IsStackFor`.

## Implementation notes

`descentDataObj` and `preimageDescentData` are `reducible`: the gluing morphisms of a descent
datum have types that mention its objects, so a rewrite inside such a type is only well formed
once the objects of the transported datum have been unfolded, and marking the two constructions
`reducible` is what makes them unfold at the transparency level the tactic framework uses for
that check.

The essential surjectivity of `descentDataFunctor` is obtained by choosing a preimage of each
object of a descent datum for `G` and gluing the chosen preimages with the morphisms obtained
from full faithfulness; `descentDataObjPreimageIso` then exhibits the original datum as the
transport of the resulting datum for `F`.
-/

@[expose] public section

universe w₁ w₂ v₁ v₂ u₁ u₂ t v' v u' u

namespace CategoryTheory

open Opposite Bicategory

namespace Pseudofunctor

section

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
  {F G : Pseudofunctor B C}

/-- The composition coherence of a strong transformation, in the flexible `mapComp'` form. -/
lemma StrongTrans.naturality_comp' (τ : StrongTrans F G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c)
    (fg : a ⟶ c) (h : f ≫ g = fg) :
    (τ.naturality fg).hom ≫ τ.app a ◁ (G.mapComp' f g fg h).hom =
      (F.mapComp' f g fg h).hom ▷ τ.app c ≫ (α_ _ _ _).hom ≫
        F.map f ◁ (τ.naturality g).hom ≫ (α_ _ _ _).inv ≫
        (τ.naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom := by
  subst h
  simp [mapComp'_eq_mapComp]

end

section

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {F G : Pseudofunctor B Cat.{v', u'}}

/-- The composition coherence of a strong transformation of pseudofunctors to `Cat`,
evaluated at an object. -/
lemma StrongTrans.app_naturality_comp' (τ : StrongTrans F G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c)
    (fg : a ⟶ c) (h : f ≫ g = fg) (M : F.obj a) :
    (τ.naturality fg).hom.toNatTrans.app M ≫
        (G.mapComp' f g fg h).hom.toNatTrans.app ((τ.app a).toFunctor.obj M) =
      (τ.app c).toFunctor.map ((F.mapComp' f g fg h).hom.toNatTrans.app M) ≫
        (τ.naturality g).hom.toNatTrans.app ((F.map f).toFunctor.obj M) ≫
        (G.map g).toFunctor.map ((τ.naturality f).hom.toNatTrans.app M) := by
  simpa using congr(($(τ.naturality_comp' f g fg h)).toNatTrans.app M)

end

section

open LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]

/-- For a pseudofunctor `F` from `LocallyDiscrete Cᵒᵖ` to `Cat` and morphisms `g : Y' ⟶ Y`
and `f : Y ⟶ X` with composite `gf`, this is the comparison isomorphism
`gf ^* M ≅ g ^* (f ^* M)`. -/
def mapCompIsoApp (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) {X Y Y' : C}
    (f : Y ⟶ X) (g : Y' ⟶ Y) (gf : Y' ⟶ X) (h : g ≫ f = gf) (M : F.obj (.mk (op X))) :
    (F.map gf.op.toLoc).toFunctor.obj M ≅
      (F.map g.op.toLoc).toFunctor.obj ((F.map f.op.toLoc).toFunctor.obj M) :=
  (Cat.Hom.toNatIso (F.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc (by aesop))).app M

/-- Naturality in `M` of the forward direction of `mapCompIsoApp`. -/
@[reassoc]
lemma mapCompIsoApp_hom_naturality (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    {X Y Y' : C} (f : Y ⟶ X) (g : Y' ⟶ Y) (gf : Y' ⟶ X) (h : g ≫ f = gf)
    {M N : F.obj (.mk (op X))} (a : M ⟶ N) :
    (F.map gf.op.toLoc).toFunctor.map a ≫ (F.mapCompIsoApp f g gf h N).hom =
      (F.mapCompIsoApp f g gf h M).hom ≫
        (F.map g.op.toLoc).toFunctor.map ((F.map f.op.toLoc).toFunctor.map a) :=
  (Cat.Hom.toNatIso (F.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc (by aesop))).hom.naturality a

/-- Naturality in `M` of the inverse direction of `mapCompIsoApp`. -/
@[reassoc]
lemma mapCompIsoApp_inv_naturality (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    {X Y Y' : C} (f : Y ⟶ X) (g : Y' ⟶ Y) (gf : Y' ⟶ X) (h : g ≫ f = gf)
    {M N : F.obj (.mk (op X))} (a : M ⟶ N) :
    (F.map g.op.toLoc).toFunctor.map ((F.map f.op.toLoc).toFunctor.map a) ≫
        (F.mapCompIsoApp f g gf h N).inv =
      (F.mapCompIsoApp f g gf h M).inv ≫ (F.map gf.op.toLoc).toFunctor.map a :=
  (Cat.Hom.toNatIso (F.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc (by aesop))).inv.naturality a

variable {F G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}

/-- The pullback `pullHom φ g gf₁ gf₂ hgf₁ hgf₂` of a morphism `φ` between pullbacks is
`g ^* φ` conjugated by the comparison isomorphisms `mapCompIsoApp`. -/
lemma pullHom_eq_mapCompIsoApp {X₁ X₂ Y : C} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom φ g gf₁ gf₂ hgf₁ hgf₂ =
      (F.mapCompIsoApp f₁ g gf₁ hgf₁ M₁).hom ≫ (F.map g.op.toLoc).toFunctor.map φ ≫
        (F.mapCompIsoApp f₂ g gf₂ hgf₂ M₂).inv := rfl

/-- Pulling back a morphism between pullbacks commutes with composing with maps of the
two source objects. -/
lemma pullHom_map_comp_map {X₁ X₂ Y : C} {M₁ N₁ : F.obj (.mk (op X₁))}
    {M₂ N₂ : F.obj (.mk (op X₂))} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} (a : N₁ ⟶ M₁) (b : M₂ ⟶ N₂)
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom ((F.map f₁.op.toLoc).toFunctor.map a ≫ φ ≫
        (F.map f₂.op.toLoc).toFunctor.map b) g gf₁ gf₂ hgf₁ hgf₂ =
      (F.map gf₁.op.toLoc).toFunctor.map a ≫ pullHom φ g gf₁ gf₂ hgf₁ hgf₂ ≫
        (F.map gf₂.op.toLoc).toFunctor.map b := by
  rw [pullHom_eq_mapCompIsoApp, pullHom_eq_mapCompIsoApp]
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.mapCompIsoApp_hom_naturality_assoc f₁ g gf₁ hgf₁ a,
    F.mapCompIsoApp_inv_naturality f₂ g gf₂ hgf₂ b]

variable (τ : StrongTrans F G)

namespace StrongTrans

/-- The comparison isomorphism attached to a strong transformation of pseudofunctors to
`Cat`, evaluated at an object: `τ (f ^* M) ≅ f ^* (τ M)`. -/
def pullIso {X Y : C} (h : Y ⟶ X) (M : F.obj (.mk (op X))) :
    (τ.app (.mk (op Y))).toFunctor.obj ((F.map h.op.toLoc).toFunctor.obj M) ≅
      (G.map h.op.toLoc).toFunctor.obj ((τ.app (.mk (op X))).toFunctor.obj M) :=
  (Cat.Hom.toNatIso (τ.naturality h.op.toLoc)).app M

/-- Naturality in `M` of the comparison isomorphism `pullIso`. -/
@[reassoc]
lemma pullIso_naturality {X Y : C} (h : Y ⟶ X) {M N : F.obj (.mk (op X))} (ψ : M ⟶ N) :
    (τ.app (.mk (op Y))).toFunctor.map ((F.map h.op.toLoc).toFunctor.map ψ) ≫
        (τ.pullIso h N).hom =
      (τ.pullIso h M).hom ≫
        (G.map h.op.toLoc).toFunctor.map ((τ.app (.mk (op X))).toFunctor.map ψ) :=
  (Cat.Hom.toNatIso (τ.naturality h.op.toLoc)).hom.naturality ψ

/-- Compatibility of `pullIso` with composition of morphisms, expressed through the
comparison isomorphisms `mapCompIsoApp` of `F` and `G`. -/
@[reassoc]
lemma pullIso_hom_comp_mapCompIsoApp_hom {X Y Y' : C} (f : Y ⟶ X) (g : Y' ⟶ Y) (gf : Y' ⟶ X)
    (h : g ≫ f = gf) (M : F.obj (.mk (op X))) :
    (τ.pullIso gf M).hom ≫ (G.mapCompIsoApp f g gf h ((τ.app (.mk (op X))).toFunctor.obj M)).hom =
      (τ.app (.mk (op Y'))).toFunctor.map (F.mapCompIsoApp f g gf h M).hom ≫
        (τ.pullIso g ((F.map f.op.toLoc).toFunctor.obj M)).hom ≫
        (G.map g.op.toLoc).toFunctor.map (τ.pullIso f M).hom :=
  τ.app_naturality_comp' f.op.toLoc g.op.toLoc gf.op.toLoc (by aesop) M

/-- Compatibility of `pullIso` with composition of morphisms, solved for the composite of
`G.mapCompIsoApp` with the image of the inverse of `pullIso`. -/
@[reassoc]
lemma mapCompIsoApp_hom_comp_map_pullIso_inv {X Y Y' : C} (f : Y ⟶ X) (g : Y' ⟶ Y) (gf : Y' ⟶ X)
    (h : g ≫ f = gf) (M : F.obj (.mk (op X))) :
    (G.mapCompIsoApp f g gf h ((τ.app (.mk (op X))).toFunctor.obj M)).hom ≫
        (G.map g.op.toLoc).toFunctor.map (τ.pullIso f M).inv =
      (τ.pullIso gf M).inv ≫
        (τ.app (.mk (op Y'))).toFunctor.map (F.mapCompIsoApp f g gf h M).hom ≫
        (τ.pullIso g ((F.map f.op.toLoc).toFunctor.obj M)).hom := by
  rw [← cancel_epi (τ.pullIso gf M).hom, Iso.hom_inv_id_assoc,
    τ.pullIso_hom_comp_mapCompIsoApp_hom_assoc f g gf h M,
    ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id, Category.comp_id]

/-- Compatibility of `pullIso` with composition of morphisms, expressed through the inverses
of the comparison isomorphisms `mapCompIsoApp`. -/
@[reassoc]
lemma pullIso_hom_comp_map_pullIso_hom_comp_mapCompIsoApp_inv {X Y Y' : C} (f : Y ⟶ X)
    (g : Y' ⟶ Y) (gf : Y' ⟶ X) (h : g ≫ f = gf) (M : F.obj (.mk (op X))) :
    (τ.pullIso g ((F.map f.op.toLoc).toFunctor.obj M)).hom ≫
        (G.map g.op.toLoc).toFunctor.map (τ.pullIso f M).hom ≫
        (G.mapCompIsoApp f g gf h ((τ.app (.mk (op X))).toFunctor.obj M)).inv =
      (τ.app (.mk (op Y'))).toFunctor.map (F.mapCompIsoApp f g gf h M).inv ≫
        (τ.pullIso gf M).hom := by
  rw [← Category.assoc, Iso.comp_inv_eq, Category.assoc,
    τ.pullIso_hom_comp_mapCompIsoApp_hom f g gf h M, ← Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, Category.id_comp]

/-- Compatibility of `pullIso` with composition of morphisms, solved for the composite of the
image of `pullIso` with the inverse of `G.mapCompIsoApp`. -/
@[reassoc]
lemma map_pullIso_hom_comp_mapCompIsoApp_inv {X Y Y' : C} (f : Y ⟶ X)
    (g : Y' ⟶ Y) (gf : Y' ⟶ X) (h : g ≫ f = gf) (M : F.obj (.mk (op X))) :
    (G.map g.op.toLoc).toFunctor.map (τ.pullIso f M).hom ≫
        (G.mapCompIsoApp f g gf h ((τ.app (.mk (op X))).toFunctor.obj M)).inv =
      (τ.pullIso g ((F.map f.op.toLoc).toFunctor.obj M)).inv ≫
        (τ.app (.mk (op Y'))).toFunctor.map (F.mapCompIsoApp f g gf h M).inv ≫
        (τ.pullIso gf M).hom := by
  rw [← cancel_epi (τ.pullIso g ((F.map f.op.toLoc).toFunctor.obj M)).hom,
    Iso.hom_inv_id_assoc,
    τ.pullIso_hom_comp_map_pullIso_hom_comp_mapCompIsoApp_inv f g gf h M]

/-- The image under a strong transformation of a morphism between pullbacks of two objects. -/
def mapPullHom {X₁ X₂ Y : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) :
    (G.map f₁.op.toLoc).toFunctor.obj ((τ.app (.mk (op X₁))).toFunctor.obj M₁) ⟶
      (G.map f₂.op.toLoc).toFunctor.obj ((τ.app (.mk (op X₂))).toFunctor.obj M₂) :=
  (τ.pullIso f₁ M₁).inv ≫ (τ.app (.mk (op Y))).toFunctor.map φ ≫ (τ.pullIso f₂ M₂).hom

/-- `mapPullHom` preserves composition. -/
@[reassoc]
lemma mapPullHom_comp {X₁ X₂ X₃ Y : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {M₃ : F.obj (.mk (op X₃))} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {f₃ : Y ⟶ X₃}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (ψ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map f₃.op.toLoc).toFunctor.obj M₃) :
    τ.mapPullHom φ ≫ τ.mapPullHom ψ = τ.mapPullHom (φ ≫ ψ) := by
  simp [mapPullHom]

/-- `mapPullHom` preserves identities. -/
@[simp]
lemma mapPullHom_id {X Y : C} {M : F.obj (.mk (op X))} {h : Y ⟶ X} :
    τ.mapPullHom (𝟙 ((F.map h.op.toLoc).toFunctor.obj M)) = 𝟙 _ := by
  simp [mapPullHom]

/-- `mapPullHom` sends the pullback `h ^* ψ` of a morphism `ψ` to `h ^* (τ ψ)`. -/
lemma mapPullHom_map {X Y : C} {M N : F.obj (.mk (op X))} (h : Y ⟶ X) (ψ : M ⟶ N) :
    τ.mapPullHom ((F.map h.op.toLoc).toFunctor.map ψ) =
      (G.map h.op.toLoc).toFunctor.map ((τ.app (.mk (op X))).toFunctor.map ψ) := by
  rw [mapPullHom, τ.pullIso_naturality h ψ, Iso.inv_hom_id_assoc]

/-- `mapPullHom` is injective when the component of `τ` at the common source is faithful. -/
lemma mapPullHom_injective {X₁ X₂ Y : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} [(τ.app (.mk (op Y))).toFunctor.Faithful]
    {φ φ' : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂}
    (h : τ.mapPullHom φ = τ.mapPullHom φ') : φ = φ' := by
  rw [mapPullHom, mapPullHom, cancel_epi, cancel_mono] at h
  exact (τ.app (.mk (op Y))).toFunctor.map_injective h

/-- Transport along a strong transformation commutes with pulling back a gluing morphism. -/
lemma pullHom_mapPullHom {X₁ X₂ Y : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom (τ.mapPullHom φ) g gf₁ gf₂ hgf₁ hgf₂ =
      τ.mapPullHom (pullHom φ g gf₁ gf₂ hgf₁ hgf₂) := by
  rw [pullHom_eq_mapCompIsoApp, pullHom_eq_mapCompIsoApp]
  dsimp only [mapPullHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [τ.mapCompIsoApp_hom_comp_map_pullIso_inv_assoc f₁ g gf₁ hgf₁ M₁,
    ← τ.pullIso_naturality_assoc g φ,
    τ.pullIso_hom_comp_map_pullIso_hom_comp_mapCompIsoApp_inv f₂ g gf₂ hgf₂ M₂]

section DescentData

variable {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- The transport of a descent datum along a strong transformation. -/
@[reducible, simps]
def descentDataObj (D : F.DescentData f) : G.DescentData f where
  obj i := (τ.app (.mk (op (X i)))).toFunctor.obj (D.obj i)
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := τ.mapPullHom (D.hom q f₁ f₂ hf₁ hf₂)
  pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    rw [τ.pullHom_mapPullHom, D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]
  hom_self Y q i g hg := by rw [D.hom_self q g hg, τ.mapPullHom_id]
  hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    rw [τ.mapPullHom_comp, D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃]

/-- The transport of a morphism of descent data along a strong transformation. -/
@[simps]
def descentDataMap {D₁ D₂ : F.DescentData f} (φ : D₁ ⟶ D₂) :
    τ.descentDataObj f D₁ ⟶ τ.descentDataObj f D₂ where
  hom i := (τ.app (.mk (op (X i)))).toFunctor.map (φ.hom i)
  comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
    dsimp only [descentDataObj]
    rw [← τ.mapPullHom_map, ← τ.mapPullHom_map, τ.mapPullHom_comp, τ.mapPullHom_comp,
      φ.comm q f₁ f₂ hf₁ hf₂]

/-- The functor between the categories of descent data induced by a strong transformation. -/
@[simps]
def descentDataFunctor : F.DescentData f ⥤ G.DescentData f where
  obj D := τ.descentDataObj f D
  map φ := τ.descentDataMap f φ
  map_id D := by ext i; simp [descentDataObj]
  map_comp φ ψ := by ext i; simp [descentDataObj]

/-- The components `pullIso` are compatible with the gluing morphisms of the transport of
`DescentData.ofObj M` and of `DescentData.ofObj (τ M)`. -/
lemma descentDataObjOfObjIso_comm (M : F.obj (.mk (op S))) ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (G.map f₁.op.toLoc).toFunctor.map (τ.pullIso (f i₁) M).hom ≫
        ((G.mapCompIsoApp (f i₁) f₁ q hf₁ ((τ.app (.mk (op S))).toFunctor.obj M)).inv ≫
          (G.mapCompIsoApp (f i₂) f₂ q hf₂ ((τ.app (.mk (op S))).toFunctor.obj M)).hom) =
      τ.mapPullHom ((F.mapCompIsoApp (f i₁) f₁ q hf₁ M).inv ≫
          (F.mapCompIsoApp (f i₂) f₂ q hf₂ M).hom) ≫
        (G.map f₂.op.toLoc).toFunctor.map (τ.pullIso (f i₂) M).hom := by
  rw [τ.map_pullIso_hom_comp_mapCompIsoApp_inv_assoc (f i₁) f₁ q hf₁ M,
    τ.pullIso_hom_comp_mapCompIsoApp_hom (f i₂) f₂ q hf₂ M]
  dsimp only [mapPullHom]
  simp only [Functor.map_comp, Category.assoc]

/-- The canonical descent datum of an object is transported to the canonical descent datum
of its image. -/
def descentDataObjOfObjIso (M : F.obj (.mk (op S))) :
    τ.descentDataObj f (DescentData.ofObj M) ≅
      DescentData.ofObj ((τ.app (.mk (op S))).toFunctor.obj M) :=
  DescentData.isoMk (fun i ↦ τ.pullIso (f i) M)
    (fun _ q _ _ f₁ f₂ hf₁ hf₂ ↦ τ.descentDataObjOfObjIso_comm f M q f₁ f₂ hf₁ hf₂)

/-- Transport of descent data is compatible with `Pseudofunctor.toDescentData`. -/
def toDescentDataCompDescentDataFunctorIso :
    F.toDescentData f ⋙ τ.descentDataFunctor f ≅
      (τ.app (.mk (op S))).toFunctor ⋙ G.toDescentData f :=
  NatIso.ofComponents (fun M ↦ τ.descentDataObjOfObjIso f M) (fun ψ ↦ by
    ext i
    exact τ.pullIso_naturality (f i) ψ)

section

variable [∀ a : LocallyDiscrete Cᵒᵖ, (τ.app a).toFunctor.Faithful]

/-- `descentDataFunctor` is faithful when the components of `τ` are faithful. -/
lemma faithful_descentDataFunctor : (τ.descentDataFunctor f).Faithful where
  map_injective {D₁ D₂} φ φ' h := by
    ext i
    exact (τ.app (.mk (op (X i)))).toFunctor.map_injective
      (congr_arg (fun ψ ↦ DescentData.Hom.hom ψ i) h)

variable [∀ a : LocallyDiscrete Cᵒᵖ, (τ.app a).toFunctor.Full]

/-- When the components of `τ` are fully faithful, every morphism between transported descent
data is the transport of a morphism of descent data. -/
lemma exists_descentDataMap_eq {D₁ D₂ : F.DescentData f}
    (ψ : τ.descentDataObj f D₁ ⟶ τ.descentDataObj f D₂) :
    ∃ φ : D₁ ⟶ D₂, τ.descentDataMap f φ = ψ := by
  refine ⟨{ hom i := (τ.app (.mk (op (X i)))).toFunctor.preimage (ψ.hom i)
            comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := ?_ }, ?_⟩
  · refine τ.mapPullHom_injective ?_
    have h := ψ.comm q f₁ f₂ hf₁ hf₂
    dsimp only [descentDataObj] at h
    rw [← τ.mapPullHom_comp, ← τ.mapPullHom_comp, τ.mapPullHom_map, τ.mapPullHom_map,
      Functor.map_preimage, Functor.map_preimage]
    exact h
  · ext i
    simp

/-- `descentDataFunctor` is full when the components of `τ` are fully faithful. -/
lemma full_descentDataFunctor : (τ.descentDataFunctor f).Full where
  map_surjective ψ := τ.exists_descentDataMap_eq f ψ

end

section

variable [∀ a : LocallyDiscrete Cᵒᵖ, (τ.app a).toFunctor.Full]
  [∀ a : LocallyDiscrete Cᵒᵖ, (τ.app a).toFunctor.Faithful]
  [∀ a : LocallyDiscrete Cᵒᵖ, (τ.app a).toFunctor.EssSurj]

/-- The gluing morphism between the chosen preimages of the objects of a descent datum
for `G`. -/
noncomputable def preimageDescentDataHom (E : G.DescentData f) ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (F.map f₁.op.toLoc).toFunctor.obj
        ((τ.app (.mk (op (X i₁)))).toFunctor.objPreimage (E.obj i₁)) ⟶
      (F.map f₂.op.toLoc).toFunctor.obj
        ((τ.app (.mk (op (X i₂)))).toFunctor.objPreimage (E.obj i₂)) :=
  (τ.app (.mk (op Y))).toFunctor.preimage
    ((τ.pullIso f₁ _).hom ≫
      (G.map f₁.op.toLoc).toFunctor.map
        ((τ.app (.mk (op (X i₁)))).toFunctor.objObjPreimageIso (E.obj i₁)).hom ≫
      E.hom q f₁ f₂ hf₁ hf₂ ≫
      (G.map f₂.op.toLoc).toFunctor.map
        ((τ.app (.mk (op (X i₂)))).toFunctor.objObjPreimageIso (E.obj i₂)).inv ≫
      (τ.pullIso f₂ _).inv)

omit [∀ a : LocallyDiscrete Cᵒᵖ, (τ.app a).toFunctor.Faithful] in
/-- The image under `mapPullHom` of `preimageDescentDataHom` is the gluing morphism of `E`
conjugated by the isomorphisms `objObjPreimageIso`. -/
lemma mapPullHom_preimageDescentDataHom (E : G.DescentData f) ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    τ.mapPullHom (τ.preimageDescentDataHom f E q f₁ f₂ hf₁ hf₂) =
      (G.map f₁.op.toLoc).toFunctor.map
          ((τ.app (.mk (op (X i₁)))).toFunctor.objObjPreimageIso (E.obj i₁)).hom ≫
        E.hom q f₁ f₂ hf₁ hf₂ ≫
        (G.map f₂.op.toLoc).toFunctor.map
          ((τ.app (.mk (op (X i₂)))).toFunctor.objObjPreimageIso (E.obj i₂)).inv := by
  rw [mapPullHom, preimageDescentDataHom, Functor.map_preimage]
  simp

/-- The descent datum for `F` on the chosen preimages of the objects of a descent datum
for `G`. -/
@[reducible]
noncomputable def preimageDescentData (E : G.DescentData f) : F.DescentData f where
  obj i := (τ.app (.mk (op (X i)))).toFunctor.objPreimage (E.obj i)
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := τ.preimageDescentDataHom f E q f₁ f₂ hf₁ hf₂
  pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    refine τ.mapPullHom_injective ?_
    rw [← τ.pullHom_mapPullHom, τ.mapPullHom_preimageDescentDataHom,
      τ.mapPullHom_preimageDescentDataHom, pullHom_map_comp_map,
      E.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]
  hom_self Y q i g hg := by
    refine τ.mapPullHom_injective ?_
    rw [τ.mapPullHom_preimageDescentDataHom, E.hom_self q g hg, τ.mapPullHom_id]
    simp [← Functor.map_comp]
  hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    refine τ.mapPullHom_injective ?_
    rw [← τ.mapPullHom_comp, τ.mapPullHom_preimageDescentDataHom,
      τ.mapPullHom_preimageDescentDataHom, τ.mapPullHom_preimageDescentDataHom]
    simp only [Category.assoc, Iso.inv_hom_id_map_assoc, DescentData.hom_comp_assoc]

/-- A descent datum for `G` is the transport of the descent datum on the chosen preimages
of its objects. -/
noncomputable def descentDataObjPreimageIso (E : G.DescentData f) :
    τ.descentDataObj f (τ.preimageDescentData f E) ≅ E :=
  DescentData.isoMk
    (fun i ↦ (τ.app (.mk (op (X i)))).toFunctor.objObjPreimageIso (E.obj i)) (by
      intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
      dsimp only [descentDataObj, preimageDescentData]
      rw [τ.mapPullHom_preimageDescentDataHom]
      simp [← Functor.map_comp])

/-- `descentDataFunctor` is essentially surjective when the components of `τ` are
equivalences. -/
lemma essSurj_descentDataFunctor : (τ.descentDataFunctor f).EssSurj where
  mem_essImage E := ⟨τ.preimageDescentData f E, ⟨τ.descentDataObjPreimageIso f E⟩⟩

/-- `descentDataFunctor` is an equivalence when the components of `τ` are equivalences. -/
lemma isEquivalence_descentDataFunctor : (τ.descentDataFunctor f).IsEquivalence :=
  have := τ.full_descentDataFunctor f
  have := τ.faithful_descentDataFunctor f
  have := τ.essSurj_descentDataFunctor f
  { }

end

/-- **Effective descent along a family is invariant under a fibrewise equivalence of
pseudofunctors.** -/
theorem isEquivalence_toDescentData_iff
    (hτ : ∀ a : LocallyDiscrete Cᵒᵖ, (τ.app a).toFunctor.IsEquivalence) :
    (F.toDescentData f).IsEquivalence ↔ (G.toDescentData f).IsEquivalence := by
  have (a : LocallyDiscrete Cᵒᵖ) : (τ.app a).toFunctor.Full := have := hτ a; inferInstance
  have (a : LocallyDiscrete Cᵒᵖ) : (τ.app a).toFunctor.Faithful := have := hτ a; inferInstance
  have (a : LocallyDiscrete Cᵒᵖ) : (τ.app a).toFunctor.EssSurj := have := hτ a; inferInstance
  have := τ.isEquivalence_descentDataFunctor f
  have := hτ (.mk (op S))
  constructor
  · intro _
    have : ((τ.app (.mk (op S))).toFunctor ⋙ G.toDescentData f).IsEquivalence :=
      Functor.isEquivalence_of_iso (τ.toDescentDataCompDescentDataFunctorIso f)
    exact Functor.isEquivalence_of_comp_left (τ.app (.mk (op S))).toFunctor _
  · intro _
    have : (F.toDescentData f ⋙ τ.descentDataFunctor f).IsEquivalence :=
      Functor.isEquivalence_of_iso (τ.toDescentDataCompDescentDataFunctorIso f).symm
    exact Functor.isEquivalence_of_comp_right _ (τ.descentDataFunctor f)

/-- **Transport of descent data along a fibrewise equivalence of pseudofunctors.** -/
noncomputable def descentDataEquivalence
    (hτ : ∀ a : LocallyDiscrete Cᵒᵖ, (τ.app a).toFunctor.IsEquivalence) :
    F.DescentData f ≌ G.DescentData f :=
  have (a : LocallyDiscrete Cᵒᵖ) : (τ.app a).toFunctor.Full := have := hτ a; inferInstance
  have (a : LocallyDiscrete Cᵒᵖ) : (τ.app a).toFunctor.Faithful := have := hτ a; inferInstance
  have (a : LocallyDiscrete Cᵒᵖ) : (τ.app a).toFunctor.EssSurj := have := hτ a; inferInstance
  have := τ.isEquivalence_descentDataFunctor f
  (τ.descentDataFunctor f).asEquivalence

end DescentData

/-- Being a stack for a presieve is invariant under a fibrewise equivalence of
pseudofunctors. -/
lemma isStackFor_iff_of_app_isEquivalence
    (hτ : ∀ a : LocallyDiscrete Cᵒᵖ, (τ.app a).toFunctor.IsEquivalence)
    {S : C} (R : Presieve S) : F.IsStackFor R ↔ G.IsStackFor R := by
  rw [Pseudofunctor.isStackFor_iff, Pseudofunctor.isStackFor_iff]
  exact τ.isEquivalence_toDescentData_iff _ hτ

end StrongTrans

end

end Pseudofunctor

end CategoryTheory

end
