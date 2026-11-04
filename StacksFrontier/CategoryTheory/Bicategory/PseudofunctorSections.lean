module

public import Mathlib.CategoryTheory.Bicategory.Functor.Cat
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# The presheaf of sections of an object under a contravariant family of inverse images

Let `C` be a category, let `obj X` be a category for every object `X` of `C`, and let
`L f : obj Y ⥤ obj X` be a functor for every morphism `f : X ⟶ Y`, equipped with comparison
isomorphisms `L (𝟙 X) ≅ 𝟭` and `L (f ≫ g) ≅ L g ⋙ L f` satisfying the left unit coherence
`hidComp` and the associativity coherence `hassoc` of a pseudofunctor
`LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`. Suppose given a terminal object `top X` of each `obj X`, and
suppose each `L f` carries terminal objects to terminal objects; write `Γ_X(A) = (top X ⟶ A)`
for the sections of an object `A` of `obj X`.

Fixing an object `Y` of `C` and an object `G` of `obj Y`, this file builds the presheaf

`T ↦ {(y, s) | y : T ⟶ Y and s ∈ Γ_T((L y).obj G)}`

on `C`, with restriction along `g : T' ⟶ T` given by `(y, s) ↦ (g ≫ y, (L g) s)`, the second
coordinate being transported through the composition comparison.

## Main definitions

* `CategoryTheory.LocallyDiscrete.fibreSections`: the sections `Γ_T((L y).obj G)`;
* `CategoryTheory.LocallyDiscrete.pullSection`: the restriction of a section along a morphism
  of the base;
* `CategoryTheory.LocallyDiscrete.sectionsPresheaf`: the presheaf above.

## Main results

* `CategoryTheory.LocallyDiscrete.pullSection_id`: restricting along an identity does nothing,
  modulo the identification of `𝟙 ≫ y` with `y`;
* `CategoryTheory.LocallyDiscrete.pullSection_comp`: restricting along a composite is
  restricting twice, modulo the identification of `(g ≫ f) ≫ y` with `g ≫ f ≫ y`.
-/

@[expose] public section

namespace CategoryTheory.LocallyDiscrete

open Limits

universe v u v' u'

variable {C : Type u} [Category.{v} C] (obj : C → Cat.{v', u'})
  (L : ∀ {X Y : C}, (X ⟶ Y) → (obj Y ⥤ obj X))
  (top : ∀ X : C, obj X) (htop : ∀ X : C, IsTerminal (top X))
  (hterm : ∀ {X Y : C} (f : X ⟶ Y) {A : obj Y}, IsTerminal A → IsTerminal ((L f).obj A))
  (lid : ∀ X : C, L (𝟙 X) ≅ 𝟭 (obj X))
  (lcomp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), L (f ≫ g) ≅ L g ⋙ L f)

/-- The sections of `G` pulled back along `y`, i.e. `Γ_T((L y).obj G)`, taken as the morphisms
from the terminal object of the fibre over `T`. -/
abbrev fibreSections {Y : C} (G : obj Y) {T : C} (y : T ⟶ Y) : Type v' :=
  top T ⟶ (L y).obj G

include htop hterm lcomp in
/-- The restriction of a section `s` along a morphism `g : T' ⟶ T` of the base: the composite of
the unique morphism from `top T'` to the terminal object `(L g).obj (top T)`, the image `(L g) s`,
and the composition comparison `(L y ⋙ L g).obj G ⟶ (L (g ≫ y)).obj G`. -/
noncomputable def pullSection {Y : C} (G : obj Y) {T' T : C} (g : T' ⟶ T) (y : T ⟶ Y)
    (s : fibreSections obj L top G y) : fibreSections obj L top G (g ≫ y) :=
  (hterm g (htop T)).from (top T') ≫ (L g).map s ≫ (lcomp g y).inv.app G

/-- The identification of the functors attached to two equal morphisms, read at an object of
the fibre. -/
private lemma eqToHom_app_obj {T Y : C} {u v : T ⟶ Y} (e : u = v) (G : obj Y) :
    (eqToHom (congrArg (fun k : T ⟶ Y => L k) e)).app G =
      eqToHom (congrArg (fun k : T ⟶ Y => (L k).obj G) e) := by
  subst e
  simp

/-- Two pairs whose first coordinates are equal and whose second coordinates agree after
transport along that equality are equal. -/
private lemma sigma_transport {Y : C} (G : obj Y) {T : C} {y y' : T ⟶ Y} (e : y = y')
    (s : fibreSections obj L top G y) :
    (⟨y', s ≫ eqToHom (congrArg (fun k : T ⟶ Y => (L k).obj G) e)⟩ :
        Σ z : T ⟶ Y, fibreSections obj L top G z) = ⟨y, s⟩ := by
  subst e
  simp

section Coherences

variable
  (hidComp : ∀ {X Y : C} (p : X ⟶ Y),
    (lcomp (𝟙 X) p).hom ≫ Functor.whiskerLeft (L p) (lid X).hom ≫
        (Functor.rightUnitor (L p)).hom =
      eqToHom (congrArg (fun k : X ⟶ Y => L k) (Category.id_comp p)))
  (hassoc : ∀ {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W),
    (lcomp f (g ≫ h)).hom ≫ Functor.whiskerRight (lcomp g h).hom (L f) ≫
        (Functor.associator (L h) (L g) (L f)).hom ≫
          Functor.whiskerLeft (L h) (lcomp f g).inv ≫ (lcomp (f ≫ g) h).inv =
      eqToHom (congrArg (fun k : X ⟶ W => L k) (Category.assoc f g h).symm))

include htop hterm hidComp in
/-- **Restriction along an identity is the identity**, modulo the identification of `𝟙 ≫ y`
with `y`. -/
theorem pullSection_id {Y : C} (G : obj Y) {T : C} (y : T ⟶ Y)
    (s : fibreSections obj L top G y) :
    pullSection obj L top htop hterm lcomp G (𝟙 T) y s =
      s ≫ eqToHom (congrArg (fun k : T ⟶ Y => (L k).obj G) (Category.id_comp y).symm) := by
  have key := NatTrans.congr_app (hidComp y) G
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    eqToHom_app_obj obj L (Category.id_comp y) G] at key
  have hkey : (lcomp (𝟙 T) y).inv.app G ≫
      eqToHom (congrArg (fun k : T ⟶ Y => (L k).obj G) (Category.id_comp y)) =
        (lid T).hom.app ((L y).obj G) := by
    rw [← key, ← Category.assoc]
    simp
  have hnat : (L (𝟙 T)).map s ≫ (lid T).hom.app ((L y).obj G) =
      (lid T).hom.app (top T) ≫ s := (lid T).hom.naturality s
  have hone : (hterm (𝟙 T) (htop T)).from (top T) ≫
      (lid T).hom.app (top T) = 𝟙 (top T) :=
    (htop T).hom_ext _ _
  rw [← cancel_mono (eqToHom (congrArg (fun k : T ⟶ Y => (L k).obj G) (Category.id_comp y))),
    pullSection]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  rw [hkey, hnat, ← Category.assoc, hone, Category.id_comp]

include htop hterm hassoc in
/-- **Restriction along a composite is restriction twice**, modulo the identification of
`(g ≫ f) ≫ y` with `g ≫ f ≫ y`. -/
theorem pullSection_comp {Y : C} (G : obj Y) {T₂ T₁ T₀ : C} (g : T₂ ⟶ T₁) (f : T₁ ⟶ T₀)
    (y : T₀ ⟶ Y) (s : fibreSections obj L top G y) :
    pullSection obj L top htop hterm lcomp G (g ≫ f) y s ≫
        eqToHom (congrArg (fun k : T₂ ⟶ Y => (L k).obj G) (Category.assoc g f y)) =
      pullSection obj L top htop hterm lcomp G g (f ≫ y)
        (pullSection obj L top htop hterm lcomp G f y s) := by
  have key := NatTrans.congr_app (hassoc g f y) G
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp,
    eqToHom_app_obj obj L (Category.assoc g f y).symm G] at key
  have hQ : (L g).map ((lcomp f y).inv.app G) ≫ (L g).map ((lcomp f y).hom.app G) =
      𝟙 ((L g).obj ((L y ⋙ L f).obj G)) := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
  have hpent : (lcomp (g ≫ f) y).inv.app G ≫
      eqToHom (congrArg (fun k : T₂ ⟶ Y => (L k).obj G) (Category.assoc g f y)) =
        (lcomp g f).hom.app ((L y).obj G) ≫ (L g).map ((lcomp f y).inv.app G) ≫
          (lcomp g (f ≫ y)).inv.app G := by
    rw [← cancel_mono (eqToHom (congrArg (fun k : T₂ ⟶ Y => (L k).obj G)
      (Category.assoc g f y).symm))]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rw [← key]
    simp only [Iso.inv_hom_id_app_assoc]
    rw [← Category.assoc ((L g).map ((lcomp f y).inv.app G)), hQ, Category.id_comp,
      Iso.hom_inv_id_app_assoc]
  have hterm₂ : ∀ {Z : obj T₂} (w : (L g).obj ((L f).obj (top T₀)) ⟶ Z),
      (hterm (g ≫ f) (htop T₀)).from (top T₂) ≫
          (lcomp g f).hom.app (top T₀) ≫ w =
        (hterm g (htop T₁)).from (top T₂) ≫
          (L g).map ((hterm f (htop T₀)).from (top T₁)) ≫ w := by
    intro Z w
    rw [← Category.assoc, ← Category.assoc,
      (hterm g (hterm f (htop T₀))).hom_ext
        ((hterm (g ≫ f) (htop T₀)).from (top T₂) ≫
          (lcomp g f).hom.app (top T₀))
        ((hterm g (htop T₁)).from (top T₂) ≫
          (L g).map ((hterm f (htop T₀)).from (top T₁)))]
  have hnat : ∀ {Z : obj T₂} (w : (L g).obj ((L f).obj ((L y).obj G)) ⟶ Z),
      (L (g ≫ f)).map s ≫ (lcomp g f).hom.app ((L y).obj G) ≫ w =
        (lcomp g f).hom.app (top T₀) ≫ (L g).map ((L f).map s) ≫ w := by
    intro Z w
    rw [← Category.assoc, ← Category.assoc, (lcomp g f).hom.naturality s]
    rfl
  rw [pullSection, pullSection, pullSection]
  simp only [Functor.map_comp, Category.assoc]
  rw [hpent, hnat, hterm₂]

include htop hterm hidComp hassoc in
/-- **The presheaf of pairs.** For `G` an object of the fibre over `Y`, the presheaf on `C`
sending `T` to the pairs `(y, s)` with `y : T ⟶ Y` and `s` a section of `G` pulled back along
`y`, and restricting along `g : T' ⟶ T` by `(y, s) ↦ (g ≫ y, (L g) s)`. -/
noncomputable def sectionsPresheaf {Y : C} (G : obj Y) : Cᵒᵖ ⥤ Type (max v v') where
  obj T := Σ y : T.unop ⟶ Y, fibreSections obj L top G y
  map {_ _} g := TypeCat.ofHom
    fun p => ⟨g.unop ≫ p.1, pullSection obj L top htop hterm lcomp G g.unop p.1 p.2⟩
  map_id T := by
    refine TypeCat.homEquiv.injective (funext fun p => ?_)
    exact Eq.trans
      (congrArg (Sigma.mk (β := fun z : T.unop ⟶ Y => fibreSections obj L top G z) (𝟙 T.unop ≫ p.1))
        (pullSection_id obj L top htop hterm lid lcomp hidComp G p.1 p.2))
      (sigma_transport obj L top G (Category.id_comp p.1).symm p.2)
  map_comp a b := by
    refine TypeCat.homEquiv.injective (funext fun p => ?_)
    exact Eq.trans (sigma_transport obj L top G (Category.assoc b.unop a.unop p.1)
        (pullSection obj L top htop hterm lcomp G (b.unop ≫ a.unop) p.1 p.2)).symm
      (congrArg
        (Sigma.mk (β := fun z : _ ⟶ Y => fibreSections obj L top G z) (b.unop ≫ a.unop ≫ p.1))
        (pullSection_comp obj L top htop hterm lcomp hassoc G b.unop a.unop p.1 p.2))

end Coherences

end CategoryTheory.LocallyDiscrete

end
