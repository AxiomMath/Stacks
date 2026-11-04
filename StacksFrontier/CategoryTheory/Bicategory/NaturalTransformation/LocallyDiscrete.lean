module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# Strong transformations out of a locally discrete bicategory

Mathlib's `CategoryTheory.pseudofunctorOfIsLocallyDiscrete` builds a pseudofunctor out of a
locally discrete bicategory without asking for the field `map₂`, because every `2`-morphism of
the source is an identity. This file does the same for *strong transformations*: out of a locally
discrete bicategory the axiom
`CategoryTheory.Pseudofunctor.StrongTrans.naturality_naturality` is automatic, so only the two
remaining coherences have to be supplied.

For a target bicategory `Cat` there is a second simplification. The two remaining coherences are
equations between `2`-morphisms, i.e. between natural transformations, and `Cat` is strict, so its
associators and unitors are identities on components. Evaluating at an object therefore turns each
coherence into a plain equation in a category, and
`CategoryTheory.Pseudofunctor.catStrongTransOfIsLocallyDiscrete` asks for exactly those.

## Main definitions

* `CategoryTheory.Pseudofunctor.strongTransOfIsLocallyDiscrete`: a strong transformation out of a
  locally discrete bicategory, from the two coherences that are not automatic.
* `CategoryTheory.Pseudofunctor.catStrongTransOfIsLocallyDiscrete`: **a strong transformation
  between pseudofunctors to `Cat` out of a locally discrete bicategory, from the two coherences
  stated componentwise**, as equations between morphisms of the target categories.

## Implementation notes

**Why the componentwise form is worth having.** A caller of the first constructor must still
discharge equations of `2`-morphisms in `Cat`, whose sides mention whiskerings, associators and
unitors, and whose objects are spelled through the composition of `Cat` — `(F.map f ≫ app b)`
rather than the applied `(app b).obj ((F.map f).obj X)`. When the categories involved are
semireducible definitions (a fibre of a fibred category, say) those two spellings of one object are
not interchangeable at the transparency the tactic framework uses to check a motive, and a caller
is pushed into transparency options. The second constructor pays that cost once, here, where `F`
and `G` are arbitrary pseudofunctors and no definition is unfolded, and hands the caller goals in
which every object is already applied.

No Stacks tag is claimed: this is bicategorical bookkeeping with no counterpart in the source.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Pseudofunctor

open Bicategory

universe v u

/-- **The component of the `2`-isomorphism of `Cat` attached to a natural isomorphism.**

`CategoryTheory.Cat.Hom.isoMk_hom` followed by `CategoryTheory.NatTrans.toCatHom₂_toNatTrans`
says this, but neither fires inside the goals
`CategoryTheory.Pseudofunctor.catStrongTransOfIsLocallyDiscrete` hands a caller, in which a
pseudofunctor's `mapId` and `mapComp` are `CategoryTheory.Cat.Hom.isoMk`s; the obstruction is the
`Category` instance path, not the statement.  Keyed on the applied component instead it does
fire, and a caller's goal becomes an equation between morphisms of the categories themselves. -/
@[simp]
lemma _root_.CategoryTheory.Cat.Hom.isoMk_hom_toNatTrans_app {C D : Type u} [Category.{v} C]
    [Category.{v} D] {F G : C ⥤ D} (e : F ≅ G) (X : C) :
    (Cat.Hom.isoMk e).hom.toNatTrans.app X = e.hom.app X :=
  rfl

variable {B : Type*} [Bicategory B] [IsLocallyDiscrete B] {C : Type*} [Bicategory C]

/-- **A strong transformation out of a locally discrete bicategory.** Since every `2`-morphism of
the source is an identity, the axiom
`CategoryTheory.Pseudofunctor.StrongTrans.naturality_naturality` is automatic, and only the unity
and functoriality coherences have to be given. -/
def strongTransOfIsLocallyDiscrete (F G : Pseudofunctor B C)
    (app : ∀ a, F.obj a ⟶ G.obj a)
    (naturality : ∀ {a b : B} (f : a ⟶ b), F.map f ≫ app b ≅ app a ≫ G.map f)
    (naturality_id : ∀ a : B,
      (naturality (𝟙 a)).hom ≫ app a ◁ (G.mapId a).hom =
        (F.mapId a).hom ▷ app a ≫ (λ_ (app a)).hom ≫ (ρ_ (app a)).inv)
    (naturality_comp : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c),
      (naturality (f ≫ g)).hom ≫ app a ◁ (G.mapComp f g).hom =
        (F.mapComp f g).hom ▷ app c ≫ (α_ _ _ _).hom ≫ F.map f ◁ (naturality g).hom ≫
        (α_ _ _ _).inv ≫ (naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom) :
    F.StrongTrans G where
  app := app
  naturality := naturality
  naturality_naturality := by
    intro a b f g η
    obtain rfl := obj_ext_of_isDiscrete η
    obtain rfl : η = 𝟙 f := Subsingleton.elim _ _
    simp
  naturality_id := naturality_id
  naturality_comp := naturality_comp

/-- **A strong transformation between pseudofunctors to `Cat` out of a locally discrete
bicategory, from its two coherences stated componentwise.** The component of the transformation
at an object is a functor, the strong naturality constraint is an isomorphism of functors, and the
two coherences are the equations those satisfy at every object — `Cat` being strict, its
associators and unitors contribute nothing to them. -/
def catStrongTransOfIsLocallyDiscrete (F G : Pseudofunctor B Cat.{v, u})
    (app : ∀ a : B, (F.obj a : Type u) ⥤ G.obj a)
    (nat : ∀ {a b : B} (f : a ⟶ b),
      (F.map f).toFunctor ⋙ app b ≅ app a ⋙ (G.map f).toFunctor)
    (nat_id : ∀ (a : B) (X : F.obj a),
      (nat (𝟙 a)).hom.app X ≫ (G.mapId a).hom.toNatTrans.app ((app a).obj X) =
        (app a).map ((F.mapId a).hom.toNatTrans.app X))
    (nat_comp : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (X : F.obj a),
      (nat (f ≫ g)).hom.app X ≫ (G.mapComp f g).hom.toNatTrans.app ((app a).obj X) =
        (app c).map ((F.mapComp f g).hom.toNatTrans.app X) ≫
          (nat g).hom.app ((F.map f).toFunctor.obj X) ≫
            (G.map g).toFunctor.map ((nat f).hom.app X)) :
    F.StrongTrans G :=
  strongTransOfIsLocallyDiscrete F G (fun a => Cat.Hom.ofFunctor (app a))
    (fun {_ _} f => Cat.Hom.isoMk (nat f))
    (by
      intro a
      ext X
      simpa [Cat.whiskerLeft_app, Cat.whiskerRight_app, Cat.leftUnitor_hom_app,
        Cat.rightUnitor_inv_app] using nat_id a X)
    (by
      intro a b c f g
      ext X
      simpa [Cat.whiskerLeft_app, Cat.whiskerRight_app, Cat.associator_hom_app,
        Cat.associator_inv_app] using nat_comp f g X)

end CategoryTheory.Pseudofunctor

end
