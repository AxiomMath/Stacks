module

public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
public import Mathlib.Tactic.CategoryTheory.Slice

/-!
# Functors out of the CoGrothendieck construction

Mathlib constructs functors out of the (covariant, `1`-functorial) Grothendieck construction
from fibrewise data with `CategoryTheory.Grothendieck.functorFrom`.  This file supplies the
analogue for the contravariant pseudofunctorial construction
`CategoryTheory.Pseudofunctor.CoGrothendieck`, which Mathlib equips only with `forget`, `map`,
`mapIdIso`, `mapCompIso` and the fibre inclusion `ι`.

For `F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat`, an object of `∫ᶜ F` is a pair `(S, a)` with
`a : F(S)`, and a morphism `(R, b) ⟶ (S, a)` is a pair `(f, h)` with `f : R ⟶ S` and
`h : b ⟶ F(f)(a)`.  So a functor `∫ᶜ F ⥤ E` is determined by a functor `fib S : F(S) ⥤ E`
in every fibre together with, for every `f : R ⟶ S`, a natural transformation
`F(f) ⋙ fib R ⟶ fib S`, subject to a unit and a cocycle law written with the pseudofunctor's
own comparison isomorphisms `F.mapId` and `F.mapComp`.

## Main definitions

* `CategoryTheory.Pseudofunctor.CoGrothendieck.functorFrom`: the functor `∫ᶜ F ⥤ E` built from
  such a family.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.ιCompFunctorFrom`: its restriction along the
  fibre inclusion `ι F S` is the given `fib S`.

## Implementation notes

Unlike the `1`-functorial `Grothendieck.functorFrom`, where the coherence hypotheses are
`eqToHom` equations because `F.map (𝟙 c) = 𝟙 _` and `F.map (f ≫ g) = F.map f ⋙ F.map g` hold
on the nose, the hypotheses here are stated with `F.mapId` and `F.mapComp`; no `eqToHom`
appears.  The two `backward.isDefEq.respectTransparency` options are set exactly as in
Mathlib's `Grothendieck.functorFrom` and `CoGrothendieck.map`: the composition law of `∫ᶜ F`
identifies `F.map ((f ≫ g).base.op.toLoc)` with `F.map (g.base.op.toLoc ≫ f.base.op.toLoc)`
only up to unfolding, so rewriting inside a composite needs the laxer transparency.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pseudofunctor Opposite
open scoped CategoryTheory.Bicategory

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat.{v₂, u₂}}
  {E : Type u₃} [Category.{v₃} E]

variable (fib : ∀ S : 𝒮, F.obj ⟨op S⟩ ⥤ E)
  (hom : ∀ {R S : 𝒮} (f : R ⟶ S), (F.map f.op.toLoc).toFunctor ⋙ fib R ⟶ fib S)
  (hom_id : ∀ S : 𝒮, hom (𝟙 S) = Functor.whiskerRight (F.mapId ⟨op S⟩).hom.toNatTrans (fib S))
  (hom_comp : ∀ {R S T : 𝒮} (f : R ⟶ S) (g : S ⟶ T), hom (f ≫ g) =
    Functor.whiskerRight (F.mapComp g.op.toLoc f.op.toLoc).hom.toNatTrans (fib R) ≫
      Functor.whiskerLeft (F.map g.op.toLoc).toFunctor (hom f) ≫ hom g)

/-- Construct a functor from `∫ᶜ F` to another category `E` out of a family of functors on the
fibres of `∫ᶜ F`, a family of natural transformations indexed by the morphisms of the base, and
the unit and cocycle coherences for that family.  This is the contravariant pseudofunctorial
analogue of `CategoryTheory.Grothendieck.functorFrom`. -/
@[simps]
public def functorFrom : CoGrothendieck F ⥤ E where
  obj X := (fib X.base).obj X.fiber
  map {X _} f := (fib X.base).map f.fiber ≫ (hom f.base).app _
  map_id X := by
    dsimp
    rw [hom_id]
    simp [← Functor.map_comp]
  map_comp {X Y Z} f g := by
    have hnat : (fib X.base).map ((F.map f.base.op.toLoc).toFunctor.map g.fiber) ≫
        (hom f.base).app ((F.map g.base.op.toLoc).toFunctor.obj Z.fiber) =
        (hom f.base).app Y.fiber ≫ (fib Y.base).map g.fiber :=
      (hom f.base).naturality g.fiber
    simp only [CoGrothendieck.categoryStruct_comp_base, op_comp, Quiver.Hom.comp_toLoc,
      CoGrothendieck.categoryStruct_comp_fiber, hom_comp, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc,
      Cat.Hom.comp_toFunctor, Functor.comp_obj]
    slice_lhs 3 4 => rw [← Functor.map_comp, Cat.Hom.inv_hom_id_toNatTrans_app]
                     simp only [Cat.Hom.comp_toFunctor, Functor.comp_obj, Functor.map_id]
    simp only [Category.id_comp]
    rw [reassoc_of% hnat]

/-- The fibre inclusion `ι F S` composed with `functorFrom` is the functor `fib S` the
construction was given on that fibre. -/
public def ιCompFunctorFrom (S : 𝒮) :
    CoGrothendieck.ι F S ⋙ functorFrom fib hom hom_id hom_comp ≅ fib S :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {X Y} φ => by
    have h : ((fib S).map (φ ≫ (F.mapId ⟨op S⟩).inv.toNatTrans.app Y) ≫ (hom (𝟙 S)).app Y) ≫
        𝟙 ((fib S).obj Y) = 𝟙 ((fib S).obj X) ≫ (fib S).map φ := by
      rw [hom_id]
      simp [← Functor.map_comp]
    exact h)

end CategoryTheory.Pseudofunctor.CoGrothendieck

end
