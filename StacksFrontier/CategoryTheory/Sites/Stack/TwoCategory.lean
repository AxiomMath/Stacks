module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import StacksFrontier.CategoryTheory.FibredOneMorphism
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack
import StacksCore.Tactic.StacksAttribute

/-!
# The 2-category of stacks over a site

Let `(𝒞, J)` be a site. The *2-category of stacks over `𝒞`* has as objects the stacks
`p : 𝒮 ⥤ 𝒞`, as 1-morphisms the functors `G : 𝒮 ⥤ 𝒮'` with `p' ∘ G = p` which carry strongly
cartesian morphisms to strongly cartesian morphisms, and as 2-morphisms the morphisms of functors
`t` with `p'(t_x) = 𝟙 (p x)` for every object `x`.

## Main definitions

* `CategoryTheory.BasedStack`, an object of the 2-category: a category over `𝒞` whose structure
  functor is a stack.
* `CategoryTheory.BasedStack.Hom`, a 1-morphism.
* `CategoryTheory.BasedStack.homCategory`, the category of 1-morphisms, whose morphisms are the
  2-morphisms.
* `CategoryTheory.BasedStack.bicategory`, the 2-category itself.

## Implementation notes

The ambient 2-category of categories over `𝒞` is Mathlib's `CategoryTheory.BasedCategory 𝒞`, whose
1-morphisms are the `BasedFunctor`s (a functor together with the *equality* `G ⋙ p' = p`) and whose
2-morphisms are the `BasedNatTrans` (a morphism of functors each of whose components lies over an
identity). The sub-2-category constructed here restricts the objects to the stacks *and* the
1-morphisms to those preserving strongly cartesian morphisms, so it is not full and Mathlib's
`CategoryTheory.Bicategory.InducedBicategory` — which takes all 1-morphisms of the ambient
bicategory, and is what `CategoryTheory.StackInSetoids` uses for Stacks 0433 — does not apply. The
restriction on 1-morphisms is the repo's `CategoryTheory.Functor.IsFibredOneMorphism`, item (2) of
Stacks 4.33.9; Mathlib has no predicate for a based functor preserving cartesian morphisms.

Because `BasedFunctor.comp` is strictly associative and strictly unital, and the extra field of a
1-morphism is a `Prop`, composition of 1-morphisms here is strictly associative and unital too: the
associator and the unitors are `Iso.refl`, and `Bicategory.Strict` holds.

"Stack over the site `(𝒞, J)`" is `CategoryTheory.Functor.IsStack`, the rendering of Stacks 026F as
a condition on the structure functor `p : 𝒮 ⥤ 𝒞`. Mathlib's `CategoryTheory.Pseudofunctor.IsStack`
carries the same tag 026F but states the condition for a pseudofunctor
`LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat`; the pinned Mathlib has no bridge between the two presentations, and
the 1-morphisms and 2-morphisms of the 2-category below are given in the fibred presentation, so
that is the presentation used here. Note the warning on `Functor.IsStack`: its descent-of-morphisms
condition is weaker than the source's, and the definitions below inherit that weakening.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

/-- **Stacks 02ZG (1)**.
An object of the 2-category of stacks over the site `(𝒞, J)`: a category over `𝒞` whose structure
functor is a stack. -/
@[stacks_fixed 02ZG "(1)"]
structure BasedStack (𝒞 : Type u₁) [Category.{v₁} 𝒞] (J : GrothendieckTopology 𝒞) where
  /-- The underlying category over `𝒞`. -/
  toBasedCategory : BasedCategory.{v₂, u₂} 𝒞
  /-- Its structure functor is a stack over `(𝒞, J)`. -/
  isStack : toBasedCategory.p.IsStack J

variable {J : GrothendieckTopology 𝒞}

namespace BasedStack

/-- **Stacks 02ZG (2)**.
A 1-morphism of stacks over `𝒞`: a functor `G` between the underlying categories with
`p' ∘ G = p`, which carries strongly cartesian morphisms to strongly cartesian morphisms. The
first condition is the field `w` of a `BasedFunctor` and is repeated as `comp_eq` inside
`Functor.IsFibredOneMorphism`. -/
@[stacks_fixed 02ZG "(2)"]
structure Hom (𝒳 𝒴 : BasedStack.{v₁, v₂, u₁, u₂} 𝒞 J) where
  /-- The underlying functor over `𝒞`. -/
  hom : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory
  /-- It preserves strongly cartesian morphisms. -/
  isFibredOneMorphism :
    Functor.IsFibredOneMorphism 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p hom.toFunctor

attribute [ext] Hom

/-- Identities and composition of 1-morphisms, computed on the underlying functors over `𝒞`. -/
instance categoryStruct : CategoryStruct (BasedStack.{v₁, v₂, u₁, u₂} 𝒞 J) where
  Hom := Hom
  id _ := ⟨BasedFunctor.id _, Functor.IsFibredOneMorphism.id _⟩
  comp f g := ⟨BasedFunctor.comp f.hom g.hom, f.isFibredOneMorphism.comp g.isFibredOneMorphism⟩

/-- The underlying functor over `𝒞` of the identity 1-morphism of a stack is the identity. -/
@[simp]
lemma id_hom (𝒳 : BasedStack.{v₁, v₂, u₁, u₂} 𝒞 J) : (𝟙 𝒳 : 𝒳 ⟶ 𝒳).hom = BasedFunctor.id _ := rfl

/-- The underlying functor over `𝒞` of a composite of 1-morphisms of stacks is the composite of the
underlying functors. -/
@[simp]
lemma comp_hom {𝒳 𝒴 𝒵 : BasedStack.{v₁, v₂, u₁, u₂} 𝒞 J} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) :
    (f ≫ g).hom = BasedFunctor.comp f.hom g.hom := rfl

/-- **Stacks 02ZG (3)**.
The 2-morphisms between two 1-morphisms of stacks: the morphisms of functors `t` with
`p'(t_x) = 𝟙 (p x)` for every object `x`, that is the `BasedNatTrans` between the underlying
functors over `𝒞`. Nothing is imposed on a 2-morphism beyond that, so this category of
1-morphisms is the one of the ambient 2-category `BasedCategory 𝒞`. -/
@[stacks 02ZG "(3)"]
instance homCategory (𝒳 𝒴 : BasedStack.{v₁, v₂, u₁, u₂} 𝒞 J) : Category (𝒳 ⟶ 𝒴) where
  Hom f g := f.hom ⟶ g.hom
  id f := 𝟙 f.hom
  comp α β := α ≫ β

variable {𝒳 𝒴 𝒵 𝒲 : BasedStack.{v₁, v₂, u₁, u₂} 𝒞 J}

/-- Left whiskering, computed in the ambient 2-category of categories over `𝒞`. -/
def whiskerLeft (f : 𝒳 ⟶ 𝒴) {g h : 𝒴 ⟶ 𝒵} (η : g ⟶ h) : f ≫ g ⟶ f ≫ h :=
  BasedCategory.whiskerLeft f.hom η

/-- Right whiskering, computed in the ambient 2-category of categories over `𝒞`. -/
def whiskerRight {f g : 𝒳 ⟶ 𝒴} (η : f ⟶ g) (h : 𝒴 ⟶ 𝒵) : f ≫ h ⟶ g ≫ h :=
  BasedCategory.whiskerRight η h.hom

/-! ### The bicategory axioms

Each of these is the corresponding axiom of `BasedCategory.bicategory`, whose associator and
unitors are identity 2-morphisms; they are stated separately rather than inline in the instance
below because inside a structure instance the whiskering fields are still metavariables when the
axiom fields are elaborated. -/

section Axioms

/-- Whiskering an identity 2-morphism on the left is an identity. -/
lemma whiskerLeft_id (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) : whiskerLeft f (𝟙 g) = 𝟙 (f ≫ g) :=
  Bicategory.whiskerLeft_id (B := BasedCategory.{v₂, u₂} 𝒞) f.hom g.hom

/-- Left whiskering is functorial in the 2-morphism: it takes a vertical composite to the vertical
composite of the whiskerings. -/
lemma whiskerLeft_comp (f : 𝒳 ⟶ 𝒴) {g h i : 𝒴 ⟶ 𝒵} (η : g ⟶ h) (θ : h ⟶ i) :
    whiskerLeft f (η ≫ θ) = whiskerLeft f η ≫ whiskerLeft f θ :=
  Bicategory.whiskerLeft_comp (B := BasedCategory.{v₂, u₂} 𝒞) f.hom η θ

/-- Whiskering on the left by an identity 1-morphism is `η` itself, transported along the left
unitors, which here are identity 2-morphisms. -/
lemma id_whiskerLeft {f g : 𝒳 ⟶ 𝒴} (η : f ⟶ g) :
    whiskerLeft (𝟙 𝒳) η = (Iso.refl (𝟙 𝒳 ≫ f)).hom ≫ η ≫ (Iso.refl (𝟙 𝒳 ≫ g)).inv :=
  Bicategory.id_whiskerLeft (B := BasedCategory.{v₂, u₂} 𝒞) η

/-- Whiskering on the left by a composite 1-morphism is whiskering by each factor in turn,
transported along the associators, which here are identity 2-morphisms. -/
lemma comp_whiskerLeft (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) {h h' : 𝒵 ⟶ 𝒲} (η : h ⟶ h') :
    whiskerLeft (f ≫ g) η =
      (Iso.refl ((f ≫ g) ≫ h)).hom ≫ whiskerLeft f (whiskerLeft g η) ≫
        (Iso.refl ((f ≫ g) ≫ h')).inv :=
  Bicategory.comp_whiskerLeft (B := BasedCategory.{v₂, u₂} 𝒞) f.hom g.hom η

/-- Whiskering an identity 2-morphism on the right is an identity. -/
lemma id_whiskerRight (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) : whiskerRight (𝟙 f) g = 𝟙 (f ≫ g) :=
  Bicategory.id_whiskerRight (B := BasedCategory.{v₂, u₂} 𝒞) f.hom g.hom

/-- Right whiskering is functorial in the 2-morphism: it takes a vertical composite to the vertical
composite of the whiskerings. -/
lemma comp_whiskerRight {f g h : 𝒳 ⟶ 𝒴} (η : f ⟶ g) (θ : g ⟶ h) (i : 𝒴 ⟶ 𝒵) :
    whiskerRight (η ≫ θ) i = whiskerRight η i ≫ whiskerRight θ i :=
  Bicategory.comp_whiskerRight (B := BasedCategory.{v₂, u₂} 𝒞) η θ i.hom

/-- Whiskering on the right by an identity 1-morphism is `η` itself, transported along the right
unitors, which here are identity 2-morphisms. -/
lemma whiskerRight_id {f g : 𝒳 ⟶ 𝒴} (η : f ⟶ g) :
    whiskerRight η (𝟙 𝒴) = (Iso.refl (f ≫ 𝟙 𝒴)).hom ≫ η ≫ (Iso.refl (g ≫ 𝟙 𝒴)).inv :=
  Bicategory.whiskerRight_id (B := BasedCategory.{v₂, u₂} 𝒞) η

/-- Whiskering on the right by a composite 1-morphism is whiskering by each factor in turn,
transported along the associators, which here are identity 2-morphisms. -/
lemma whiskerRight_comp {f f' : 𝒳 ⟶ 𝒴} (η : f ⟶ f') (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒲) :
    whiskerRight η (g ≫ h) =
      (Iso.refl ((f ≫ g) ≫ h)).inv ≫ whiskerRight (whiskerRight η g) h ≫
        (Iso.refl ((f' ≫ g) ≫ h)).hom :=
  Bicategory.whiskerRight_comp (B := BasedCategory.{v₂, u₂} 𝒞) η g.hom h.hom

/-- Left and right whiskering of a single 2-morphism by 1-morphisms on either side commute, up to
the associators, which here are identity 2-morphisms. -/
lemma whisker_assoc (f : 𝒳 ⟶ 𝒴) {g g' : 𝒴 ⟶ 𝒵} (η : g ⟶ g') (h : 𝒵 ⟶ 𝒲) :
    whiskerRight (whiskerLeft f η) h =
      (Iso.refl ((f ≫ g) ≫ h)).hom ≫ whiskerLeft f (whiskerRight η h) ≫
        (Iso.refl ((f ≫ g') ≫ h)).inv :=
  Bicategory.whisker_assoc (B := BasedCategory.{v₂, u₂} 𝒞) f.hom η h.hom

/-- The interchange law: whiskering two 2-morphisms into each other's sources and targets gives the
same horizontal composite whichever order the two whiskerings are performed in. -/
lemma whisker_exchange {f g : 𝒳 ⟶ 𝒴} {h i : 𝒴 ⟶ 𝒵} (η : f ⟶ g) (θ : h ⟶ i) :
    whiskerLeft f θ ≫ whiskerRight η i = whiskerRight η h ≫ whiskerLeft g θ :=
  Bicategory.whisker_exchange (B := BasedCategory.{v₂, u₂} 𝒞) η θ

end Axioms

/-- **Stacks 02ZG**.
The 2-category of stacks over the site `(𝒞, J)`: the sub-2-category of the 2-category of fibred
categories over `𝒞` (Stacks 02XP) whose objects are the stacks over `𝒞`, whose 1-morphisms are the
functors over `𝒞` preserving strongly cartesian morphisms, and whose 2-morphisms are the morphisms
of functors whose components lie over identities. -/
@[stacks 02ZG]
instance bicategory : Bicategory (BasedStack.{v₁, v₂, u₁, u₂} 𝒞 J) where
  whiskerLeft {_ _ _} f {_ _} η := whiskerLeft f η
  whiskerRight {_ _ _} {_ _} η h := whiskerRight η h
  associator _ _ _ := Iso.refl _
  leftUnitor _ := Iso.refl _
  rightUnitor _ := Iso.refl _
  whiskerLeft_id := whiskerLeft_id
  whiskerLeft_comp := whiskerLeft_comp
  id_whiskerLeft := id_whiskerLeft
  comp_whiskerLeft := comp_whiskerLeft
  id_whiskerRight := id_whiskerRight
  comp_whiskerRight := comp_whiskerRight
  whiskerRight_id := whiskerRight_id
  whiskerRight_comp := whiskerRight_comp
  whisker_assoc := whisker_assoc
  whisker_exchange := whisker_exchange
  pentagon f g h i := by
    exact Bicategory.pentagon (B := BasedCategory.{v₂, u₂} 𝒞) f.hom g.hom h.hom i.hom
  triangle f g := by
    exact Bicategory.triangle (B := BasedCategory.{v₂, u₂} 𝒞) f.hom g.hom

/-- Composition of 1-morphisms is strictly associative and strictly unital, as it is in the ambient
2-category of categories over `𝒞`. -/
instance : Bicategory.Strict (BasedStack.{v₁, v₂, u₁, u₂} 𝒞 J) where
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
  leftUnitor_eqToIso _ := rfl
  rightUnitor_eqToIso _ := rfl
  associator_eqToIso _ _ _ := rfl

/-- The 1-morphisms of the 2-category of stacks over `𝒞` are exactly the functors over `𝒞`
preserving strongly cartesian morphisms: a 1-morphism `𝒳 ⟶ 𝒴` is a `BasedFunctor` `G`, that is a
functor with `p' ∘ G = p`, together with a proof that `G` carries strongly cartesian morphisms to
strongly cartesian morphisms. -/
def homEquivBasedFunctor (𝒳 𝒴 : BasedStack.{v₁, v₂, u₁, u₂} 𝒞 J) :
    (𝒳 ⟶ 𝒴) ≃ { G : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory //
      Functor.IsFibredOneMorphism 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p G.toFunctor } where
  toFun f := ⟨f.hom, f.isFibredOneMorphism⟩
  invFun G := ⟨G.1, G.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The 2-morphisms of the 2-category of stacks over `𝒞` are the morphisms of functors whose
components lie over identities: a 2-morphism `f ⟶ g` is the same thing as a `BasedNatTrans`
between the underlying functors, that is a morphism of functors `t` with `p'(t_x) = 𝟙 (p x)`. -/
def twoHomEquivBasedNatTrans (f g : 𝒳 ⟶ 𝒴) : (f ⟶ g) ≃ BasedNatTrans f.hom g.hom where
  toFun η := η
  invFun t := t
  left_inv _ := rfl
  right_inv _ := rfl

end BasedStack

end CategoryTheory
