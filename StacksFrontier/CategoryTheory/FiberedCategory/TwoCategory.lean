module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The 2-category of fibred categories over a base

Let `𝒮` be a category. The *2-category of fibred categories over `𝒮`* (Stacks 02XP) is the
sub-2-category of the 2-category of categories over `𝒮` (Stacks 003Y) whose objects are the
fibred categories, whose 1-morphisms are the functors over `𝒮` that carry strongly cartesian
morphisms to strongly cartesian morphisms, and whose 2-morphisms are all the 2-morphisms of the
ambient 2-category.

## Main definitions

* `CategoryTheory.BasedFunctor.PreservesStronglyCartesian`: the condition imposed on the
  1-morphisms;
* `CategoryTheory.CatFibered`: the 2-category of fibred categories over `𝒮` (Stacks 02XP). Its
  hom-categories are the categories `Mor_{Fib/𝒮}(𝒳, 𝒴)` of the source.

## Main results

* `CategoryTheory.CatFibered.isFibered`, `CategoryTheory.CatFibered.homFunctor_comp_p` together
  with `CategoryTheory.CatFibered.Hom.preservesStronglyCartesian`, and
  `CategoryTheory.CatFibered.homEquivBasedNatTrans` with
  `CategoryTheory.CatFibered.isHomLift_app`: the three clauses of the source, spelled out.

## Implementation notes

This is not a full sub-2-category of `CategoryTheory.BasedCategory 𝒮`, so
`CategoryTheory.Bicategory.InducedBicategory` does not apply. The bicategory structure is built
directly: 1-morphisms are based functors preserving strongly cartesian morphisms, and the
2-morphisms and all of the structural data (whiskerings, associator, unitors) are those of
`BasedCategory 𝒮`. The resulting bicategory is strict.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory

universe v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

namespace BasedFunctor

variable {𝒳 𝒴 𝒵 : BasedCategory.{v₂, u₂} 𝒮}

/-- A based functor `G : 𝒳 ⥤ᵇ 𝒴` *preserves strongly cartesian morphisms* if it carries every
strongly cartesian morphism of `𝒳` over a morphism `f` of the base to a strongly cartesian
morphism of `𝒴` over `f`. -/
def PreservesStronglyCartesian (G : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  ∀ ⦃R S : 𝒮⦄ ⦃a b : 𝒳.obj⦄ (f : R ⟶ S) (φ : a ⟶ b),
    𝒳.p.IsStronglyCartesian f φ → 𝒴.p.IsStronglyCartesian f (G.map φ)

/-- The identity based functor preserves strongly cartesian morphisms. -/
lemma preservesStronglyCartesian_id : (BasedFunctor.id 𝒳).PreservesStronglyCartesian :=
  fun _ _ _ _ _ _ h ↦ h

/-- A composition of based functors preserving strongly cartesian morphisms preserves strongly
cartesian morphisms. -/
@[sga "1 VI 5.3" "(iii)"]
lemma PreservesStronglyCartesian.comp {G : 𝒳 ⥤ᵇ 𝒴} {H : 𝒴 ⥤ᵇ 𝒵}
    (hG : G.PreservesStronglyCartesian) (hH : H.PreservesStronglyCartesian) :
    (BasedFunctor.comp G H).PreservesStronglyCartesian :=
  fun _ _ _ _ f φ h ↦ hH f _ (hG f φ h)

end BasedFunctor

/-- The 2-category of fibred categories over `𝒮`: the sub-2-category of the 2-category
`BasedCategory 𝒮` of categories over `𝒮` (Stacks 003Y) whose

1. objects are the categories `p : 𝒳 ⥤ 𝒮` over `𝒮` that are fibred categories;
2. 1-morphisms `(𝒳, p) ⟶ (𝒴, p')` are the functors `G : 𝒳 ⥤ 𝒴` with `p' ∘ G = p` carrying
   strongly cartesian morphisms to strongly cartesian morphisms;
3. 2-morphisms `t : G ⟶ H` are the morphisms of functors with `p'(t_x) = 𝟙 (p x)` for every
   object `x` of `𝒳`.

The hom-category `𝒳 ⟶ 𝒴` is the source's `Mor_{Fib/𝒮}(𝒳, 𝒴)`. -/
@[stacks 02XP]
def CatFibered (𝒮 : Type u₁) [Category.{v₁} 𝒮] :=
  {𝒳 : BasedCategory.{v₂, u₂} 𝒮 // 𝒳.p.IsFibered}

namespace CatFibered

/-- A category over `𝒮` whose structure functor is a fibred category, viewed as an object of the
2-category of fibred categories over `𝒮`. -/
abbrev mk (𝒳 : BasedCategory.{v₂, u₂} 𝒮) (h : 𝒳.p.IsFibered) : CatFibered.{v₁, v₂, u₁, u₂} 𝒮 :=
  ⟨𝒳, h⟩

/-- The category over `𝒮` underlying an object of the 2-category of fibred categories over `𝒮`. -/
abbrev val (𝒳 : CatFibered.{v₁, v₂, u₁, u₂} 𝒮) : BasedCategory.{v₂, u₂} 𝒮 := 𝒳.1

/-- The structure functor of an object of the 2-category of fibred categories over `𝒮` is a
fibred category. -/
instance isFibered (𝒳 : CatFibered.{v₁, v₂, u₁, u₂} 𝒮) : 𝒳.val.p.IsFibered := 𝒳.2

/-- A 1-morphism of the 2-category of fibred categories over `𝒮`: a functor over `𝒮` preserving
strongly cartesian morphisms. -/
@[ext]
structure Hom (𝒳 𝒴 : CatFibered.{v₁, v₂, u₁, u₂} 𝒮) where
  /-- The underlying functor over `𝒮`. -/
  hom : 𝒳.val ⥤ᵇ 𝒴.val
  /-- The underlying functor preserves strongly cartesian morphisms. -/
  preservesStronglyCartesian : hom.PreservesStronglyCartesian

/-- Composition of 1-morphisms is composition of the underlying functors over `𝒮`, and the
identity 1-morphism is the identity functor. -/
@[simps id_hom comp_hom]
instance categoryStruct : CategoryStruct (CatFibered.{v₁, v₂, u₁, u₂} 𝒮) where
  Hom 𝒳 𝒴 := Hom 𝒳 𝒴
  id 𝒳 := ⟨BasedFunctor.id 𝒳.val, BasedFunctor.preservesStronglyCartesian_id⟩
  comp u v := ⟨BasedFunctor.comp u.hom v.hom, u.2.comp v.2⟩

/-- Extensionality for 1-morphisms: a 1-morphism is determined by its underlying functor over
`𝒮`. -/
@[ext]
lemma Hom.ext' {𝒳 𝒴 : CatFibered.{v₁, v₂, u₁, u₂} 𝒮} {f g : 𝒳 ⟶ 𝒴} (h : f.hom = g.hom) :
    f = g :=
  Hom.ext h

variable {𝒳 𝒴 : CatFibered.{v₁, v₂, u₁, u₂} 𝒮}

/-- A 2-morphism of the 2-category of fibred categories over `𝒮`: a 2-morphism of the 2-category
of categories over `𝒮` between the underlying 1-morphisms, no further condition being imposed. -/
@[ext]
structure Hom₂ (f g : 𝒳 ⟶ 𝒴) where
  /-- The underlying 2-morphism of the 2-category of categories over `𝒮`. -/
  hom : f.hom ⟶ g.hom

/-- The hom-category `Mor_{Fib/𝒮}(𝒳, 𝒴)` of the 2-category of fibred categories over `𝒮`: its
objects are the 1-morphisms and its morphisms are the 2-morphisms, composed as in the 2-category
of categories over `𝒮`. -/
@[simps!]
instance Hom.category (𝒳 𝒴 : CatFibered.{v₁, v₂, u₁, u₂} 𝒮) : Category (𝒳 ⟶ 𝒴) where
  Hom f g := Hom₂ f g
  id f := ⟨𝟙 f.hom⟩
  comp u v := ⟨u.hom ≫ v.hom⟩

/-- Extensionality for 2-morphisms: a 2-morphism is determined by the underlying 2-morphism of
the 2-category of categories over `𝒮`. -/
@[ext]
lemma hom₂_ext {f g : 𝒳 ⟶ 𝒴} {η θ : f ⟶ g} (h : η.hom = θ.hom) : η = θ :=
  Hom₂.ext h

/-- Constructor for 2-isomorphisms of the 2-category of fibred categories over `𝒮`. -/
@[simps!]
def isoMk {f g : 𝒳 ⟶ 𝒴} (φ : f.hom ≅ g.hom) : f ≅ g where
  hom := ⟨φ.hom⟩
  inv := ⟨φ.inv⟩
  hom_inv_id := hom₂_ext φ.hom_inv_id
  inv_hom_id := hom₂_ext φ.inv_hom_id

section Whiskering

variable {𝒵 : CatFibered.{v₁, v₂, u₁, u₂} 𝒮}

/-- Left whiskering in the 2-category of fibred categories over `𝒮`, taken over from the
2-category of categories over `𝒮`. -/
def whiskerLeft (F : 𝒳 ⟶ 𝒴) {G H : 𝒴 ⟶ 𝒵} (η : G ⟶ H) : F ≫ G ⟶ F ≫ H :=
  Hom₂.mk (BasedCategory.whiskerLeft F.hom η.hom)

/-- The 2-morphism of the 2-category of categories over `𝒮` underlying a left whiskering. -/
@[simp]
lemma whiskerLeft_hom (F : 𝒳 ⟶ 𝒴) {G H : 𝒴 ⟶ 𝒵} (η : G ⟶ H) :
    (whiskerLeft F η).hom = BasedCategory.whiskerLeft F.hom η.hom :=
  rfl

/-- Right whiskering in the 2-category of fibred categories over `𝒮`, taken over from the
2-category of categories over `𝒮`. -/
def whiskerRight {F G : 𝒳 ⟶ 𝒴} (η : F ⟶ G) (H : 𝒴 ⟶ 𝒵) : F ≫ H ⟶ G ≫ H :=
  Hom₂.mk (BasedCategory.whiskerRight η.hom H.hom)

/-- The 2-morphism of the 2-category of categories over `𝒮` underlying a right whiskering. -/
@[simp]
lemma whiskerRight_hom {F G : 𝒳 ⟶ 𝒴} (η : F ⟶ G) (H : 𝒴 ⟶ 𝒵) :
    (whiskerRight η H).hom = BasedCategory.whiskerRight η.hom H.hom :=
  rfl

end Whiskering

/-- The 2-category of fibred categories over `𝒮` (Stacks 02XP), with all of its structural data
taken over from the 2-category `BasedCategory 𝒮` of categories over `𝒮`. Since the latter is
strict, the associator and the unitors are identities. -/
instance bicategory : Bicategory (CatFibered.{v₁, v₂, u₁, u₂} 𝒮) where
  whiskerLeft := fun {_ _ _} F {_ _} η ↦ CatFibered.whiskerLeft F η
  whiskerRight := fun {_ _ _} {_ _} η H ↦ CatFibered.whiskerRight η H
  associator _ _ _ := isoMk (Iso.refl _)
  leftUnitor _ := isoMk (Iso.refl _)
  rightUnitor _ := isoMk (Iso.refl _)
  whiskerLeft_id := by
    intro a b c F G
    exact hom₂_ext (Bicategory.whiskerLeft_id (B := BasedCategory.{v₂, u₂} 𝒮) F.hom G.hom)
  whiskerLeft_comp := by
    intro a b c F G H I η θ
    exact hom₂_ext (Bicategory.whiskerLeft_comp (B := BasedCategory.{v₂, u₂} 𝒮)
      F.hom (Hom₂.hom η) (Hom₂.hom θ))
  id_whiskerLeft := by
    intro a b F G η
    exact hom₂_ext (Bicategory.id_whiskerLeft (B := BasedCategory.{v₂, u₂} 𝒮) (Hom₂.hom η))
  comp_whiskerLeft := by
    intro a b c d F G H H' η
    exact hom₂_ext (Bicategory.comp_whiskerLeft (B := BasedCategory.{v₂, u₂} 𝒮)
      F.hom G.hom (Hom₂.hom η))
  id_whiskerRight := by
    intro a b c F G
    exact hom₂_ext (Bicategory.id_whiskerRight (B := BasedCategory.{v₂, u₂} 𝒮) F.hom G.hom)
  comp_whiskerRight := by
    intro a b c F G H η θ I
    exact hom₂_ext (Bicategory.comp_whiskerRight (B := BasedCategory.{v₂, u₂} 𝒮)
      (Hom₂.hom η) (Hom₂.hom θ) I.hom)
  whiskerRight_id := by
    intro a b F G η
    exact hom₂_ext (Bicategory.whiskerRight_id (B := BasedCategory.{v₂, u₂} 𝒮) (Hom₂.hom η))
  whiskerRight_comp := by
    intro a b c d F F' η G H
    exact hom₂_ext (Bicategory.whiskerRight_comp (B := BasedCategory.{v₂, u₂} 𝒮)
      (Hom₂.hom η) G.hom H.hom)
  whisker_assoc := by
    intro a b c d F G G' η H
    exact hom₂_ext (Bicategory.whisker_assoc (B := BasedCategory.{v₂, u₂} 𝒮)
      F.hom (Hom₂.hom η) H.hom)
  whisker_exchange := by
    intro a b c F G H I η θ
    exact hom₂_ext (Bicategory.whisker_exchange (B := BasedCategory.{v₂, u₂} 𝒮)
      (Hom₂.hom η) (Hom₂.hom θ))
  pentagon := by
    intro a b c d e F G H I
    exact hom₂_ext (Bicategory.pentagon (B := BasedCategory.{v₂, u₂} 𝒮) F.hom G.hom H.hom I.hom)
  triangle := by
    intro a b c F G
    exact hom₂_ext (Bicategory.triangle (B := BasedCategory.{v₂, u₂} 𝒮) F.hom G.hom)

/-- The 2-category of fibred categories over `𝒮` is strict, as the 2-category of categories over
`𝒮` is. -/
instance : Strict (CatFibered.{v₁, v₂, u₁, u₂} 𝒮) where
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
  leftUnitor_eqToIso _ := rfl
  rightUnitor_eqToIso _ := rfl
  associator_eqToIso _ _ _ := rfl

/-- The functor `𝒳 ⥤ 𝒴` underlying a 1-morphism. -/
abbrev homFunctor (G : 𝒳 ⟶ 𝒴) : 𝒳.val.obj ⥤ 𝒴.val.obj := G.hom.toFunctor

/-- The functor underlying a 1-morphism satisfies `p' ∘ G = p`. -/
lemma homFunctor_comp_p (G : 𝒳 ⟶ 𝒴) : homFunctor G ⋙ 𝒴.val.p = 𝒳.val.p :=
  G.hom.w

/-- A 2-morphism `G ⟶ H` is precisely a morphism of the underlying functors all of whose
components lie over an identity of `𝒮`, i.e. a `BasedNatTrans` between the underlying based
functors. -/
def homEquivBasedNatTrans (G H : 𝒳 ⟶ 𝒴) : (G ⟶ H) ≃ BasedNatTrans G.hom H.hom where
  toFun t := t.hom
  invFun t := Hom₂.mk t
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every component of a 2-morphism lies over an identity of `𝒮`. -/
lemma isHomLift_app {G H : 𝒳 ⟶ 𝒴} (t : G ⟶ H) (x : 𝒳.val.obj) :
    𝒴.val.p.IsHomLift (𝟙 (𝒳.val.p.obj x)) (t.hom.app x) :=
  t.hom.isHomLift' x

end CatFibered

end CategoryTheory
