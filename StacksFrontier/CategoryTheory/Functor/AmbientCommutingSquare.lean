module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Whiskering

/-!
# Descending a commuting square of functors from an ambient one

A square of functors

```
  A₁ ──F──→ B₁
  │          │
  H          G
  ↓          ↓
  A₂ ──K──→ B₂
```

commutes as soon as it does after comparing each of its four corners with an ambient square, the
comparison on the corner `B₂` reached by both composites being fully faithful.

This is the shape every square of functors between full subcategories takes: each functor is a
lift of a functor of the ambient categories, the comparison with the ambient functor is the
identity, and the content of the square lives upstairs.

## Main definitions

* `CategoryTheory.Functor.squareOfAmbient`.

## Implementation notes

The comparison functors are arbitrary, not inclusions of full subcategories, so that the
statement also covers a corner which is not a subcategory at all: pass the identity functor and
the unitor there. Only the comparison out of the terminal corner has to be fully faithful, which
is what `CategoryTheory.Functor.fullyFaithfulCancelRight` needs.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₁' v₂' v₃' v₄' u₁ u₂ u₃ u₄ u₁' u₂' u₃' u₄'

variable {A₁ : Type u₁} [Category.{v₁} A₁] {A₂ : Type u₂} [Category.{v₂} A₂]
  {B₁ : Type u₃} [Category.{v₃} B₁] {B₂ : Type u₄} [Category.{v₄} B₂]
  {A₁' : Type u₁'} [Category.{v₁'} A₁'] {A₂' : Type u₂'} [Category.{v₂'} A₂']
  {B₁' : Type u₃'} [Category.{v₃'} B₁'] {B₂' : Type u₄'} [Category.{v₄'} B₂']

/-- **A square of functors commutes as soon as an ambient square it is compared with does.**
Given comparison functors `jA₁, jA₂, jB₁, jB₂` out of the four corners, with `jB₂` fully
faithful, isomorphisms comparing each of the four functors of the square with a functor of the
ambient square, and a commuting ambient square, the square commutes. -/
noncomputable def Functor.squareOfAmbient
    (jA₁ : A₁ ⥤ A₁') (jA₂ : A₂ ⥤ A₂') (jB₁ : B₁ ⥤ B₁') (jB₂ : B₂ ⥤ B₂')
    [jB₂.Full] [jB₂.Faithful]
    {F : A₁ ⥤ B₁} {f : A₁' ⥤ B₁'} (hF : F ⋙ jB₁ ≅ jA₁ ⋙ f)
    {G : B₁ ⥤ B₂} {g : B₁' ⥤ B₂'} (hG : G ⋙ jB₂ ≅ jB₁ ⋙ g)
    {H : A₁ ⥤ A₂} {h : A₁' ⥤ A₂'} (hH : H ⋙ jA₂ ≅ jA₁ ⋙ h)
    {K : A₂ ⥤ B₂} {k : A₂' ⥤ B₂'} (hK : K ⋙ jB₂ ≅ jA₂ ⋙ k)
    (α : f ⋙ g ≅ h ⋙ k) :
    F ⋙ G ≅ H ⋙ K :=
  Functor.fullyFaithfulCancelRight jB₂
    (Functor.associator F G jB₂ ≪≫
      Functor.isoWhiskerLeft F hG ≪≫
      (Functor.associator F jB₁ g).symm ≪≫
      Functor.isoWhiskerRight hF g ≪≫
      Functor.associator jA₁ f g ≪≫
      Functor.isoWhiskerLeft jA₁ α ≪≫
      (Functor.associator jA₁ h k).symm ≪≫
      Functor.isoWhiskerRight hH.symm k ≪≫
      Functor.associator H jA₂ k ≪≫
      Functor.isoWhiskerLeft H hK.symm ≪≫
      (Functor.associator H K jB₂).symm)

end CategoryTheory

end
