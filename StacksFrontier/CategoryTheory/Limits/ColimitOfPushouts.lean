module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# A colimit of pushout squares along a fixed morphism is a pushout square

Let `a : A ⟶ R` be a morphism of a category `C` and let `D₁, D₂ : J ⥤ C` be two diagrams of the
same nonempty shape. Suppose given, for every `j`, a square

```
  A ---- α j ----> D₁.obj j
  |                   |
  a                  τ j
  |                   |
  v                   v
  R ---- β j ----> D₂.obj j
```

which is a pushout square, and suppose the three families `α`, `β`, `τ` are compatible with the
transition maps of `D₁` and `D₂`. This file shows that the square obtained by passing to colimits
along `D₁` and `D₂` is again a pushout square. No filteredness hypothesis on `J` is needed, only
that `J` be nonempty; for `J` empty both colimits are initial objects and the square need not be a
pushout.

## Main results

* `CategoryTheory.IsPushout.of_colimit_of_isPushout`: a colimit of pushout squares along a fixed
  morphism `a : A ⟶ R` is a pushout square. The colimit cocones `c₁` on `D₁` and `c₂` on `D₂` and
  the three morphisms `u`, `v`, `w` of the limiting square are taken as data, characterised by the
  hypotheses `hu`, `hv`, `hw`.

## Implementation notes

The compatibility hypothesis `_hα` of `α` is not used in the proof.

## References

* [Stacks Project, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ)
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

/-- A colimit of pushout squares along a fixed morphism `a : A ⟶ R` is a pushout square.

Given diagrams `D₁, D₂ : J ⥤ C` on a nonempty shape `J`, families of morphisms
`α j : A ⟶ D₁.obj j`, `β j : R ⟶ D₂.obj j` and `τ j : D₁.obj j ⟶ D₂.obj j` compatible with the
transition maps (`_hα`, `hβ`, `hτ`) such that every square `IsPushout (α j) a (τ j) (β j)` is a
pushout square, and colimit cocones `c₁` on `D₁` and `c₂` on `D₂`, the induced square

```
  A ------ u ------> c₁.pt
  |                    |
  a                    w
  |                    |
  v                    v
  R ------ v ------> c₂.pt
```

is a pushout square. The morphisms `u`, `v`, `w` are taken as data together with the hypotheses
`hu`, `hv`, `hw` characterising them. -/
theorem IsPushout.of_colimit_of_isPushout
    {C : Type u₁} [Category.{v₁} C] {J : Type u₂} [Category.{v₂} J] [Nonempty J]
    {D₁ D₂ : J ⥤ C} {A R : C} (a : A ⟶ R)
    (α : ∀ j, A ⟶ D₁.obj j) (β : ∀ j, R ⟶ D₂.obj j) (τ : ∀ j, D₁.obj j ⟶ D₂.obj j)
    (_hα : ∀ {i j : J} (f : i ⟶ j), α i ≫ D₁.map f = α j)
    (hβ : ∀ {i j : J} (f : i ⟶ j), β i ≫ D₂.map f = β j)
    (hτ : ∀ {i j : J} (f : i ⟶ j), τ i ≫ D₂.map f = D₁.map f ≫ τ j)
    (hsq : ∀ j, IsPushout (α j) a (τ j) (β j))
    {c₁ : Cocone D₁} (hc₁ : IsColimit c₁) {c₂ : Cocone D₂} (hc₂ : IsColimit c₂)
    {u : A ⟶ c₁.pt} (hu : ∀ j, α j ≫ c₁.ι.app j = u)
    {v : R ⟶ c₂.pt} (hv : ∀ j, β j ≫ c₂.ι.app j = v)
    {w : c₁.pt ⟶ c₂.pt} (hw : ∀ j, c₁.ι.app j ≫ w = τ j ≫ c₂.ι.app j) :
    IsPushout u a w v := by
  obtain ⟨j₀⟩ := ‹Nonempty J›
  have hcomm : u ≫ w = a ≫ v := by
    rw [← hu j₀, ← hv j₀, Category.assoc, hw j₀, (hsq j₀).w_assoc]
  refine IsPushout.of_isColimit' ⟨hcomm⟩ (PushoutCocone.isColimitAux' _ fun S => ?_)
  have hd (j : J) : α j ≫ (c₁.ι.app j ≫ S.inl) = a ≫ S.inr := by
    rw [← Category.assoc, hu j]
    exact S.condition
  have hex : ∃ d : ∀ j, D₂.obj j ⟶ S.pt,
      (∀ j, τ j ≫ d j = c₁.ι.app j ≫ S.inl) ∧ ∀ j, β j ≫ d j = S.inr :=
    ⟨fun j => (hsq j).desc _ _ (hd j), fun j => (hsq j).inl_desc _ _ (hd j),
      fun j => (hsq j).inr_desc _ _ (hd j)⟩
  choose d hτd hβd using hex
  have hnat {i j : J} (f : i ⟶ j) : D₂.map f ≫ d j = d i := by
    refine (hsq i).hom_ext ?_ ?_
    · rw [← Category.assoc, hτ f, Category.assoc, hτd j, hτd i, ← Category.assoc, c₁.w f]
    · rw [← Category.assoc, hβ f, hβd j, hβd i]
  have hexm : ∃ m : c₂.pt ⟶ S.pt, ∀ j, c₂.ι.app j ≫ m = d j :=
    ⟨hc₂.desc { pt := S.pt, ι := { app := d, naturality := fun _ _ f => by simpa using hnat f } },
      fun j => hc₂.fac _ j⟩
  choose m hm using hexm
  have hwm : w ≫ m = S.inl := by
    refine hc₁.hom_ext fun j => ?_
    rw [← Category.assoc, hw j, Category.assoc, hm j, hτd j]
  have hvm : v ≫ m = S.inr := by
    rw [← hv j₀, Category.assoc, hm j₀, hβd j₀]
  have huniq (m' : c₂.pt ⟶ S.pt) (h₁ : w ≫ m' = S.inl) (h₂ : v ≫ m' = S.inr) : m' = m := by
    refine hc₂.hom_ext fun j => ?_
    rw [hm j]
    refine (hsq j).hom_ext ?_ ?_
    · rw [← Category.assoc, ← hw j, Category.assoc, h₁, hτd j]
    · rw [← Category.assoc, hv j, h₂, hβd j]
  exact ⟨m, hwm, hvm, fun h₁ h₂ => huniq _ h₁ h₂⟩

end CategoryTheory

end
