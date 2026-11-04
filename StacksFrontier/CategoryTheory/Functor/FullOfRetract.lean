module

public import Mathlib.CategoryTheory.Retract

/-!
# Fullness of a functor is inherited by retracts

A functor `G` is full at a pair of objects exactly when `G.map` is surjective on the Hom-set
between them. This file records that this surjectivity **passes to retracts**: if `M` is a
retract of `M₀`, `N` a retract of `N₀`, and `G.map` is surjective on `M₀ ⟶ N₀`, then it is
surjective on `M ⟶ N`.

The argument is the obvious conjugation. Given `ψ : G.obj M ⟶ G.obj N`, push it up to
`G.map r_M ≫ ψ ≫ G.map i_N : G.obj M₀ ⟶ G.obj N₀`, lift that to some `f₀ : M₀ ⟶ N₀`, and take
`i_M ≫ f₀ ≫ r_N`. Its image under `G` is `G.map (i_M ≫ r_M) ≫ ψ ≫ G.map (i_N ≫ r_N)`, and both
outer factors are identities because `i ≫ r = 𝟙` on each side. Only functoriality is used, so
there is no hypothesis on the categories at all.

## Main results

* `CategoryTheory.Functor.exists_map_eq_of_retract`: **surjectivity of `G.map` on a Hom-set
  passes to retracts of the two objects.**
* `CategoryTheory.Functor.full_of_retract`: **a functor is full as soon as it is full at the
  pairs drawn from a class of objects of which every object is a retract.** This is the form a
  consumer uses: a fullness statement available only at some distinguished objects — free sheaves
  of modules, say — becomes fullness outright once every object is exhibited as a retract of a
  distinguished one.

## Implementation notes

The class of distinguished objects is taken as a bare predicate `C → Prop` rather than as an
`CategoryTheory.ObjectProperty`, so that a caller may use a predicate stated with existential
quantifiers over data (an index type and an isomorphism, for instance) without first having to
package it.
-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (G : C ⥤ D)

/-- **Surjectivity of `G.map` on a Hom-set passes to retracts.** If `M` is a retract of `M₀` and
`N` is a retract of `N₀`, then every morphism `G.obj M ⟶ G.obj N` is in the image of `G.map` as
soon as every morphism `G.obj M₀ ⟶ G.obj N₀` is.

The lift of `ψ` is `i_M ≫ f₀ ≫ r_N`, where `f₀` lifts the conjugate `G.map r_M ≫ ψ ≫ G.map i_N`
of `ψ`; the two retraction identities cancel the conjugation. -/
theorem exists_map_eq_of_retract {M N M₀ N₀ : C} (hM : Retract M M₀) (hN : Retract N N₀)
    (h : ∀ ψ : G.obj M₀ ⟶ G.obj N₀, ∃ f : M₀ ⟶ N₀, G.map f = ψ)
    (ψ : G.obj M ⟶ G.obj N) : ∃ f : M ⟶ N, G.map f = ψ := by
  obtain ⟨f₀, hf₀⟩ := h (G.map hM.r ≫ ψ ≫ G.map hN.i)
  refine ⟨hM.i ≫ f₀ ≫ hN.r, ?_⟩
  rw [G.map_comp, G.map_comp, hf₀]
  simp [← G.map_comp_assoc, ← G.map_comp, hM.retract, hN.retract]

/-- **A functor is full as soon as it is full at the pairs drawn from a class of objects of which
every object is a retract.**

`P` is the distinguished class: `hret` exhibits every object as a retract of one satisfying `P`,
and `h` is fullness at a pair of objects satisfying `P`. Fullness at an arbitrary pair is then
`CategoryTheory.Functor.exists_map_eq_of_retract`. -/
theorem full_of_retract (P : C → Prop)
    (hret : ∀ M : C, ∃ M₀ : C, P M₀ ∧ Nonempty (Retract M M₀))
    (h : ∀ M₀ N₀ : C, P M₀ → P N₀ →
      ∀ ψ : G.obj M₀ ⟶ G.obj N₀, ∃ f : M₀ ⟶ N₀, G.map f = ψ) :
    G.Full where
  map_surjective {M N} ψ := by
    obtain ⟨M₀, hM₀, ⟨rM⟩⟩ := hret M
    obtain ⟨N₀, hN₀, ⟨rN⟩⟩ := hret N
    exact exists_map_eq_of_retract G rM rN (h M₀ N₀ hM₀ hN₀) ψ

end CategoryTheory.Functor

end
