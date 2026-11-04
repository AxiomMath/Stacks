module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Cancelling the middle factor in an iterated 2-fibre product (Stacks 02XD)

Fix categories and functors `A --F--> B <--G-- C <--H-- D`. Writing `×` for the 2-fibre product
of categories, i.e. Mathlib's `CategoryTheory.Limits.CategoricalPullback`, there are three
2-fibre products in sight: `A ×_B C = CategoricalPullback F G` with second projection
`π₂ : A ×_B C ⥤ C`, the iterated product `(A ×_B C) ×_C D = CategoricalPullback (π₂ F G) H`, and
`A ×_B D = CategoricalPullback F (H ⋙ G)`. This file constructs the canonical equivalence
`(A ×_B C) ×_C D ≌ A ×_B D`,
which holds for all categories and functors, with no existence or size hypotheses.

The comparison functor sends `((a, c, φ : F a ≅ G c), d, ψ : c ≅ H d)` to
`(a, d, G(ψ) ∘ φ : F a ≅ G (H d))`, and its inverse sends `(a, d, χ : F a ≅ G (H d))` to
`((a, H d, χ), d, 𝟙 (H d))`; the unit and counit are built from the structural isomorphisms of
the objects involved. The result is a genuine `CategoryTheory.Equivalence`, not an isomorphism
or equality of categories.
-/

@[expose] public section

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

namespace CategoryTheory.Limits.CategoricalPullback

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
    (F : A ⥤ B) (G : C ⥤ B) (H : D ⥤ C)

-- `π₂` is a plain `def`, and Lean 4.34 checks implicit arguments at `implicit` transparency,
-- which unfolds only `[reducible]`/`[instance_reducible]`/`[implicit_reducible]` definitions.
-- Objects of `(A ×_B C) ×_C D` have their structural isomorphism typed as
-- `(π₂ F G).obj X.fst ≅ H.obj X.snd`, and every `simp`/`rw` below has to see that this is
-- `X.fst.snd ≅ H.obj X.snd`. `Functor.comp` already carries this attribute upstream.
attribute [local implicit_reducible] π₂

/-- The comparison functor `(A ×_B C) ×_C D ⥤ A ×_B D`, sending
`((a, c, φ), d, ψ)` to `(a, d, G(ψ) ∘ φ)`. -/
def assocCompFunctor :
    CategoricalPullback (π₂ F G) H ⥤ CategoricalPullback F (H ⋙ G) where
  obj X := ⟨X.fst.fst, X.snd, X.fst.iso ≪≫ G.mapIso X.iso⟩
  map {X Y} f := ⟨f.fst.fst, f.snd, by
    have w1 := f.fst.w
    have w2 : f.fst.snd ≫ Y.iso.hom = X.iso.hom ≫ H.map f.snd := f.w
    have w2' : G.map f.fst.snd ≫ G.map Y.iso.hom = G.map X.iso.hom ≫ G.map (H.map f.snd) := by
      rw [← G.map_comp, ← G.map_comp]; exact congrArg _ w2
    dsimp only [Iso.trans_hom, Functor.mapIso_hom, Functor.comp_map]
    rw [reassoc_of% w1, Category.assoc]
    exact congrArg (X.fst.iso.hom ≫ ·) w2'⟩
  map_id X := by apply hom_ext <;> rfl
  map_comp f g := by apply hom_ext <;> rfl

/-- The functor `A ×_B D ⥤ (A ×_B C) ×_C D` inverse to `assocCompFunctor`, sending
`(a, d, χ)` to `((a, H d, χ), d, 𝟙 (H d))`. -/
def assocCompInverse :
    CategoricalPullback F (H ⋙ G) ⥤ CategoricalPullback (π₂ F G) H where
  obj X := ⟨⟨X.fst, H.obj X.snd, X.iso⟩, X.snd, Iso.refl (H.obj X.snd)⟩
  map {X Y} f := ⟨⟨f.fst, H.map f.snd, by
      have w1 := f.w
      dsimp only [Functor.comp_map] at w1 ⊢
      exact w1⟩, f.snd, by
      -- Stated with the identities pinned at `H.obj _`: in the goal they are spelled through
      -- `π₂` of a structure literal, which `simp` cannot retype under.
      have key : H.map f.snd ≫ 𝟙 (H.obj Y.snd) = 𝟙 (H.obj X.snd) ≫ H.map f.snd := by simp
      exact key⟩
  map_id X := by
    refine hom_ext ?_ ?_
    · refine hom_ext ?_ ?_ <;> simp
    · simp
  map_comp f g := by
    refine hom_ext ?_ ?_
    · refine hom_ext ?_ ?_ <;> simp
    · simp

/-- Component of the unit isomorphism `𝟭 ≅ assocCompFunctor ⋙ assocCompInverse`; on
`((a, c, φ), d, ψ)` it is `ψ` in the middle factor and the identity elsewhere. -/
def assocCompUnitIsoApp (p : CategoricalPullback (π₂ F G) H) :
    p ≅ (assocCompFunctor F G H ⋙ assocCompInverse F G H).obj p :=
  mkIso (mkIso (Iso.refl _) p.iso (by dsimp [assocCompFunctor, assocCompInverse]; simp))
    (Iso.refl _) (by
      -- Both sides pinned to the reduced spelling; in the goal they are read off through `π₂`
      -- of a `mkIso` and through the composite functor, which `simp` cannot retype under.
      have key : p.iso.hom ≫ 𝟙 (H.obj p.snd) = p.iso.hom ≫ H.map (𝟙 p.snd) := by simp
      exact key)

/-- Component of the counit isomorphism `assocCompInverse ⋙ assocCompFunctor ≅ 𝟭`; it is the
identity in both factors. -/
def assocCompCounitIsoApp (q : CategoricalPullback F (H ⋙ G)) :
    (assocCompInverse F G H ⋙ assocCompFunctor F G H).obj q ≅ q :=
  mkIso (Iso.refl _) (Iso.refl _) (by
    dsimp [assocCompFunctor, assocCompInverse]
    simp)

-- Same reason: `dsimp` unfolds these two below, and the `mkIso` proof obligations that surface
-- then have to be retyped through them.
attribute [local implicit_reducible] assocCompFunctor assocCompInverse

/-- **Stacks 02XD.** The canonical equivalence of categories `(A ×_B C) ×_C D ≌ A ×_B D`
for `A --F--> B <--G-- C <--H-- D`, i.e.
`CategoricalPullback (π₂ F G) H ≌ CategoricalPullback F (H ⋙ G)`, given by
`assocCompFunctor`. -/
@[stacks 02XD]
def assocComp :
    CategoricalPullback (π₂ F G) H ≌ CategoricalPullback F (H ⋙ G) :=
  Equivalence.mk (assocCompFunctor F G H) (assocCompInverse F G H)
    (NatIso.ofComponents (assocCompUnitIsoApp F G H) (by
      intro X Y f
      apply hom_ext
      · apply hom_ext
        · dsimp [assocCompFunctor, assocCompInverse, assocCompUnitIsoApp]; simp
        · dsimp [assocCompFunctor, assocCompInverse, assocCompUnitIsoApp]; exact f.w
      · dsimp [assocCompFunctor, assocCompInverse, assocCompUnitIsoApp]; simp))
    (NatIso.ofComponents (assocCompCounitIsoApp F G H) (by
      intro X Y f
      apply hom_ext <;>
        · dsimp [assocCompFunctor, assocCompInverse, assocCompCounitIsoApp]; simp))

end CategoryTheory.Limits.CategoricalPullback
