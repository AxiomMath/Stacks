module

public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Uniqueness of a tensor inverse pinned by an evaluation pairing

`StacksFrontier/AlgebraicGeometry/TwistTensor/ThetaIntegerMul.lean` constructs the comparison
`Stacks.Monoidal.isoOfTensorInverse` of two tensor inverses and proves the pin it satisfies.  This
file proves the uniqueness counterpart: an isomorphism of tensor inverses is determined by the
evaluation pairing it is pinned against, as soon as the object being inverted has a tensor inverse
on the left as well.

## Main results

* `Stacks.Monoidal.whiskerLeft_injective_of_tensorInverse`: left whiskering by an object with a
  tensor inverse on the left is injective on morphisms.
* `Stacks.Monoidal.eq_of_tensorHom_comp_eq`: **uniqueness of a tensor inverse pinned by an
  evaluation pairing** — at most one isomorphism `X ≅ Y` carries the pairing of `A` with `X` to
  the pairing of `B` with `Y` along `A ≅ B`.  The hypothesis that `A` has a tensor inverse on the
  left is not removable; the docstring exhibits the counterexample without it.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory

namespace Stacks.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **Left whiskering by an object with a tensor inverse on the left is injective on
morphisms.**  If `Z' ⊗ Z ≅ 𝟙` then a morphism is determined by its left whiskering into `Z`: it
is recovered from it by whiskering into `Z'`, reassociating and cancelling with the inverse law.

This is the mirror of `Stacks.Monoidal.whiskerRight_injective_of_tensorInverse`, and the side the
inverse law is taken on is not interchangeable with it: an inverse law `Z ⊗ Z' ≅ 𝟙` cancels a
right whiskering by `Z` and does *not* cancel a left one, there being no braiding to carry the
one cancellation to the other. -/
theorem whiskerLeft_injective_of_tensorInverse {X Y Z Z' : C} (e : Z' ⊗ Z ≅ 𝟙_ C)
    {u v : X ⟶ Y} (huv : Z ◁ u = Z ◁ v) : u = v := by
  have key : ∀ w : X ⟶ Y,
      (e.hom ▷ X) ≫ (λ_ X).hom ≫ w =
        (α_ Z' Z X).hom ≫ (Z' ◁ (Z ◁ w)) ≫ (α_ Z' Z Y).inv ≫ (e.hom ▷ Y) ≫ (λ_ Y).hom := by
    intro w
    calc (e.hom ▷ X) ≫ (λ_ X).hom ≫ w
        = (e.hom ▷ X) ≫ (𝟙_ C ◁ w) ≫ (λ_ Y).hom := by
          rw [MonoidalCategory.leftUnitor_naturality]
      _ = ((Z' ⊗ Z) ◁ w) ≫ (e.hom ▷ Y) ≫ (λ_ Y).hom := by
          rw [← Category.assoc, ← MonoidalCategory.whisker_exchange, Category.assoc]
      _ = _ := by simp
  have : IsIso (e.hom ▷ X) :=
    inferInstanceAs (IsIso (MonoidalCategory.whiskerRightIso e X).hom)
  refine (cancel_epi (λ_ X).hom).mp ((cancel_epi (e.hom ▷ X)).mp ?_)
  rw [key u, key v, huv]

/-- **Uniqueness of a tensor inverse pinned by an evaluation pairing.**  Let `e : A ≅ B`, let
`hx : A ⊗ X ≅ 𝟙` and `hy : B ⊗ Y ≅ 𝟙` be evaluation pairings, and let `hA : A' ⊗ A ≅ 𝟙` exhibit
a tensor inverse of `A` on the left.  Then at most one isomorphism `φ : X ≅ Y` satisfies
`(e.hom ⊗ₘ φ.hom) ≫ hy.hom = hx.hom`.

The pin says exactly that `A ◁ φ.hom` is one fixed morphism, namely `hx.hom` followed by the
inverse of the isomorphism `e.hom ▷ Y ≫ hy.hom`; so the statement *is* the injectivity of left
whiskering by `A`, and `hA` is what supplies it, through
`Stacks.Monoidal.whiskerLeft_injective_of_tensorInverse`.

The hypothesis `hA` is not removable, and `hx` and `hy` do not supply it: they exhibit `X` and
`Y` as tensor inverses of `A` and `B` on the *right*, which makes `X ⊗ (-)` faithful and says
nothing about `A ⊗ (-)`.  For the counterexample take the strict monoidal category of
endofunctors of `Set^ℕ` with `A ⊗ X` the composite applying `A` after `X` and `𝟙` the identity
functor; let `A` drop the zeroth term of a sequence of sets and let `X = Y` prepend a fixed
two-element set `T`.  Then `A ⊗ X` and `A ⊗ Y` are the identity functor, so `hx`, `hy` and `e`
may all be taken to be identities, while the automorphisms of `X` are the bijections of `T`, of
which there are two; left whiskering by `A` forgets the zeroth term and sends both to the
identity, so both satisfy the pin and they are distinct.

Compare `Stacks.Monoidal.isoOfTensorInverse`, which *constructs* such a `φ` — from the two
pairings taken in the orders `A ⊗ X ≅ 𝟙` and `Y ⊗ B ≅ 𝟙` — and
`Stacks.Monoidal.isoOfTensorInverse_tensorHom_comp_of_mulIso`, which is the pin it satisfies.  In
a braided category the left inverse law needed here is `β_ X A ≪≫ hx`. -/
theorem eq_of_tensorHom_comp_eq {A A' B X Y : C} (e : A ≅ B) (hA : A' ⊗ A ≅ 𝟙_ C)
    (hx : A ⊗ X ≅ 𝟙_ C) (hy : B ⊗ Y ≅ 𝟙_ C) (φ ψ : X ≅ Y)
    (hφ : (e.hom ⊗ₘ φ.hom) ≫ hy.hom = hx.hom)
    (hψ : (e.hom ⊗ₘ ψ.hom) ≫ hy.hom = hx.hom) : φ = ψ := by
  refine Iso.ext (whiskerLeft_injective_of_tensorInverse hA ?_)
  have h : (e.hom ⊗ₘ φ.hom) ≫ hy.hom = (e.hom ⊗ₘ ψ.hom) ≫ hy.hom := hφ.trans hψ.symm
  rw [MonoidalCategory.tensorHom_def', MonoidalCategory.tensorHom_def', Category.assoc,
    Category.assoc] at h
  exact (cancel_mono ((e.hom ▷ Y) ≫ hy.hom)).mp (by simpa only [Category.assoc] using h)

end Stacks.Monoidal
