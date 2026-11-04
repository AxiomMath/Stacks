module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import StacksCore.Tactic.StacksAttribute

/-!
# Flatness of translation on a group scheme

Let `G` be a group scheme over `S` and `T` a flat scheme over `S`. For any `S`-morphism
`ψ : T ⟶ G`, multiplication after `ψ` on the first factor gives a flat morphism
`T ×[S] G ⟶ G`. In particular, multiplication is flat when `G` is flat over `S`.

## Main results

* `AlgebraicGeometry.flat_mul_after_map`: the morphism `(t, g) ↦ ψ(t) * g` is flat.
* `AlgebraicGeometry.flat_mul`: multiplication is flat for a flat group scheme.

## Implementation notes

A group scheme over `S` is a group object in `Over S`; its tensor product is the fibre product
over `S`. The first result uses the lift of `ψ` after the first projection together with the
second projection to `G`, followed by group multiplication; translating by the inverse of `ψ`
is an inverse automorphism of `T ×[S] G`, so the morphism in question differs from the flat
second projection by an isomorphism. The second result is the specialization `T = G`,
`ψ = 𝟙 G`.

## References

* [Stacks Project, Tag 047H](https://stacks.math.columbia.edu/tag/047H)
-/

@[expose] public section

open CategoryTheory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

/-- Translating by `f` and then by its inverse on the second factor cancels. -/
private lemma translate_then_inverse_cancel {C : Type*} [Category* C]
    [CartesianMonoidalCategory C] {A G : C} [GrpObj G] (f g : A ⟶ G) :
    lift (f ≫ ι[G]) (lift f g ≫ μ[G]) ≫ μ[G] = g := by
  rw [← MonObj.lift_lift_assoc (f ≫ ι[G]) f g]; simp

/-- **Stacks Project, Tag 047H.** Left translation parametrized by a flat scheme is flat. -/
@[stacks 047H "translation"]
lemma flat_mul_after_map {S : Scheme.{u}} (G T : Over S) [GrpObj G]
    (ψ : T ⟶ G) [Flat T.hom] :
    Flat (lift (fst T G ≫ ψ) (snd T G) ≫ μ[G]).left := by
  have key (φ : T ⟶ G) :
      lift (fst T G) (lift (fst T G ≫ φ) (snd T G) ≫ μ[G]) ≫
        lift (fst T G) (lift (fst T G ≫ φ ≫ ι[G]) (snd T G) ≫ μ[G]) = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · rw [Category.assoc]; simp only [Category.id_comp, CartesianMonoidalCategory.lift_snd]
      rw [← Category.assoc, CartesianMonoidalCategory.comp_lift]
      simpa using translate_then_inverse_cancel (fst T G ≫ φ) (snd T G)
  let α := lift (fst T G) (lift (fst T G ≫ ψ) (snd T G) ≫ μ[G])
  let β := lift (fst T G) (lift (fst T G ≫ ψ ≫ ι[G]) (snd T G) ≫ μ[G])
  have : IsIso α := ⟨⟨β, key ψ, by simpa [α, β] using key (ψ ≫ ι[G])⟩⟩
  have : IsIso α.left := inferInstanceAs (IsIso ((Over.forget S).map α))
  have : Flat α.left := by infer_instance
  have : Flat (snd T G).left := by
    show Flat (Limits.pullback.snd T.hom G.hom); infer_instance
  have heq : α.left ≫ (snd T G).left = (lift (fst T G ≫ ψ) (snd T G) ≫ μ[G]).left := by
    simpa [Scheme.Hom.comp_base] using congrArg Over.Hom.left
      (show α ≫ snd T G = lift (fst T G ≫ ψ) (snd T G) ≫ μ[G] from by
        apply Over.OverMorphism.ext; simp [α])
  rw [← heq]; infer_instance

/-- **Stacks Project, Tag 047H.** Multiplication on a flat group scheme is flat. -/
@[stacks 047H "multiplication", sga "3 XVIII 2.2"]
lemma flat_mul {S : Scheme.{u}} (G : Over S) [GrpObj G] [Flat G.hom] :
    Flat μ[G].left := by
  simpa using (flat_mul_after_map (G := G) (T := G) (ψ := 𝟙 G))

end AlgebraicGeometry
