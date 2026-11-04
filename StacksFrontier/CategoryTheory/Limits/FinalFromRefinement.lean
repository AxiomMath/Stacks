module

public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Finality of a functor from nonempty comma categories and common refinements

A functor `u : C ⥤ D` is final when every comma category `I^u_X` of pairs `(Y, X ⟶ u(Y))` is
nonempty and connected.  This file gives the two criteria for connectedness that a functor of
sites usually satisfies:

* any two objects of `I^u_X` admit a *common refinement* — an object mapping to both — whence
  every pair is joined by a zigzag of length two;
* that common refinement exists as soon as `C` has binary products and `u` preserves them, the
  refinement of `(Y₁, a₁)` and `(Y₂, a₂)` being `Y₁ ⨯ Y₂` with the map induced by `a₁` and `a₂`.

Together with `Stacks.ConstantSheaf.constantSheafCompSheafPullbackIsoOfFinal` this reduces the
comparison of constant sheaves along a continuous functor of sites to two statements about the
source site: nonemptiness of the comma categories, and preservation of binary products.

## Main results

* `CategoryTheory.Functor.final_of_exists_hom_of_exists_refinement` — nonemptiness plus common
  refinements imply finality.
* `CategoryTheory.Functor.final_of_exists_hom_of_preservesBinaryProducts` — nonemptiness plus
  binary products in `C` preserved by `u` imply finality.

## What is and is not proved

No tag attribute is placed in this file: finality of a functor is Stacks 04E6 (which already
carries that tag in Mathlib, on `CategoryTheory.Functor.Final`), and what is proved here are two
sufficient conditions for it, not that statement.

Neither criterion is necessary.  A functor can be final with no binary products anywhere in
sight, the comma categories being connected by longer zigzags.

## References

* [Stacks Project, Tag 04E6](https://stacks.math.columbia.edu/tag/04E6)
* [Stacks Project, Tag 09WN](https://stacks.math.columbia.edu/tag/09WN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (u : C ⥤ D)

/-- **Finality from nonemptiness and common refinements.**  Suppose that for every object `X` of
`D` there is a morphism from `X` into the image of `u`, and that any two such morphisms
`a₁ : X ⟶ u(Y₁)` and `a₂ : X ⟶ u(Y₂)` are dominated by a third: an object `Y` with morphisms
`q₁ : Y ⟶ Y₁`, `q₂ : Y ⟶ Y₂` and a morphism `a : X ⟶ u(Y)` with `a ≫ u(q₁) = a₁` and
`a ≫ u(q₂) = a₂`.  Then `u` is final.

The second hypothesis says exactly that the two objects `(Y₁, a₁)` and `(Y₂, a₂)` of the comma
category `I^u_X` receive morphisms from the common object `(Y, a)`, so they are joined by a
zigzag of length two; with the first hypothesis `I^u_X` is therefore nonempty and connected. -/
theorem final_of_exists_hom_of_exists_refinement
    (h₁ : ∀ X : D, ∃ Y : C, Nonempty (X ⟶ u.obj Y))
    (h₂ : ∀ (X : D) (Y₁ Y₂ : C) (a₁ : X ⟶ u.obj Y₁) (a₂ : X ⟶ u.obj Y₂),
      ∃ (Y : C) (q₁ : Y ⟶ Y₁) (q₂ : Y ⟶ Y₂) (a : X ⟶ u.obj Y),
        a ≫ u.map q₁ = a₁ ∧ a ≫ u.map q₂ = a₂) :
    u.Final := by
  refine ⟨fun X => ?_⟩
  obtain ⟨Y₀, ⟨f₀⟩⟩ := h₁ X
  have : Nonempty (StructuredArrow X u) := ⟨StructuredArrow.mk f₀⟩
  refine zigzag_isConnected fun j₁ j₂ => ?_
  obtain ⟨Y, q₁, q₂, a, hq₁, hq₂⟩ := h₂ X j₁.right j₂.right j₁.hom j₂.hom
  exact Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single
      (Or.inr ⟨(StructuredArrow.homMk q₁ hq₁ : StructuredArrow.mk a ⟶ j₁)⟩))
    (Relation.ReflTransGen.single
      (Or.inl ⟨(StructuredArrow.homMk q₂ hq₂ : StructuredArrow.mk a ⟶ j₂)⟩))

/-- **Finality from nonemptiness and preservation of binary products.**  If every object of `D`
admits a morphism into the image of `u`, the source `C` has binary products, and `u` preserves
them, then `u` is final.

The common refinement of `a₁ : X ⟶ u(Y₁)` and `a₂ : X ⟶ u(Y₂)` demanded by
`final_of_exists_hom_of_exists_refinement` is the product `Y₁ ⨯ Y₂` with its two projections:
preservation of the product makes `u(Y₁ ⨯ Y₂)` a product of `u(Y₁)` and `u(Y₂)` in `D`, so `a₁`
and `a₂` induce a morphism `X ⟶ u(Y₁ ⨯ Y₂)` over both. -/
theorem final_of_exists_hom_of_preservesBinaryProducts [HasBinaryProducts C]
    [∀ Y₁ Y₂ : C, PreservesLimit (pair Y₁ Y₂) u]
    (h₁ : ∀ X : D, ∃ Y : C, Nonempty (X ⟶ u.obj Y)) :
    u.Final := by
  refine final_of_exists_hom_of_exists_refinement u h₁ fun X Y₁ Y₂ a₁ a₂ => ?_
  obtain ⟨a, ha₁, ha₂⟩ :=
    BinaryFan.IsLimit.lift' (isLimitOfHasBinaryProductOfPreservesLimit u Y₁ Y₂) a₁ a₂
  exact ⟨Y₁ ⨯ Y₂, Limits.prod.fst, Limits.prod.snd, a, ha₁, ha₂⟩

end CategoryTheory.Functor

end
