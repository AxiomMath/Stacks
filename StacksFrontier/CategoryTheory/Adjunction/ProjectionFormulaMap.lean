module

public import StacksFrontier.CategoryTheory.BifunctorProdMap
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Products.Basic

/-!
# The projection-formula map of an adjunction

Let `L ⊣ R` be an adjunction, let `A` be a bifunctor on the source of `L` and `B` one on its
target, and let `α : A ⋙ L ⟶ L.prod L ⋙ B` compare them. Then there is a canonical map

  `A(R G, H) ⟶ R (B(G, L H))`,

the adjoint transpose of `α` composed with the counit in the first factor. Every projection
formula in the library is an instance of it: `A` and `B` are tensor products and `L`, `R` are a
pullback–pushforward pair, and the projection formula is the assertion that this map is an
isomorphism.

## Main definitions

* `CategoryTheory.adjunctionTensorMap`: the map itself.

## Main results

* `CategoryTheory.map_adjunctionTensorMap_comp_counit`: the defining equation with the transpose
  carried out — applying `L` to the map and following with the counit gives the composite the map
  is the transpose of.
* `CategoryTheory.adjunctionTensorMap_eq_unit_comp`: the map written through the unit.
* `CategoryTheory.adjunctionTensorMap_natural`: it is natural in both arguments.
* `CategoryTheory.adjunctionTensorMap_unit`: tensoring with the unit and then applying it is the
  adjoint transpose of the comparison.
* `CategoryTheory.bifunctor_map_comp_left`, `CategoryTheory.bifunctor_map_comp_right`,
  `CategoryTheory.bifunctor_map_comp_both`: a composition in one or in both factors of a
  bifunctor splits.
* `CategoryTheory.bifunctor_comparison_naturality` (in
  `StacksFrontier.CategoryTheory.BifunctorProdMap`): naturality of `α`, written one factor at a time.
-/

@[expose] public section

namespace CategoryTheory

open scoped CategoryTheory.Prod

variable {C : Type*} {D : Type*} [Category C] [Category D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- The canonical map `A(R G, H) ⟶ R (B(G, L H))`: the adjoint transpose of the comparison
followed by the counit in the first factor. -/
public def adjunctionTensorMap (G : D) (H : C) :
    A.obj (R.obj G, H) ⟶ R.obj (B.obj (G, L.obj H)) :=
  adj.homEquiv _ _ (α.app (R.obj G, H) ≫ B.map (adj.counit.app G ×ₘ 𝟙 (L.obj H)))

/-- **The defining equation of the canonical map, transposed.**  Applying `L` to
`adjunctionTensorMap` and following with the counit of `L ⊣ R` gives the composite the map is the
transpose of: `α` at `(R G, H)`, followed by `B` of the counit at `G` in the first variable and
the identity in the second.

This is the characterization `adjunctionTensorMap` is defined by, written without
`Adjunction.homEquiv` so that it can be used as a rewrite rule in the middle of a composite.
The transpose must not be taken at the point of use: unfolding `adjunctionTensorMap` and
rewriting with `Adjunction.homEquiv_symm_apply` in a concrete instance leaves the two sides of
the equivalence to be matched by unification, and on the instance at the derived categories of a
ringed space that unification exhausts the default heartbeat limit.  Stated here, in bare
categories and with both sides written out, there is nothing left to unify. -/
@[reassoc]
public lemma map_adjunctionTensorMap_comp_counit (G : D) (H : C) :
    L.map (adjunctionTensorMap adj A B α G H) ≫ adj.counit.app (B.obj (G, L.obj H)) =
      α.app (R.obj G, H) ≫ B.map (adj.counit.app G ×ₘ 𝟙 (L.obj H)) := by
  have h := (adj.homEquiv (A.obj (R.obj G, H)) (B.obj (G, L.obj H))).symm_apply_apply
    (α.app (R.obj G, H) ≫ B.map (adj.counit.app G ×ₘ 𝟙 (L.obj H)))
  rw [Adjunction.homEquiv_counit] at h
  exact h

/-- The canonical map, written through the unit of the adjunction. -/
public lemma adjunctionTensorMap_eq_unit_comp (G : D) (H : C) :
    adjunctionTensorMap adj A B α G H =
      adj.unit.app (A.obj (R.obj G, H)) ≫
        R.map (α.app (R.obj G, H) ≫ B.map (adj.counit.app G ×ₘ 𝟙 (L.obj H))) := by
  unfold adjunctionTensorMap
  exact Adjunction.homEquiv_unit adj _ _ _

/-- Transposing the canonical map after a morphism `u ×ₘ k` in the source. -/
private lemma homEquiv_symm_map_comp_adjunctionTensorMap {F : C} {G' : D} {H H' : C}
    (u : F ⟶ R.obj G') (k : H ⟶ H') :
    (adj.homEquiv _ _).symm (A.map (u ×ₘ k) ≫ adjunctionTensorMap adj A B α G' H') =
      α.app (F, H) ≫ B.map (L.map u ×ₘ L.map k) ≫ B.map (adj.counit.app G' ×ₘ 𝟙 (L.obj H')) := by
  unfold adjunctionTensorMap
  rw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply,
    ← Category.assoc, bifunctor_comparison_naturality A B α u k, Category.assoc]

/-- The canonical map is natural in both arguments. -/
public lemma adjunctionTensorMap_natural {G G' : D} {H H' : C} (g : G ⟶ G') (k : H ⟶ H') :
    A.map (R.map g ×ₘ k) ≫ adjunctionTensorMap adj A B α G' H' =
      adjunctionTensorMap adj A B α G H ≫ R.map (B.map (g ×ₘ L.map k)) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [homEquiv_symm_map_comp_adjunctionTensorMap, Adjunction.homEquiv_naturality_right_symm,
    adjunctionTensorMap, Equiv.symm_apply_apply, Category.assoc, ← Functor.map_comp]
  rw [← B.map_comp]
  congr 2
  apply Prod.ext
  · exact adj.counit.naturality g
  · simp

/-- Tensoring the unit and then applying the canonical map is the adjoint transpose of the
comparison. -/
public lemma adjunctionTensorMap_unit (F H : C) :
    A.map (adj.unit.app F ×ₘ 𝟙 H) ≫ adjunctionTensorMap adj A B α (L.obj F) H =
      adj.homEquiv _ _ (α.app (F, H)) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [homEquiv_symm_map_comp_adjunctionTensorMap, ← B.map_comp]
  simp [← CategoryTheory.prod_id]

/- `bifunctor_map_comp_left`, `bifunctor_map_comp_right` and `bifunctor_map_comp_both` stood
here, stated for one category `D` and `B : D × D ⥤ D`. They are the same three statements as
the ones in `StacksFrontier.CategoryTheory.BifunctorProdMap`, publicly imported above, which
proves them for a bifunctor `C₁ × C₂ ⥤ C₃` between three categories and so subsumes them at
`C₁ = C₂ = C₃ = D`. One copy is kept, under the same fully qualified names, and this file
carries it through to every consumer that had them from here. -/

end CategoryTheory

end
