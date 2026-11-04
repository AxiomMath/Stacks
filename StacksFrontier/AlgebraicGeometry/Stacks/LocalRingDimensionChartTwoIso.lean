module

public import StacksFrontier.AlgebraicGeometry.Stacks.LocalRingDimensionSquareIndependence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex

/-!
# The invariant of Stacks 0DSA is unchanged when the chart is replaced by a 2-isomorphic one

The comparison of two smooth charts in **Stacks 0DS9** produces a common refinement `W` together
with a *2-isomorphism* of the two composites `W ⟶ 𝒳`
(`AlgebraicGeometry.Stack.exists_smoothChart_refining_two_smoothCharts`), not an equality. So
before the two refinement comparisons can be chained, the invariant of Stacks 0DSA has to be
known to be unchanged when the chart `g : V ⟶ 𝒳` is replaced by a 2-isomorphic `g'`. That is
what this file proves.

## Main results

* `AlgebraicGeometry.Stack.selfIntersectionDiagonalPreHomCongrTwoIso`: a mediating morphism from
  the tautological square into a presented self-intersection of `g`, read as one into the
  doubly-reindexed square over the cospan `(g', g')`, with the *same* underlying 1-morphism.
* `AlgebraicGeometry.Stack.hasRelationLocalRingDimension_congr_twoIso`: the invariant at a point
  `ν` of the chart is the same for `g` and for `g'`, each with an arbitrary presented
  self-intersection — at the same point of the chart, with no transport.

## Implementation notes

**Why reindexing the cospan costs almost nothing.**
`CategoryTheory.Bicategory.TwoCommSq.reindexFst` and `.reindexSnd` change neither the apex nor
the two projections of a 2-commutative square — only its filler — and carry terminality along
(`CategoryTheory.Bicategory.isTwoFibreProduct_reindexFst`, `...reindexSnd`). So for `η : g ≅ g'`
the doubly-reindexed square `T₁ = (T.reindexFst η).reindexSnd η` over the cospan `(g', g')` has
`T₁.pt = T.pt` and `T₁.snd = T.snd` *by `rfl`*. Three consequences, all definitional:

* the equivalence `eQ` presenting `T.pt` presents `T₁.pt` with no retyping;
* `AlgebraicGeometry.Stack.selfIntersectionSourceMap` at `T₁` is *literally the same morphism* of
  presheaves as at `T`, since it is read off `sq.snd.hom`;
* `AlgebraicGeometry.Stack.HasRelationLocalRingDimension` at `(g', T₁)` and at `(g, T)` are the
  same proposition — the predicate mentions the chart's 1-morphism only through the square's
  second leg. That is why the first step of the comparison below is `Iff.rfl`.

What is *not* definitional is the mediating morphism giving the diagonal. A morphism of
2-commutative squares from the tautological square into `T` carries, besides its 1-morphism and
two comparison 2-cells, the compatibility square of **Stacks 003O**, and that square mentions
both fillers; reindexing changes `T`'s filler and replaces the tautological square at `g` by the
tautological square at `g'`, which is *not* a reindexing of it — both have the identity filler,
whereas a reindexing of the identity filler is `t ◁ η⁻¹ ≫ t ◁ η`, equal to the identity only
propositionally. So the compatibility square is re-proved here, by
`AlgebraicGeometry.Stack.compat_tautological_reindexBoth`, and
`CategoryTheory.Bicategory.reindexFst_compat_iff` is not applicable: it moves one leg of the
cospan and here both move.

Following the implementation note of
`StacksFrontier/CategoryTheory/TwoFibreProduct/CospanReindex.lean`, that computation is stated for
bare 1- and 2-morphisms rather than for the squares, so that each rewrite fires on the nose; the
squares meet it at `exact`-level unification, where the definitional identities above are
available.

The computation itself is two instances of one naturality fact — whiskering an invertible
2-morphism of a cospan leg past a comparison 2-cell, which is the exchange law followed by
naturality of the associator in its last argument — applied once with `η⁻¹` on the first
projection and once with `η` on the second, after which `η⁻¹ ≫ η = 𝟙` closes it. The two
whiskerings genuinely cancel against each other; neither does on its own.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 0DS9](https://stacks.math.columbia.edu/tag/0DS9)
* [Stacks Project, Tag 0DSA](https://stacks.math.columbia.edu/tag/0DSA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

/-! ### The compatibility square of Stacks 003O under reindexing both legs of a cospan -/

section Compat

universe w₁ v₁ u₁

variable {A : Type u₁} [Bicategory.{w₁, v₁} A] {X Z W V : A} {f f' : X ⟶ Z}

/-- Let `θ : f ≅ f'` be an invertible 2-morphism. If a 1-morphism `u` with 2-cells
`aFst : t ⟶ u ≫ sfst` and `aSnd : t ⟶ u ≫ ssnd` satisfies the compatibility square of a morphism
from the square with identity filler on `t ≫ f` into the square with filler `siso`, then it
satisfies the compatibility square from the square with identity filler on `t ≫ f'` into the
square with filler `sfst ◁ θ.inv ≫ siso ≫ ssnd ◁ θ.hom`. -/
theorem compat_tautological_reindexBoth (θ : f ≅ f') (u : W ⟶ V) (t : W ⟶ X)
    (sfst ssnd : V ⟶ X) (siso : sfst ≫ f ⟶ ssnd ≫ f)
    (aFst : t ⟶ u ≫ sfst) (aSnd : t ⟶ u ≫ ssnd)
    (h : 𝟙 (t ≫ f) ≫ (aSnd ▷ f) ≫ (α_ u ssnd f).hom
      = (aFst ▷ f) ≫ (α_ u sfst f).hom ≫ (u ◁ siso)) :
    𝟙 (t ≫ f') ≫ (aSnd ▷ f') ≫ (α_ u ssnd f').hom
      = (aFst ▷ f') ≫ (α_ u sfst f').hom ≫
        (u ◁ ((sfst ◁ θ.inv ≫ siso) ≫ ssnd ◁ θ.hom)) := by
  rw [Category.id_comp] at h ⊢
  have key {s : V ⟶ X} (a : t ⟶ u ≫ s) {k k' : X ⟶ Z} (φ : k ⟶ k') :
      t ◁ φ ≫ (a ▷ k') ≫ (α_ u s k').hom = (a ▷ k) ≫ (α_ u s k).hom ≫ u ◁ s ◁ φ := by
    rw [whisker_exchange_assoc, associator_naturality_right]
  refine Eq.symm ?_
  rw [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% (key aFst θ.inv), ← reassoc_of% h, ← key aSnd θ.hom,
    whiskerLeft_inv_hom_assoc]

end Compat

/-! ### The invariant at a 2-isomorphic chart -/

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : AlgebraicStacks.{u, w} B S hS} (V : BigFppfOver B S hS)
  {g g' : schemeStack.{u, w} B S hS V ⟶ 𝒳} (η : g ≅ g')
  (T : Bicategory.TwoCommSq g g)

/-- **A mediating morphism giving the diagonal, read at a 2-isomorphic chart.** A morphism `δ` of
2-commutative squares from the tautological square of `g` into a presented self-intersection `T`
of `g` is also one from the tautological square of `g'` into the doubly-reindexed square
`(T.reindexFst η).reindexSnd η` over the cospan `(g', g')`, with the same underlying 1-morphism
and the same two comparison 2-cells. -/
def selfIntersectionDiagonalPreHomCongrTwoIso
    (δ : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS V g) T) :
    Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS V g')
      ((T.reindexFst η).reindexSnd η) where
  hom := δ.hom
  isoFst := δ.isoFst
  isoSnd := δ.isoSnd
  compat :=
    compat_tautological_reindexBoth η δ.hom (𝟙 (schemeStack.{u, w} B S hS V)) T.fst T.snd
      T.iso.hom δ.isoFst.hom δ.isoSnd.hom δ.compat

include η in
/-- **The invariant of Stacks 0DSA does not change when the chart is replaced by a 2-isomorphic
one.** Let `η : g ≅ g'` be a 2-isomorphism of smooth charts `V ⟶ 𝒳`, let `T` be a presented
self-intersection of `g` and `T'` one of `g'`, each with its own presenting algebraic space,
comparison equivalence and mediating morphism, and let `ν` be a point of `V`. Then the two
presentations measure the invariant at `ν` to be the same integer.

The point of the chart does not move, and neither does the comparison equivalence `eV` of the
chart: a 2-isomorphism of the chart's 1-morphism leaves `V`, and hence the presheaf it
represents, alone. -/
theorem hasRelationLocalRingDimension_congr_twoIso
    (hT : Bicategory.IsTwoFibreProduct T)
    (T' : Bicategory.TwoCommSq g' g') (hT' : Bicategory.IsTwoFibreProduct T')
    (Q Q' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eV : StacksRepresentableCFG.EquivalenceOver
      (schemeStack.{u, w} B S hS V).val.val.p
      (presheafOfCategories (yoneda.obj V ⋙ typeToCat)).p)
    (eQ : StacksRepresentableCFG.EquivalenceOver
      T.pt.val.val.p (presheafOfCategories (Q ⋙ typeToCat)).p)
    (eQ' : StacksRepresentableCFG.EquivalenceOver
      T'.pt.val.val.p (presheafOfCategories (Q' ⋙ typeToCat)).p)
    (δ : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS V g) T)
    (δ' : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS V g') T')
    (ν : Space.points B S hS (yoneda.obj V)) (d : ℤ) :
    HasRelationLocalRingDimension B S hS V g T Q eV eQ
        (Space.pointsMap B S hS (yoneda.obj V)
          (selfIntersectionDiagonalMap B S hS V g T Q eV eQ δ) ν) d ↔
      HasRelationLocalRingDimension B S hS V g' T' Q' eV eQ'
        (Space.pointsMap B S hS (yoneda.obj V)
          (selfIntersectionDiagonalMap B S hS V g' T' Q' eV eQ' δ') ν) d :=
  (Iff.rfl.trans
    (hasRelationLocalRingDimension_transport_twoFibreProduct B S hS V g'
      ((T.reindexFst η).reindexSnd η) T' Q Q' eV eQ eQ'
      (Bicategory.isTwoFibreProduct_reindexSnd η (Bicategory.isTwoFibreProduct_reindexFst η hT))
      hT' (selfIntersectionDiagonalPreHomCongrTwoIso B S hS V η T δ) δ' ν d))

end AlgebraicGeometry.Stack

end
