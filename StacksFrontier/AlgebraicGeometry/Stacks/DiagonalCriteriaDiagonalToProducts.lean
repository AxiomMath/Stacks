module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaSchemePoints
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.DiagonalFibre
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Equivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverProdDiagonalEquiv
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverSliceProduct
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-!
# From a representable diagonal to algebraic-space 2-fibre products (Stacks 045G, (1) ⇒ (4))

Let `S` be a scheme contained in a big fppf site `B` and let `𝒳` be a category fibred in groupoids
over the big fppf site of `S`. This file proves the implication from condition (1) of Stacks 045G —
the diagonal `𝒳 ⟶ 𝒳 × 𝒳` is representable by algebraic spaces — to condition (4): the 2-fibre
product over `𝒳` of any two scheme-valued points of `𝒳` is representable by an algebraic space.

This is the direction of Stacks 045G that the source writes as the chain of equivalences

```text
(Sch/U)_{fppf} ×_{x, 𝒳, y} (Sch/V)_{fppf}
  ≅ (Sch/(U ×_S V))_{fppf} ×_{(x, y), 𝒳 × 𝒳, Δ} 𝒳
```

and the proof here is exactly that chain, in two steps. Stacks 02XE over the site identifies the
left-hand side with the 2-fibre product of the cospan `(x × y, Δ)` whose first vertex is the
*product* `(Sch/U) × (Sch/V)` of the two slices
(`CategoryTheory.TwoFibreProductOver.prodDiagComparison`), and the product of two slices is the
slice over the product of the two objects
(`CategoryTheory.TwoFibreProductOver.sliceProd`), which for the big fppf site of `S` is
`U ×_S V`. Both identifications are equivalences *over* the site that commute with the structure
functors on the nose, so the representability statement of condition (1) at the scheme `U ×_S V`
transports along them, after the base is moved from `U ×_S V` to `S` by the forward half of
Stacks 03I5 (`AlgebraicGeometry.Stack.exists_isAlgebraicSpace_equivalenceOver_comp_overMap`).

## Main results

* `AlgebraicGeometry.Stack.hasAlgebraicSpaceSchemePointProducts_of_hasRepresentableDiagonal`:
  **Stacks 045G**, condition (1) implies condition (4).
* `AlgebraicGeometry.Stack.isRepresentableFromSchemes_of_isAlgebraicSpaceIsomPresheaf`: the same
  implication read between conditions (2) and (3), using the equivalences (1) ⇔ (2) and
  (3) ⇔ (4).

## Implementation notes

The scheme-valued point quantified over in condition (1) is taken at `W = U ×_S V`, and the
1-morphism `W ⟶ 𝒳 × 𝒳` fed to it is the composite of the iterated-slice equivalence
`CategoryTheory.Over.iteratedSliceBackward`, of the comparison of `𝒞/W` with
`(𝒞/U) × (𝒞/V)` and of the product 1-morphism `x × y`; all three commute with the structure
functors on the nose, so the compatibility hypothesis is `rfl`.

The underlying functors of the two scheme-valued points are replaced by variables of their
reduced types at the start of the proof. Without that, every subsequent term is stated through
`(AlgebraicGeometry.Stack.schemeFibredCategory B S hS U).val.p` rather than through
`CategoryTheory.Over.forget U`, and the two are definitionally equal only after unfolding
`CategoryTheory.BasedCategory.ofFunctor`, which neither `rw` nor instance search will do.

Binary products of the site are not an instance of the ambient library: they come from fibre
products of schemes through `CategoryTheory.Over.ConstructProducts`, so they are supplied here as
a local instance.

The converse implication (4) ⇒ (1) is **not** in this file. It is not an equivalence of 2-fibre
products but a fibre-product statement: the fibre of the diagonal over a point of `𝒳 × 𝒳` defined
on `𝒞/U` is the fibre product of `𝒞/U` with the 2-fibre product of the two scheme-valued points
over `(𝒞/U) × (𝒞/U) = 𝒞/(U ×_S U)`, so it needs Stacks 02X2 in the form
`AlgebraicGeometry.isAlgebraicSpace_of_isPullback` and not merely a chain of equivalences.

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 02XE](https://stacks.math.columbia.edu/tag/02XE)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PresheafOfCategories
open CategoryTheory.TwoFibreProductOver.DiagonalFibre

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The big fppf site of `S` has binary products: the product of two schemes over `S` is their
fibre product over `S`, which the site has because the category of schemes of `B` has pullbacks. -/
theorem hasBinaryProducts_bigFppfOver : HasBinaryProducts (BigFppfOver B S hS) :=
  Over.ConstructProducts.over_binaryProduct_of_pullback

attribute [local instance] hasBinaryProducts_bigFppfOver

/-- The composite of two equivalences is an equivalence, with both hypotheses explicit. -/
private theorem isEquivalence_comp' {A : Type*} [Category A] {Bb : Type*} [Category Bb]
    {C : Type*} [Category C] (F : A ⥤ Bb) (G : Bb ⥤ C)
    (hF : F.IsEquivalence) (hG : G.IsEquivalence) : (F ⋙ G).IsEquivalence :=
  ((@Functor.asEquivalence A _ Bb _ F hF).trans
    (@Functor.asEquivalence Bb _ C _ G hG)).isEquivalence_functor

/-- The structure functor of the 2-fibre product of two fibred categories over the identity of
the base, via the identity, is fibred in groupoids. -/
private theorem isFiberedInGroupoids_structureFunctor_id {𝒞 : Type*} [Category 𝒞]
    {A : Type*} [Category A] {Bb : Type*} [Category Bb] (p : A ⥤ 𝒞) (q : Bb ⥤ 𝒞)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) :
    (TwoFibreProductOver.structureFunctor p q (𝟭 𝒞) p q).IsFiberedInGroupoids :=
  TwoFibreProductOver.isFiberedInGroupoids p q (𝟭 _) p q hp hq
    Functor.isFiberedInGroupoids_id rfl rfl

variable (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))

/-- If the diagonal of `𝒳` is representable by algebraic spaces, then for 1-morphisms
`xf : 𝒞/U ⥤ 𝒳` and `yf : 𝒞/V ⥤ 𝒳` over the site, the 2-fibre product of `xf` and `yf` is
equivalent over the site to the category associated to an algebraic space over `S`. -/
private theorem exists_isAlgebraicSpace_equivalenceOver_sliceProduct
    (h₁ : HasRepresentableDiagonal B S hS 𝒳) (U V : BigFppfOver B S hS)
    (xf : Over U ⥤ 𝒳.val.obj) (yf : Over V ⥤ 𝒳.val.obj)
    (hxw : xf ⋙ 𝒳.val.p = Over.forget U) (hyw : yf ⋙ 𝒳.val.p = Over.forget V) :
    ∃ G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS G ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.structureFunctor (Over.forget U) (Over.forget V) 𝒳.val.p xf yf)
        (discreteProjection G)) := by
  have hpZ : (TwoFibreProductOver.structureFunctor (Over.forget U) (Over.forget V) (𝟭 _)
      (Over.forget U) (Over.forget V)).IsFiberedInGroupoids :=
    isFiberedInGroupoids_structureFunctor_id _ _ (Functor.IsFiberedInGroupoids.over_forget U)
      (Functor.IsFiberedInGroupoids.over_forget V)
  have hte : (Over.iteratedSliceBackward (U ⨯ V) ⋙
      TwoFibreProductOver.sliceProd U V).IsEquivalence :=
    isEquivalence_comp' _ _ (Over.iteratedSliceEquiv (U ⨯ V)).symm.isEquivalence_functor
      (TwoFibreProductOver.instIsEquivalenceSliceProd U V)
  have hcmp := TwoFibreProductOver.isEquivalence_precomposeFst
    (Over.map (U ⨯ V).hom)
    (TwoFibreProductOver.structureFunctor (Over.forget U) (Over.forget V) (𝟭 _)
      (Over.forget U) (Over.forget V))
    𝒳.val.p (ProdP 𝒳.val.p)
    (TwoFibreProductOver.prodMap xf yf hxw hyw) (Diag 𝒳.val.p)
    (Over.iteratedSliceBackward (U ⨯ V) ⋙ TwoFibreProductOver.sliceProd U V) rfl
    𝒳.isFiberedInGroupoids (Functor.IsFiberedInGroupoids.over_map (U ⨯ V).hom) hpZ hte rfl
  obtain ⟨F, hF, ⟨e⟩⟩ := h₁ (U ⨯ V)
    ((Over.iteratedSliceBackward (U ⨯ V) ⋙ TwoFibreProductOver.sliceProd U V) ⋙
      TwoFibreProductOver.prodMap xf yf hxw hyw) rfl
  obtain ⟨G, hG, ⟨e'⟩⟩ := exists_isAlgebraicSpace_equivalenceOver_comp_overMap B S hS (U ⨯ V)
    (TwoFibreProductOver.fst (Over.map (U ⨯ V).hom) 𝒳.val.p (ProdP 𝒳.val.p)
      ((Over.iteratedSliceBackward (U ⨯ V) ⋙ TwoFibreProductOver.sliceProd U V) ⋙
        TwoFibreProductOver.prodMap xf yf hxw hyw) (Diag 𝒳.val.p)) hF e
  refine ⟨G, hG, ?_⟩
  have hQ₁ : (TwoFibreProductOver.structureFunctor (Over.map (U ⨯ V).hom) 𝒳.val.p
      (ProdP 𝒳.val.p)
      ((Over.iteratedSliceBackward (U ⨯ V) ⋙ TwoFibreProductOver.sliceProd U V) ⋙
        TwoFibreProductOver.prodMap xf yf hxw hyw) (Diag 𝒳.val.p)).IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _
      (Functor.IsFiberedInGroupoids.over_map (U ⨯ V).hom) 𝒳.isFiberedInGroupoids
      (isFiberedInGroupoids_structureFunctor_id _ _ 𝒳.isFiberedInGroupoids
        𝒳.isFiberedInGroupoids)
      rfl rfl
  have hTgt : (TwoFibreProductOver.structureFunctor (Over.forget U) (Over.forget V) 𝒳.val.p
      xf yf).IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids (Over.forget U) (Over.forget V) 𝒳.val.p xf yf
      (Functor.IsFiberedInGroupoids.over_forget U) (Functor.IsFiberedInGroupoids.over_forget V)
      𝒳.isFiberedInGroupoids hxw hyw
  obtain ⟨k⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence hQ₁ hTgt
    (TwoFibreProductOver.precomposeFst (Over.map (U ⨯ V).hom)
        (TwoFibreProductOver.structureFunctor (Over.forget U) (Over.forget V) (𝟭 _)
          (Over.forget U) (Over.forget V))
        𝒳.val.p (ProdP 𝒳.val.p) (TwoFibreProductOver.prodMap xf yf hxw hyw) (Diag 𝒳.val.p)
        (Over.iteratedSliceBackward (U ⨯ V) ⋙ TwoFibreProductOver.sliceProd U V) rfl ⋙
      TwoFibreProductOver.prodDiagComparison xf yf hxw hyw) rfl
    (isEquivalence_comp' _ _ hcmp
      (TwoFibreProductOver.instIsEquivalenceProdDiagComparison xf yf hxw hyw))
  exact ⟨k.symm.trans
    (StacksRepresentableCFG.EquivalenceOver.ofEq TwoFibreProductOver.fst_comp_eq e')⟩

/-- **Stacks 045G, condition (1) implies condition (4).** If the diagonal of `𝒳` is representable
by algebraic spaces, then the 2-fibre product over `𝒳` of any two scheme-valued points of `𝒳` is
representable by an algebraic space over `S`. -/
theorem hasAlgebraicSpaceSchemePointProducts_of_hasRepresentableDiagonal
    (h₁ : HasRepresentableDiagonal B S hS 𝒳) :
    HasAlgebraicSpaceSchemePointProducts B S hS 𝒳 := fun U V x y =>
  exists_isAlgebraicSpace_equivalenceOver_sliceProduct B S hS 𝒳 h₁ U V
    x.toFunctor y.toFunctor x.w y.w

/-- **Stacks 045G, condition (2) implies condition (3).** Algebraicity of all isomorphism sheaves
implies that every 1-morphism to `𝒳` from the category represented by a scheme over `S` is
representable by algebraic spaces. -/
theorem isRepresentableFromSchemes_of_isAlgebraicSpaceIsomPresheaf
    (h₂ : IsAlgebraicSpaceIsomPresheaf B S hS 𝒳) :
    IsRepresentableFromSchemes B S hS 𝒳 :=
  (isRepresentableFromSchemes_iff_hasAlgebraicSpaceSchemePointProducts B S hS 𝒳).2
    (hasAlgebraicSpaceSchemePointProducts_of_hasRepresentableDiagonal B S hS 𝒳
      ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).2 h₂))

end AlgebraicGeometry.Stack

end
