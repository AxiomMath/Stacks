module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.CategoricalPullbackSquareDiagonal
public import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedFunctor

/-!
# 2-cartesianness of a square only depends on the square up to equivalence

A 2-commutative square of categories
```
      a
  C' ---> C
  |       |
u |       | p
  v       v
  D' ---> D
      b
```
with filler `α : a ⋙ p ≅ u ⋙ b` is 2-cartesian when its comparison functor
`CategoryTheory.Limits.CategoricalPullback.squareComparison` into the explicit 2-fibre product
`p ⊡ b` of Stacks 003R is an equivalence. This file proves that the property only depends on the
square up to equivalence of its cospan: if a second square over the same `a` is obtained from the
first by replacing `D'` and `D` by equivalent categories — compatibly with the three functors and
the filler — then the two comparison functors are equivalences together.

The transfer functor between the two explicit 2-fibre products is
`CategoryTheory.Limits.CategoricalPullback.map` (Stacks 02XA) on the identity of `C` and the two
comparison functors, and it is an equivalence by Stacks 02XB (3)
(`CategoryTheory.induced_isEquivalence_of_isEquivalence`); over it, the two comparison functors
agree up to a natural isomorphism whose first component is the identity and whose second is the
comparison of the two left legs. The single coherence hypothesis `hα` is the only mathematical
input: it says that the filler of the second square is the filler of the first read through the
three comparisons.

This is the "full equivalence-invariance of the notion" that Mathlib's
`Mathlib/CategoryTheory/Limits/Shapes/Pullback/Categorical/Basic.lean` lists as missing.

## Main definitions

* `CategoryTheory.Limits.CategoricalPullback.squareTransfer`: the functor `p₁ ⊡ b₁ ⥤ p₂ ⊡ b₂`
  induced by the two comparisons.

## Main results

* `CategoryTheory.Limits.CategoricalPullback.squareComparisonTransferIso`: the comparison of the
  first square, followed by the transfer, is the comparison of the second.
* `CategoryTheory.Limits.CategoricalPullback.essSurj_squareComparison_iff_of_transfer`: the two
  comparisons are essentially surjective together.
* `CategoryTheory.Limits.CategoricalPullback.isEquivalence_squareComparison_iff_of_transfer`: the
  two squares are 2-cartesian together.

## References

* [Stacks Project, Tag 003R](https://stacks.math.columbia.edu/tag/003R)
* [Stacks Project, Tag 02XA](https://stacks.math.columbia.edu/tag/02XA)
* [Stacks Project, Tag 02XB](https://stacks.math.columbia.edu/tag/02XB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits.CategoricalPullback

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {C' : Type u₁} {C : Type u₂} {D₁' : Type u₃} {D₁ : Type u₄}
  {D₂' : Type u₅} {D₂ : Type u₆}
  [Category.{v₁} C'] [Category.{v₂} C] [Category.{v₃} D₁'] [Category.{v₄} D₁]
  [Category.{v₅} D₂'] [Category.{v₆} D₂]
  (a : C' ⥤ C) (u₁ : C' ⥤ D₁') (p₁ : C ⥤ D₁) (b₁ : D₁' ⥤ D₁) (α₁ : a ⋙ p₁ ≅ u₁ ⋙ b₁)
  (u₂ : C' ⥤ D₂') (p₂ : C ⥤ D₂) (b₂ : D₂' ⥤ D₂) (α₂ : a ⋙ p₂ ≅ u₂ ⋙ b₂)
  (K : D₁' ⥤ D₂') (M : D₁ ⥤ D₂)
  (iu : u₁ ⋙ K ≅ u₂) (ip : p₁ ⋙ M ≅ p₂) (ib : K ⋙ b₂ ≅ b₁ ⋙ M)

/-- **The transfer functor between the two explicit 2-fibre products.** It is
`CategoryTheory.Limits.CategoricalPullback.map` (Stacks 02XA) on the identity of `C`, the
comparison `K` of the lower left corners and the comparison `M` of the lower right ones. -/
def squareTransfer : p₁ ⊡ b₁ ⥤ p₂ ⊡ b₂ :=
  CategoricalPullback.map p₁ b₁ (𝟭 C) K M p₂ b₂ ib ip

/-- **The transfer functor is an equivalence** when the two comparisons of the lower corners are:
this is Stacks 02XB (3), the identity of `C` being an equivalence. Fullness and faithfulness of
`M` are all that is used of it. -/
instance isEquivalence_squareTransfer [K.IsEquivalence] [M.Full] [M.Faithful] :
    (squareTransfer p₁ b₁ p₂ b₂ K M ip ib).IsEquivalence :=
  induced_isEquivalence_of_isEquivalence (𝟭 C) K M ib ip

/-- **The comparison functor of a square is the comparison of any square equivalent to it.** The
isomorphism is the identity on the `C`-component and the comparison `K` of the left legs on the
other; the coherence hypothesis `hα` is exactly what its compatibility condition needs. -/
noncomputable def squareComparisonTransferIso
    (hα : ∀ x : C', α₂.hom.app x =
      ip.inv.app (a.obj x) ≫ M.map (α₁.hom.app x) ≫ ib.inv.app (u₁.obj x) ≫
        b₂.map (iu.hom.app x)) :
    squareComparison a u₁ p₁ b₁ α₁ ⋙ squareTransfer p₁ b₁ p₂ b₂ K M ip ib ≅
      squareComparison a u₂ p₂ b₂ α₂ :=
  NatIso.ofComponents
    (fun x => mkIso (Iso.refl _) (iu.app x) (by simp [squareTransfer, hα x]))
    (fun g => by
      refine CategoricalPullback.hom_ext ?_ ?_
      · simp [squareTransfer, mkIso]
      · exact iu.hom.naturality g)

/-- **Essential surjectivity of the comparison functor is invariant under equivalence of the
cospan.** The transfer functor is an equivalence, so the comparison of the second square is
essentially surjective exactly when that of the first is. -/
theorem essSurj_squareComparison_iff_of_transfer [K.IsEquivalence] [M.Full] [M.Faithful]
    (hα : ∀ x : C', α₂.hom.app x =
      ip.inv.app (a.obj x) ≫ M.map (α₁.hom.app x) ≫ ib.inv.app (u₁.obj x) ≫
        b₂.map (iu.hom.app x)) :
    (squareComparison a u₁ p₁ b₁ α₁).EssSurj ↔
      (squareComparison a u₂ p₂ b₂ α₂).EssSurj := by
  have e := squareComparisonTransferIso a u₁ p₁ b₁ α₁ u₂ p₂ b₂ α₂ K M iu ip ib hα
  constructor
  · intro _
    exact Functor.essSurj_of_iso e
  · intro _
    have := Functor.essSurj_of_iso e.symm
    exact Functor.essSurj_of_comp_fully_faithful (squareComparison a u₁ p₁ b₁ α₁)
      (squareTransfer p₁ b₁ p₂ b₂ K M ip ib)

/-- **2-cartesianness is invariant under equivalence of the cospan.** Two squares over the same
`a` whose lower corners are compared by an equivalence `K` and a fully faithful `M`, compatibly
with the legs and the fillers, are 2-cartesian together. -/
theorem isEquivalence_squareComparison_iff_of_transfer [K.IsEquivalence] [M.Full] [M.Faithful]
    (hα : ∀ x : C', α₂.hom.app x =
      ip.inv.app (a.obj x) ≫ M.map (α₁.hom.app x) ≫ ib.inv.app (u₁.obj x) ≫
        b₂.map (iu.hom.app x)) :
    (squareComparison a u₁ p₁ b₁ α₁).IsEquivalence ↔
      (squareComparison a u₂ p₂ b₂ α₂).IsEquivalence := by
  have e := squareComparisonTransferIso a u₁ p₁ b₁ α₁ u₂ p₂ b₂ α₂ K M iu ip ib hα
  constructor
  · intro _
    exact Functor.isEquivalence_of_iso e
  · intro _
    have := Functor.isEquivalence_of_iso e.symm
    exact Functor.isEquivalence_of_comp_right (squareComparison a u₁ p₁ b₁ α₁)
      (squareTransfer p₁ b₁ p₂ b₂ K M ip ib)

end CategoryTheory.Limits.CategoricalPullback

end
