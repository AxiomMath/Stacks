module

public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.Representability
public import StacksFrontier.CategoryTheory.FiberedCategory.RelocalizeAsElements
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceDescent

/-!
# Representability by an algebraic space over a smaller base scheme

Let `S` be a scheme contained in a big fppf site `B`, let `V` be a scheme over `S` and let
`q : 𝒟 ⥤ (Sch/V)_{fppf}` be a category fibred in groupoids over the big fppf site of `V`.
Composing `q` with the localization functor `CategoryTheory.Over.map V.hom` views `𝒟` over the big
fppf site of `S`. The content of this file is that this changes nothing about representability:

> `q` is equivalent over the site of `V` to the category of elements of an algebraic space over `V`
> if and only if `q ⋙ Over.map V.hom` is equivalent over the site of `S` to the category of
> elements of an algebraic space over `S`.

## Main results

* `AlgebraicGeometry.Stack.exists_isAlgebraicSpace_equivalenceOver_comp_overMap`: the forward
  direction.
* `AlgebraicGeometry.Stack.exists_isAlgebraicSpace_equivalenceOver_of_comp_overMap`: the backward
  direction, for `q` fibred in groupoids.
* `AlgebraicGeometry.Stack.exists_isAlgebraicSpace_equivalenceOver_comp_overMap_iff`: the two
  together.

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 00Y1](https://stacks.math.columbia.edu/tag/00Y1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.PresheafOfCategories

namespace AlgebraicGeometry.Stack

universe u v₂ u₂

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (V : BigFppfOver B S hS)

/-- The restriction to `V` of the presheaf of points of `V` as a scheme over `S` is an algebraic
space over `V`. -/
theorem isAlgebraicSpace_relocalizeRestrict_yoneda :
    IsAlgebraicSpace B V.left.1 V.left.2
      ((OverShriek.relocalizeRestrict V.hom).obj (yoneda.obj V)) := by
  have _ : HasPullbacks B.Schemes := inferInstance
  exact isAlgebraicSpace_of_iso B V.left.1 V.left.2
    (OverShriek.restrictYonedaIso V.hom V).symm
    (isAlgebraicSpace_yoneda B V.left.1 V.left.2 ((Over.pullback V.hom).obj V))

variable {𝒟 : Type u₂} [Category.{v₂} 𝒟] (q : 𝒟 ⥤ BigFppfOver B V.left.1 V.left.2)

/-- **Representability over `V` gives representability over `S`.** A category over the big fppf
site of `V` which is equivalent there to the category of elements of an algebraic space over `V`
is, viewed over the big fppf site of `S`, equivalent there to the category of elements of an
algebraic space over `S`. -/
theorem exists_isAlgebraicSpace_equivalenceOver_comp_overMap
    {F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B V.left.1 V.left.2 F)
    (e : StacksRepresentableCFG.EquivalenceOver q (discreteProjection F)) :
    ∃ G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS G ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver (q ⋙ Over.map V.hom)
        (discreteProjection G)) :=
  ⟨(OverShriek.relocalizePresheafFunctor V.hom).obj F,
    isAlgebraicSpace_viewOver B V.left.1 S V.left.2 hS V.hom F hF,
    ⟨(e.compRight (Over.map V.hom)).trans (relocalizeElementsEquivalenceOver V.hom F)⟩⟩

/-- **Representability over `S` gives representability over `V`.** If a category fibred in
groupoids over the big fppf site of `V`, viewed over the big fppf site of `S`, is equivalent
there to the category of elements of an algebraic space over `S`, then it is equivalent over the
big fppf site of `V` to the category of elements of an algebraic space over `V`. -/
theorem exists_isAlgebraicSpace_equivalenceOver_of_comp_overMap
    (hqf : q.IsFiberedInGroupoids)
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hG : IsAlgebraicSpace B S hS G)
    (e : StacksRepresentableCFG.EquivalenceOver (q ⋙ Over.map V.hom) (discreteProjection G)) :
    ∃ F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B V.left.1 V.left.2 F ∧
        Nonempty (StacksRepresentableCFG.EquivalenceOver q (discreteProjection F)) := by
  obtain ⟨F, τ, ι, π, ρ, hpb, hE⟩ :=
    exists_isPullback_nonempty_equivalenceOver_of_comp_overMap V.hom q hqf e
  have hH := isAlgebraicSpace_relocalizeRestrict_yoneda B S hS V
  exact ⟨F, isAlgebraicSpace_of_isPullback
    (isAlgebraicSpace_relocalizeRestrict B V.left.1 S V.left.2 hS V.hom G hG)
    (isAlgebraicSpace_yoneda B V.left.1 V.left.2 (Over.mk (𝟙 V.left)))
    hH.isSheaf hH.diagonal_representable hpb, hE⟩

/-- **Representability by an algebraic space does not depend on the base.** A category fibred in
groupoids over the big fppf site of `V` is equivalent there to the category of elements of an
algebraic space over `V` exactly when, viewed over the big fppf site of `S`, it is equivalent
there to the category of elements of an algebraic space over `S`. -/
theorem exists_isAlgebraicSpace_equivalenceOver_comp_overMap_iff (hqf : q.IsFiberedInGroupoids) :
    (∃ F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u,
        IsAlgebraicSpace B V.left.1 V.left.2 F ∧
          Nonempty (StacksRepresentableCFG.EquivalenceOver q (discreteProjection F))) ↔
      ∃ G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS G ∧
        Nonempty (StacksRepresentableCFG.EquivalenceOver (q ⋙ Over.map V.hom)
          (discreteProjection G)) := by
  constructor
  · rintro ⟨F, hF, ⟨e⟩⟩
    exact exists_isAlgebraicSpace_equivalenceOver_comp_overMap B S hS V q hF e
  · rintro ⟨G, hG, ⟨e⟩⟩
    exact exists_isAlgebraicSpace_equivalenceOver_of_comp_overMap B S hS V q hqf hG e

end AlgebraicGeometry.Stack

end
