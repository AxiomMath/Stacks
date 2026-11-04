module

public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.UnderlyingTwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex

/-!
# The relative dimension of Stacks 0DRL is unchanged by a 2-isomorphism of the 1-morphism

The relative dimension `AlgebraicGeometry.Stack.relativeStackDimensionAt` of **Stacks 0DRL** is
an infimum over the fibres `𝒯 ×_𝒳 Spec k` of a 1-morphism `f : 𝒯 ⟶ 𝒳` taken at the *canonical*
2-fibre product of Stacks 04T2, so its definition mentions `f` on the nose. The relative
dimension at a point nevertheless depends on the 1-morphism only up to 2-isomorphism.

## Main results

* `AlgebraicGeometry.Stack.relativeStackDimensionAt_congr_twoIso`: for `θ : f ≅ f'` the relative
  dimensions of `f` and of `f'` agree at every point of `|𝒯|`.
* `AlgebraicGeometry.Stack.relativeStackDimensionAt_comp_of_isMonomorphism_of_twoIso`:
  **postcomposing with a monomorphism does not change the relative dimension**, in the form in
  which the factorisation is only 2-isomorphic to the given 1-morphism.

## Implementation notes

Both local-finite-type witnesses are carried, since each side of the conclusion needs its own;
no transport of that property along `θ` is used or proved here.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04ZW](https://stacks.math.columbia.edu/tag/04ZW)
* [Stacks Project, Tag 0DRL](https://stacks.math.columbia.edu/tag/0DRL)
* [Stacks Project, Tag 0DRM](https://stacks.math.columbia.edu/tag/0DRM)
-/


@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The relative dimension of Stacks 0DRL is unchanged by a 2-isomorphism of the 1-morphism.**
If `θ : f ≅ f'` is an invertible 2-morphism of 1-morphisms `𝒯 ⟶ 𝒳`, locally of finite type, of
locally Noetherian algebraic stacks over `S`, then `f` and `f'` have the same relative dimension
at every point `t ∈ |𝒯|`. -/
theorem relativeStackDimensionAt_congr_twoIso {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS}
    {f f' : 𝒯 ⟶ 𝒳} (θ : f ≅ f')
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (hf' : AlgebraicStacks.IsLocallyOfFiniteType B S hS f')
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (t : points B S hS 𝒯.val.val 𝒯.val.property) :
    relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t =
      relativeStackDimensionAt.{u, w} B S hS f' hf' h𝒯 h𝒳 t := by
  classical
  set p := Quotient.out
    (pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒳.val.property f.hom.hom t) with hpdef
  have hp : pointClass B S hS 𝒳.val.val 𝒳.val.property p =
      pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒳.val.property f.hom.hom t := Quotient.out_eq _
  have hp' : pointClass B S hS 𝒳.val.val 𝒳.val.property p =
      pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒳.val.property f'.hom.hom t :=
    hp.trans (congrFun (pointsMap_eq_of_basedNatTrans B S hS 𝒯.val.val 𝒯.val.property
      𝒳.val.property θ.hom.hom.hom) t)
  obtain ⟨q, hq⟩ := exists_point_fieldFibreStackSquare.{u, w} B S hS f t p hp
  have hR := Bicategory.isTwoFibreProduct_swap
    (isTwoFibreProduct_underlying_algebraicStacks B S hS (fieldFibreStackSquare B S hS f p)
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
        (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p) f))
  have hRN := isLocallyNoetherianStack_fieldFibreStackSquare.{u, w} B S hS f hf p
  refine (dimensionAtPoint_eq_relativeStackDimensionAt_of_isTwoFibreProduct.{u, w} B S hS f hf
      h𝒯 h𝒳 t p hp hR (fieldFibreStackSquare B S hS f p).pt.property hRN q hq).symm.trans ?_
  exact dimensionAtPoint_eq_relativeStackDimensionAt_of_isTwoFibreProduct.{u, w} B S hS f' hf'
    h𝒯 h𝒳 t p hp'
    (hR := Bicategory.isTwoFibreProduct_reindexFst
      (Bicategory.InducedBicategory.isoHom θ) hR)
    (fieldFibreStackSquare B S hS f p).pt.property hRN q hq

/-- **Postcomposing with a monomorphism does not change the relative dimension of Stacks 0DRL**,
up to a 2-isomorphism. Let `g : 𝒯 ⟶ 𝒵` and `i : 𝒵 ⟶ 𝒳` be 1-morphisms of locally Noetherian
algebraic stacks over `S` with `i` a monomorphism (Stacks 04ZW), and let `f : 𝒯 ⟶ 𝒳` be
*2-isomorphic* to `g ≫ i`, with `f`, `g` and `g ≫ i` locally of finite type. Then `f` and `g` have
the same relative dimension at every `t ∈ |𝒯|`. -/
theorem relativeStackDimensionAt_comp_of_isMonomorphism_of_twoIso
    {𝒯 𝒵 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳) (g : 𝒯 ⟶ 𝒵) (i : 𝒵 ⟶ 𝒳)
    (θ : f ≅ g ≫ i)
    (hi : AlgebraicStacks.IsMonomorphism B S hS i)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (hg : AlgebraicStacks.IsLocallyOfFiniteType B S hS g)
    (hgi : AlgebraicStacks.IsLocallyOfFiniteType B S hS (g ≫ i))
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒵 : IsLocallyNoetherianStack.{u, w} B S hS 𝒵)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (t : points B S hS 𝒯.val.val 𝒯.val.property) :
    relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t =
      relativeStackDimensionAt.{u, w} B S hS g hg h𝒯 h𝒵 t :=
  (relativeStackDimensionAt_congr_twoIso.{u, w} B S hS θ hf hgi h𝒯 h𝒳 t).trans
    (relativeStackDimensionAt_comp_of_isMonomorphism.{u, w} B S hS g i hi hg hgi h𝒯 h𝒵 h𝒳 t)

end AlgebraicGeometry.Stack

end
