module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ProductMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyEquivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids

/-!
# A relative property stable under composition is stable under products (Stacks 045E)

Let `P` be a property of morphisms of algebraic spaces over `S` which is stable under base
change, local on the target for the fppf precoverage, and stable under composition. If two
1-morphisms `f₁ : 𝒳₁ ⟶ 𝒴₁`, `f₂ : 𝒳₂ ⟶ 𝒴₂` of categories fibred in groupoids over the big fppf
site of `S` are representable by algebraic spaces and have the relative property `P` of
Stacks 03YK, then so does their product `f₁ × f₂` of Stacks 0303.

The argument is the one of Stacks 0303 with representability replaced by the relative property
throughout: `f₁ × f₂` factors as `(f₁ × id) ∘ (id × f₂)`, each factor is a base change of the
corresponding `fᵢ` along a projection of a product, so Stacks 045C applies, and the composite is
handled by Stacks 045B.

## Main results

* `AlgebraicGeometry.Stack.hasRelativeProperty_productMap`: **Stacks 045E**.

## Implementation notes

The base change is the one of `AlgebraicGeometry.Stack.productCancelIso`: the iterated 2-fibre
product `(𝒵 × 𝒴) ×_{pr₂, 𝒴, f} 𝒳` is `𝒵 × 𝒳` compatibly with `id × f`. The 2-fibre product
square itself is main's `CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare` together
with `CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare`, so no square
has to be shown terminal here; Stacks 045C is applied to it, and Stacks 0459 then carries the
conclusion across the comparison.

Everything is stated at the universe pattern
`CategoryTheory.CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}` of
Stacks 045C, which is the closure of `{u, v, u + 1, w}` under forming 2-fibre products — and
also under forming products, so `𝒳₁ × 𝒳₂` stays inside it. That constraint is inherited from
Stacks 045C (`AlgebraicGeometry.Stack.hasRelativeProperty_baseChange`), which carries the
`@[stacks 045C]` attribute at the same pattern and which this statement consumes; it is not an
artefact of this file. The projection `pr₂ : 𝒵 × 𝒴 ⟶ 𝒴` is a 1-morphism of the 2-category only
because of that closure — at a general pattern a product has a larger morphism and object
universe than its factors, and only its `CategoryTheory.BasedFunctor` form exists.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 0303](https://stacks.math.columbia.edu/tag/0303)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 045E](https://stacks.math.columbia.edu/tag/045E)
* [Stacks Project, Tag 0459](https://stacks.math.columbia.edu/tag/0459)
-/

@[expose] public section

open CategoryTheory CategoryTheory.CatFiberedInGroupoids

namespace AlgebraicGeometry.Stack

universe u v w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (P : MorphismProperty (AlgebraicSpaces B S hS))
  [P.IsStableUnderBaseChange]
  [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, t} B S hS)]

section

variable {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
  (BigFppfOver B S hS)}

/-- The second projection of a product, as a 1-morphism of the 2-category of categories fibred
in groupoids over the big fppf site of `S`. This is available at the universe pattern of
Stacks 045C because that pattern is closed under forming products. -/
def productSndHom (𝒵 𝒴 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
    (BigFppfOver B S hS)) : product 𝒵 𝒴 ⟶ 𝒴 :=
  Bicategory.InducedBicategory.mkHom (productSnd B S hS 𝒵 𝒴)

/-- The identity based functor of a product is an equivalence. -/
private theorem isEquivalence_basedFunctor_id_product (𝒵 𝒴 : CatFiberedInGroupoids.{u, max u v,
    u + 1, max (max (u + 1) w) v} (BigFppfOver B S hS)) :
    Functor.IsEquivalence (BasedFunctor.id (product 𝒵 𝒴).val).toFunctor :=
  inferInstanceAs (Functor.IsEquivalence (𝟭 (product 𝒵 𝒴).val.obj))

/-- **Stacks 045E when the first factor is an identity.** `id_𝒵 × f` is a base change of `f`
along `pr₂ : 𝒵 × 𝒴 ⟶ 𝒴`, so it has the relative property `P` whenever `f` does, by Stacks 045C
and Stacks 0459. -/
theorem hasRelativeProperty_productMap_id_left (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hPf : HasRelativeProperty.{u, _, _, t} B S hS P f hf) :
    HasRelativeProperty.{u, _, _, t} B S hS P (productMap (𝟙 𝒵) f)
      (isRepresentableByAlgebraicSpaces_productMap_id_left B S hS f hf) := by
  have hsq := isTwoFibreProduct_twoFibreProductSquare (productSndHom B S hS 𝒵 𝒴) f
  have h045C := hasRelativeProperty_baseChange.{u, v, w, t} B S hS P 𝒳 𝒴 (product 𝒵 𝒴) f
    (productSndHom B S hS 𝒵 𝒴) (twoFibreProductSquare (productSndHom B S hS 𝒵 𝒴) f) hsq hf hPf
  have hid := isEquivalence_basedFunctor_id_product.{u, v, w} B S hS 𝒵 𝒴
  have hce : Functor.IsEquivalence (productCancel B S hS (𝒵 := 𝒵) f).toFunctor :=
    isEquivalence_productCancel B S hS f
  exact (@hasRelativeProperty_iff_of_equivalences B S hS _ _ _ _ P _ _
    (twoFibreProductSquare (productSndHom B S hS 𝒵 𝒴) f).fst (productMap (𝟙 𝒵) f)
    (productCancel B S hS (𝒵 := 𝒵) f) (BasedFunctor.id (product 𝒵 𝒴).val)
    (productCancelIso B S hS (𝒵 := 𝒵) f) hce hid
    (isRepresentableByAlgebraicSpaces_productMap_id_left B S hS f hf)).mpr h045C

/-- **Stacks 045E when the second factor is an identity**, obtained from
`AlgebraicGeometry.Stack.hasRelativeProperty_productMap_id_left` by exchanging the two
factors. -/
theorem hasRelativeProperty_productMap_id_right (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hPf : HasRelativeProperty.{u, _, _, t} B S hS P f hf) :
    HasRelativeProperty.{u, _, _, t} B S hS P (productMap f (𝟙 𝒵))
      (isRepresentableByAlgebraicSpaces_productMap_id_right B S hS f hf) :=
  (hasRelativeProperty_iff_of_equivalences B S hS P (productMap f (𝟙 𝒵))
    (productMap (𝟙 𝒵) f) (productSwap 𝒳 𝒵).hom (productSwap 𝒴 𝒵).hom
    (productSwapMapIso f (𝟙 𝒵))
    (isRepresentableByAlgebraicSpaces_productMap_id_left B S hS f hf)).mp
    (hasRelativeProperty_productMap_id_left B S hS P f hf hPf)

end

section

variable [P.IsStableUnderComposition]
  {𝒳₁ 𝒳₂ 𝒴₁ 𝒴₂ : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
    (BigFppfOver B S hS)}

/-- **Stacks 045E.** A property of morphisms of algebraic spaces over `S` which is stable under
base change, local on the target for the fppf precoverage and stable under composition, and which
holds relatively for two 1-morphisms of categories fibred in groupoids over the big fppf site of
`S` representable by algebraic spaces, holds relatively for their product.

The product factors as `(f₁ × id_{𝒳₂}) ∘ (id_{𝒴₁} × f₂)`; the two factors are handled by
`AlgebraicGeometry.Stack.hasRelativeProperty_productMap_id_right` and `…_id_left`, and the
composite by Stacks 045B. -/
@[stacks 045E]
theorem hasRelativeProperty_productMap (f₁ : 𝒳₁ ⟶ 𝒴₁) (f₂ : 𝒳₂ ⟶ 𝒴₂)
    (hf₁ : IsRepresentableByAlgebraicSpaces B S hS f₁.hom)
    (hf₂ : IsRepresentableByAlgebraicSpaces B S hS f₂.hom)
    (hP₁ : HasRelativeProperty.{u, _, _, t} B S hS P f₁ hf₁)
    (hP₂ : HasRelativeProperty.{u, _, _, t} B S hS P f₂ hf₂) :
    HasRelativeProperty.{u, _, _, t} B S hS P (productMap f₁ f₂)
      (isRepresentableByAlgebraicSpaces_productMap B S hS f₁ f₂ hf₁ hf₂) := by
  have hcomp := hasRelativeProperty_comp B S hS P
    (productMap f₁ (𝟙 𝒳₂)) (productMap (𝟙 𝒴₁) f₂)
    (isRepresentableByAlgebraicSpaces_productMap_id_right B S hS f₁ hf₁)
    (isRepresentableByAlgebraicSpaces_productMap_id_left B S hS f₂ hf₂)
    (hasRelativeProperty_productMap_id_right B S hS P f₁ hf₁ hP₁)
    (hasRelativeProperty_productMap_id_left B S hS P f₂ hf₂ hP₂)
  have h₁ := isEquivalence_basedFunctor_id_product.{u, v, w} B S hS 𝒳₁ 𝒳₂
  have h₂ := isEquivalence_basedFunctor_id_product.{u, v, w} B S hS 𝒴₁ 𝒴₂
  refine (hasRelativeProperty_iff_of_equivalences B S hS P (productMap f₁ f₂)
    (productMap f₁ (𝟙 𝒳₂) ≫ productMap (𝟙 𝒴₁) f₂)
    (BasedFunctor.id (product 𝒳₁ 𝒳₂).val) (BasedFunctor.id (product 𝒴₁ 𝒴₂).val) ?_ _).mp hcomp
  refine productNatIso _ _ (Iso.refl _) (Iso.refl _) ?_ ?_ <;> intro x
  · exact IsHomLift.id (BasedFunctor.w_obj (BasedFunctor.comp
      (BasedFunctor.comp (BasedFunctor.id (product 𝒳₁ 𝒳₂).val)
        (productMap f₁ (𝟙 𝒳₂) ≫ productMap (𝟙 𝒴₁) f₂).hom)
      ⟨TwoFibreProductOver.fst 𝒴₁.val.p 𝒴₂.val.p (𝟭 (BigFppfOver B S hS)) 𝒴₁.val.p 𝒴₂.val.p,
        TwoFibreProductOver.fst_comp_eq⟩) x)
  · exact IsHomLift.id (BasedFunctor.w_obj (BasedFunctor.comp
      (BasedFunctor.comp (BasedFunctor.id (product 𝒳₁ 𝒳₂).val)
        (productMap f₁ (𝟙 𝒳₂) ≫ productMap (𝟙 𝒴₁) f₂).hom)
      ⟨TwoFibreProductOver.snd 𝒴₁.val.p 𝒴₂.val.p (𝟭 (BigFppfOver B S hS)) 𝒴₁.val.p 𝒴₂.val.p,
        TwoFibreProductOver.snd_comp_eq⟩) x)

end

end AlgebraicGeometry.Stack

end
