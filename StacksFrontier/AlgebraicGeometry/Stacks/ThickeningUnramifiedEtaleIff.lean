module

public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningEtaleDeformationProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedEtaleDiagramForward

/-!
# Unramifiedness and étaleness along a thickening of algebraic stacks (Stacks 0CJC, (8), (9))

Consider the commutative diagram of thickenings of algebraic stacks over `S` of **Stacks 0CJC**:
`(𝒳 ⊂ 𝒳') ⟶ (𝒴 ⊂ 𝒴')` over a thickening `ℬ ⊂ ℬ'`, with `𝒴' ⟶ ℬ'` locally of finite type,
`𝒳' ⟶ ℬ'` flat and locally of finite presentation, and `𝒳`, `𝒴` the base changes of `𝒳'`,
`𝒴'` to `ℬ`. Items (8) and (9) say that `f` is unramified, resp. étale, if and only if `f'` is.

`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningEtaleDeformationProperties` proves the
implication from `f` to `f'` and the converse from the étale diagram test of condition (2) of
Stacks 0CIY on `f'`. That test now follows from unramifiedness, resp. étaleness, of `f'`
(`AlgebraicGeometry.Stack.isUnramifiedOnEveryEtaleDiagram_of_isUnramified` and
`AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleDiagram_isEtale_of_isEtale`), so both items hold.

## Main results

* `AlgebraicGeometry.Stack.isUnramified_iff_isUnramified_ambient`: **Stacks 0CJC**, item (8).
* `AlgebraicGeometry.Stack.isEtale_iff_isEtale_ambient`: **Stacks 0CJC**, item (9).
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {ℬ ℬ' 𝒴' 𝒳' : AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 0CJC, unramified.** Under the hypotheses of
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_iff_isFlat_ambient`, the restricted 1-morphism
`f` is unramified if and only if the ambient 1-morphism `f'` is unramified. -/
@[stacks 0CJC "unramified"]
theorem isUnramified_iff_isUnramified_ambient
    {iB : ℬ ⟶ ℬ'} {pX' : 𝒳' ⟶ ℬ'} {pY' : 𝒴' ⟶ ℬ'}
    {PX : Bicategory.TwoCommSq pX' iB} {PY : Bicategory.TwoCommSq pY' iB}
    {f : PX.pt ⟶ PY.pt} {f' : 𝒳' ⟶ 𝒴'}
    (hiB : IsThickening iB)
    (hcartX : Bicategory.IsTwoFibreProduct PX) (hcartY : Bicategory.IsTwoFibreProduct PY)
    (houter : f' ≫ pY' ≅ pX')
    (hrestrict : f ≫ PY.fst ≅ PX.fst ≫ f')
    (hinner : f ≫ PY.snd ≅ PX.snd)
    (hcoh : Bicategory.whiskerLeft f PY.iso.hom ≫ Bicategory.whiskerRight hinner.hom iB =
      Bicategory.whiskerRight hrestrict.hom pY' ≫
        Bicategory.whiskerLeft PX.fst houter.hom ≫ PX.iso.hom)
    (hYft : AlgebraicStacks.IsLocallyOfFiniteType B S hS pY')
    (hXflat : AlgebraicStacks.IsFlat B S hS pX')
    (hXfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS pX') :
    IsUnramified B S hS f ↔ IsUnramified B S hS f' :=
  ⟨isUnramified_ambient_of_isUnramified B S hS hiB hcartX hcartY houter hrestrict hinner hcoh
      hYft hXflat hXfp,
    fun hf' => isUnramified_restricted_of_isUnramifiedOnEveryEtaleDiagram B S hS hcartX hcartY
      houter hrestrict hinner hcoh (isUnramifiedOnEveryEtaleDiagram_of_isUnramified B S hS hf')⟩

/-- **Stacks 0CJC, étale.** Under the hypotheses of
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_iff_isFlat_ambient`, the restricted 1-morphism
`f` is étale if and only if the ambient 1-morphism `f'` is étale. -/
@[stacks 0CJC "etale"]
theorem isEtale_iff_isEtale_ambient
    {iB : ℬ ⟶ ℬ'} {pX' : 𝒳' ⟶ ℬ'} {pY' : 𝒴' ⟶ ℬ'}
    {PX : Bicategory.TwoCommSq pX' iB} {PY : Bicategory.TwoCommSq pY' iB}
    {f : PX.pt ⟶ PY.pt} {f' : 𝒳' ⟶ 𝒴'}
    (hiB : IsThickening iB)
    (hcartX : Bicategory.IsTwoFibreProduct PX) (hcartY : Bicategory.IsTwoFibreProduct PY)
    (houter : f' ≫ pY' ≅ pX')
    (hrestrict : f ≫ PY.fst ≅ PX.fst ≫ f')
    (hinner : f ≫ PY.snd ≅ PX.snd)
    (hcoh : Bicategory.whiskerLeft f PY.iso.hom ≫ Bicategory.whiskerRight hinner.hom iB =
      Bicategory.whiskerRight hrestrict.hom pY' ≫
        Bicategory.whiskerLeft PX.fst houter.hom ≫ PX.iso.hom)
    (hYft : AlgebraicStacks.IsLocallyOfFiniteType B S hS pY')
    (hXflat : AlgebraicStacks.IsFlat B S hS pX')
    (hXfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS pX') :
    IsEtale B S hS f ↔ IsEtale B S hS f' :=
  ⟨isEtale_ambient_of_isEtale B S hS hiB hcartX hcartY houter hrestrict hinner hcoh
      hYft hXflat hXfp,
    fun hf' => isEtale_restricted_of_etaleDiagram B S hS hiB hcartX hcartY houter hrestrict
      hinner hcoh hf'.1 (hasPropertyOnEveryEtaleDiagram_isEtale_of_isEtale B S hS hf')⟩

end AlgebraicGeometry.Stack

end
