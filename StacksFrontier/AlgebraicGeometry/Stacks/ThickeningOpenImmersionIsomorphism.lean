module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleStabilizerPreservingIsomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.FullyFaithfulMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothMonomorphismOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningDeformationPropertiesPointTest
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSurjective

/-!
# Isomorphisms and open immersions along a thickening of algebraic stacks (Stacks 0CJC)

Consider a commutative diagram of thickenings of algebraic stacks over `S`,
`(𝒳 ⊂ 𝒳') ⟶ (𝒴 ⊂ 𝒴')`, both over a thickening `iB : ℬ ⟶ ℬ'`, with `𝒴' ⟶ ℬ'` locally of finite
type, `𝒳' ⟶ ℬ'` flat and locally of finite presentation, and the two restricted stacks the base
changes of the ambient ones along `iB`. Items (2) and (3) of **Stacks 0CJC** say that the
restricted 1-morphism `f : 𝒳 ⟶ 𝒴` is an isomorphism, resp. an open immersion, exactly when the
ambient one `f' : 𝒳' ⟶ 𝒴'` is. This file proves both, and restates item (6), syntomic, with no
hypothesis beyond the source's.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isOpenImmersion_iff_isSmooth_and_isMonomorphism`: a
  1-morphism of algebraic stacks is an open immersion exactly when it is smooth and a
  monomorphism.
* `AlgebraicStacks.isEquivalence_iff_isSmooth_and_isMonomorphism_and_isSurjective`: a
  1-morphism of algebraic stacks is an isomorphism exactly when it is smooth, a monomorphism and
  surjective.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isEquivalence_iff_isEquivalence_ambient`:
  **Stacks 0CJC**, item (2), isomorphism.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isOpenImmersion_iff_isOpenImmersion_ambient`:
  **Stacks 0CJC**, item (3), open immersion.
* `AlgebraicGeometry.Stack.AlgebraicStacks.hasPropertyOnSomeSmoothDiagram_isSyntomic_iff_ambient`:
  **Stacks 0CJC**, item (6), syntomic.

## Implementation notes

An isomorphism of algebraic stacks is a 1-morphism which is an equivalence in the 2-category of
algebraic stacks; it is read here, as in **Stacks 0DUD**
(`AlgebraicGeometry.Stack.isEquivalence_of_isEtale_of_inducesIsomorphismAt`), as the underlying
functor `CatFiberedInGroupoids.homFunctor f.hom` being an equivalence of categories.

Both items are reduced to items of Stacks 0CJC that are already proved, rather than to the
chart argument of the source, which reads parts (3) and (4) of **Stacks 0CGX** off a tower of
charts whose top comparison is an equivalence.

An open immersion is the same as a smooth monomorphism. One direction is
`AlgebraicGeometry.Stack.AlgebraicStacks.isOpenImmersion_of_isSmooth_of_isMonomorphism`, the
algebraic-stack form of **Stacks 025G**; the other is that an open immersion is smooth
(`AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_of_isOpenImmersion`) and, being representable
by algebraic spaces with open immersions as representing morphisms, a monomorphism. So item (3)
is items (7) and (4) together,
`AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_iff_isSmooth_ambient` and
`AlgebraicGeometry.Stack.AlgebraicStacks.isMonomorphism_iff_isMonomorphism_ambient`.

An isomorphism is the same as a smooth surjective monomorphism. An equivalence is fully faithful,
hence representable by algebraic spaces (**Stacks 04Y5**, unconditional in this library as
`AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_faithful`) and a
monomorphism (**Stacks 04ZZ**); it is surjective on points, and smooth because postcomposing a
smooth presentation with an equivalence leaves it a smooth presentation. Conversely a smooth
monomorphism is an open immersion, hence étale (**Stacks 0CIP**) and universally injective, and
an étale, universally injective, surjective 1-morphism representable by algebraic spaces is an
isomorphism by **Stacks 05W5** in the form
`AlgebraicGeometry.Stack.isEquivalence_of_isEtale_of_universallyInjective_of_isSurjective`. So
item (2) is items (7) and (4) together with part (2) of **Stacks 0CJ9**,
`AlgebraicGeometry.Stack.isSurjective_inner_iff_outer`, read on the morphism of thickenings whose
ambient 1-morphism is `f'` and whose restricted one is `f`.

The syntomic statement on the base,
`AlgebraicGeometry.Stack.AlgebraicStacks.isSyntomic_iff_isSyntomic_ambient`, carries the source
and target locality of syntomic morphisms of algebraic spaces as two instance arguments. Both are
instances of this library (**Stacks 06F0** and **Stacks 0428**), so
`hasPropertyOnSomeSmoothDiagram_isSyntomic_iff_ambient` states the item with neither.

## References

* [Stacks Project, Tag 025G](https://stacks.math.columbia.edu/tag/025G)
* [Stacks Project, Tag 0428](https://stacks.math.columbia.edu/tag/0428)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
* [Stacks Project, Tag 04ZZ](https://stacks.math.columbia.edu/tag/04ZZ)
* [Stacks Project, Tag 05W5](https://stacks.math.columbia.edu/tag/05W5)
* [Stacks Project, Tag 06F0](https://stacks.math.columbia.edu/tag/06F0)
* [Stacks Project, Tag 0CIP](https://stacks.math.columbia.edu/tag/0CIP)
* [Stacks Project, Tag 0CJ9](https://stacks.math.columbia.edu/tag/0CJ9)
* [Stacks Project, Tag 0CJC](https://stacks.math.columbia.edu/tag/0CJC)
* [Stacks Project, Tag 0CGX](https://stacks.math.columbia.edu/tag/0CGX)
* [Stacks Project, Tag 0DUD](https://stacks.math.columbia.edu/tag/0DUD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CatFiberedInGroupoids
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Open immersions and isomorphisms as smooth monomorphisms -/

section Characterizations

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **An open immersion of algebraic stacks is a monomorphism.** Both notions are representability
by algebraic spaces together with a condition on the morphisms representing the base changes along
scheme-valued points, and an open immersion of algebraic spaces is a monomorphism. -/
theorem isMonomorphism_of_isOpenImmersion (f : 𝒳 ⟶ 𝒴) (hf : IsOpenImmersion B S hS f) :
    IsMonomorphism B S hS f :=
  ⟨hf.1, fun U y hy F hF he => (Space.mono_hom_iff_mono B S hS _).1
    (Space.mono_of_isOpenImmersion B S hS _ (hf.2 U y hy F hF he))⟩

/-- **A 1-morphism of algebraic stacks is an open immersion if and only if it is smooth and a
monomorphism.** The converse direction is
`AlgebraicGeometry.Stack.AlgebraicStacks.isOpenImmersion_of_isSmooth_of_isMonomorphism`, the
algebraic-stack form of Stacks 025G. -/
theorem isOpenImmersion_iff_isSmooth_and_isMonomorphism (f : 𝒳 ⟶ 𝒴) :
    IsOpenImmersion B S hS f ↔ IsSmooth B S hS f ∧ IsMonomorphism B S hS f :=
  ⟨fun hf => ⟨isSmooth_of_isOpenImmersion B S hS f hf,
      isMonomorphism_of_isOpenImmersion B S hS f hf⟩,
    fun hf => isOpenImmersion_of_isSmooth_of_isMonomorphism B S hS f hf.1 hf.2⟩

/-- **A monomorphism of algebraic stacks is universally injective.** It is representable by
algebraic spaces, every morphism representing one of its base changes is a monomorphism of
algebraic spaces, hence universally injective, and Stacks 0CI1 turns that into universal
injectivity of the 1-morphism. -/
theorem universallyInjective_of_isMonomorphism (f : 𝒳 ⟶ 𝒴) (hf : IsMonomorphism B S hS f) :
    UniversallyInjective B S hS f :=
  (representable_universallyInjective_iff B S hS f hf.1).1 fun U y hy T hT he =>
    Space.universallyInjective_of_mono B S hS _
      ((Space.mono_hom_iff_mono B S hS _).2 (hf.2 U y hy T hT he))

/-- **A 1-morphism of algebraic stacks is an isomorphism if and only if it is smooth, a
monomorphism and surjective.**

An equivalence is fully faithful, so it is representable by algebraic spaces (Stacks 04Y5) and a
monomorphism (Stacks 04ZZ); it is surjective on points, and it is smooth by
`AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_of_isEquivalence`, a smooth chart of the source
composed with it being a smooth chart of the target. Conversely a smooth
monomorphism is an open immersion (Stacks 025G), hence étale (Stacks 0CIP), and a monomorphism is
universally injective, so Stacks 05W5 for 1-morphisms representable by algebraic spaces applies. -/
theorem isEquivalence_iff_isSmooth_and_isMonomorphism_and_isSurjective (f : 𝒳 ⟶ 𝒴) :
    (CatFiberedInGroupoids.homFunctor f.hom).IsEquivalence ↔
      IsSmooth B S hS f ∧ IsMonomorphism B S hS f ∧ IsSurjective B S hS f :=
  ⟨fun hf => ⟨isSmooth_of_isEquivalence B S hS f hf,
      isMonomorphism_of_full_and_faithful B S hS f inferInstance inferInstance,
      surjective_pointsMap_of_isEquivalence B S hS f hf⟩,
    fun ⟨hsm, hmono, hsurj⟩ =>
      isEquivalence_of_isEtale_of_universallyInjective_of_isSurjective B S hS f hmono.1
        (isEtale_of_isOpenImmersion B S hS f
          (isOpenImmersion_of_isSmooth_of_isMonomorphism B S hS f hsm hmono))
        (universallyInjective_of_isMonomorphism B S hS f hmono) hsurj⟩

end Characterizations

/-! ### The clauses of Stacks 0CJC -/

variable {ℬ ℬ' 𝒴' 𝒳' : AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 0CJC, isomorphism.** For a commutative diagram of thickenings of algebraic stacks over
`S` over a thickening `iB : ℬ ⟶ ℬ'` of bases, with `𝒴' ⟶ ℬ'` locally of finite type, `𝒳' ⟶ ℬ'`
flat and locally of finite presentation and the two restricted stacks the base changes of the
ambient ones along `iB`, the restricted 1-morphism `f` is an isomorphism if and only if the
ambient 1-morphism `f'` is. -/
@[stacks 0CJC "isomorphism"]
theorem isEquivalence_iff_isEquivalence_ambient
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
    (hYft : IsLocallyOfFiniteType B S hS pY')
    (hXflat : IsFlat B S hS pX')
    (hXfp : IsLocallyOfFinitePresentation B S hS pX') :
    (CatFiberedInGroupoids.homFunctor f.hom).IsEquivalence ↔
      (CatFiberedInGroupoids.homFunctor f'.hom).IsEquivalence := by
  have hiX : Stack.IsThickening PX.fst :=
    Stack.isThickening_baseChange B S hS iB pX' PX.swap
      (Bicategory.isTwoFibreProduct_swap hcartX) hiB
  have hiY : Stack.IsThickening PY.fst :=
    Stack.isThickening_baseChange B S hS iB pY' PY.swap
      (Bicategory.isTwoFibreProduct_swap hcartY) hiB
  rw [isEquivalence_iff_isSmooth_and_isMonomorphism_and_isSurjective,
    isEquivalence_iff_isSmooth_and_isMonomorphism_and_isSurjective,
    isSmooth_iff_isSmooth_ambient B S hS hiB hcartX hcartY houter hrestrict hinner hcoh hYft
      hXflat hXfp,
    isMonomorphism_iff_isMonomorphism_ambient B S hS hiB hcartX hcartY houter hrestrict hinner
      hcoh hYft hXflat hXfp,
    Stack.isSurjective_inner_iff_outer
      ({ outer := f', inner := f, comm := hrestrict } :
        Stack.ThickeningMorphism PX.fst PY.fst hiX hiY)]

/-- **Stacks 0CJC, open immersion.** Under the hypotheses of
`AlgebraicGeometry.Stack.AlgebraicStacks.isEquivalence_iff_isEquivalence_ambient`, the restricted
1-morphism `f` is an open immersion if and only if the ambient 1-morphism `f'` is. -/
@[stacks 0CJC "open immersion"]
theorem isOpenImmersion_iff_isOpenImmersion_ambient
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
    (hYft : IsLocallyOfFiniteType B S hS pY')
    (hXflat : IsFlat B S hS pX')
    (hXfp : IsLocallyOfFinitePresentation B S hS pX') :
    IsOpenImmersion B S hS f ↔ IsOpenImmersion B S hS f' := by
  rw [isOpenImmersion_iff_isSmooth_and_isMonomorphism,
    isOpenImmersion_iff_isSmooth_and_isMonomorphism,
    isSmooth_iff_isSmooth_ambient B S hS hiB hcartX hcartY houter hrestrict hinner hcoh hYft
      hXflat hXfp,
    isMonomorphism_iff_isMonomorphism_ambient B S hS hiB hcartX hcartY houter hrestrict hinner
      hcoh hYft hXflat hXfp]

/-- **Stacks 0CJC, syntomic.** Under the hypotheses of
`AlgebraicGeometry.Stack.AlgebraicStacks.isEquivalence_iff_isEquivalence_ambient`, the restricted
1-morphism `f` is syntomic — passes the existential smooth-diagram test of **Stacks 06FN** at
syntomicity of morphisms of algebraic spaces, which is how the source defines a syntomic
1-morphism of algebraic stacks — if and only if the ambient 1-morphism `f'` is. -/
@[stacks 0CJC "syntomic"]
theorem hasPropertyOnSomeSmoothDiagram_isSyntomic_iff_ambient
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
    (hYft : IsLocallyOfFiniteType B S hS pY')
    (hXflat : IsFlat B S hS pX')
    (hXfp : IsLocallyOfFinitePresentation B S hS pX') :
    Stack.HasPropertyOnSomeSmoothDiagram B S hS
        (fun _ _ k => Space.IsSyntomic B S hS k) f.hom ↔
      Stack.HasPropertyOnSomeSmoothDiagram B S hS
        (fun _ _ k => Space.IsSyntomic B S hS k) f'.hom :=
  isSyntomic_iff_isSyntomic_ambient B S hS hiB hcartX hcartY houter hrestrict hinner hcoh hYft
    hXflat hXfp

end AlgebraicGeometry.Stack.AlgebraicStacks

end
