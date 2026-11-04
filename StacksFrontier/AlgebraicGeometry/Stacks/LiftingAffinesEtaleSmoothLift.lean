module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesLocalStep

/-!
# Smooth lifts along a thickening of algebraic stacks (Stacks 0CJV)

Let `ι : 𝒳 ⟶ 𝒳'` be a thickening of algebraic stacks over `S`, let `W` be an algebraic space over
`S` and let `x : W ⟶ 𝒳` be a smooth 1-morphism. **Stacks 0CJV** asserts that there is an étale
covering `{W_i ⟶ W}` and, for each `i`, a cartesian square
```
W_i ⟶ W'_i
 ↓       ↓
 𝒳  ⟶  𝒳'
```
with `W'_i ⟶ 𝒳'` smooth. One such square is one object of
`AlgebraicGeometry.Stack.EtaleSmoothLift` (**Stacks 0CJP**), so the assertion is that the `base`
components of a family of smooth lifts form an étale covering of `W`. This file proves it,
`AlgebraicGeometry.Stack.exists_isEtaleCovering_etaleSmoothLift`, at exactly these hypotheses.

## The proof

The source's first paragraph produces the covering: a smooth surjective chart `U' ⟶ 𝒳'` by a
scheme of the site (`exists_smooth_surjective_spaceChart`), its base change
`U = 𝒳 ×_{𝒳'} U'`, smooth and surjective over `𝒳` (`exists_thickeningChart_mono`), and the
smooth surjective `V = W ×_𝒳 U ⟶ W` (`exists_smooth_surjective_twoFibreProduct`), refined by an
étale covering by schemes of the site by **Stacks 0CFV**; this is
`exists_etaleCovering_etaleSmoothLift_of_local`. Its remaining paragraphs produce the lift
around each point of a member `T` of that covering, given with a morphism `T ⟶ U` over `𝒳`:
`AlgebraicGeometry.Stack.LiftingAffinesLocal.exists_local_etaleSmoothLift`, whose module
documentation lists the steps. The morphism `T ⟶ U` is locally of finite presentation by
**Stacks 05WT**, as `T ⟶ W` is étale and `V ⟶ W` and `V ⟶ U` are smooth.

## Implementation notes

The source's Koszul-regular immersion and its appeal to **Stacks 0CER** are replaced by minimal
generators of the ideal of the affine member in an affine space over the chart of `𝒳`, lifted
to the thickened chart, and a Jacobian lifting argument along the nil ideal of the thickening
(`Algebra.isSmoothAt_tensor_quotient_span`). The conclusion is the source's.

Thickenings of algebraic stacks are `AlgebraicGeometry.Stack.IsThickening` (**Stacks 0BPP**,
part (1)), the definition the library uses throughout.

## References

* [Stacks Project, Tag 0CJV](https://stacks.math.columbia.edu/tag/0CJV)
* [Stacks Project, Tag 0CJP](https://stacks.math.columbia.edu/tag/0CJP)
* [Stacks Project, Tag 0CFV](https://stacks.math.columbia.edu/tag/0CFV)
* [Stacks Project, Tag 05WT](https://stacks.math.columbia.edu/tag/05WT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Bicategory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism `s : F ⟶ G` of algebraic spaces with `s ≫ p` étale for a smooth `p`, followed by a
smooth `q`, is locally of finite presentation (**Stacks 05WT**). -/
theorem _root_.AlgebraicGeometry.Space.isLocallyOfFinitePresentation_comp_of_isEtale_comp
    {F G H K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (hH : IsAlgebraicSpace B S hS H)
    (hK : IsAlgebraicSpace B S hS K) (s : F ⟶ G) (p : G ⟶ H) (q : G ⟶ K)
    (hsp : Space.IsEtale B S hS (s ≫ p)) (hp : Space.IsSmooth B S hS p)
    (hq : Space.IsSmooth B S hS q) :
    Space.IsLocallyOfFinitePresentation B S hS (s ≫ q) :=
  Space.isLocallyOfFinitePresentation_comp B S hS hF hG hK s q
    (Space.isLocallyOfFinitePresentation_of_comp B S hS hF hG hH s p
      (Space.isLocallyOfFinitePresentation_of_isEtale B S hS hsp)
      (Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
        (Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hp)))
    (Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hq)

/-- **The pointwise local lifts of Stacks 0CJV over the chart `V = W ×_𝒳 (𝒳 ×_{𝒳'} U')`.** Every
point of a scheme of the site, étale over `W` through a morphism factoring through `V`, has an
open neighbourhood which is the base of a smooth lift along `ι`. -/
theorem exists_local_etaleSmoothLift_of_twoFibreProduct
    {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (ι : 𝒳 ⟶ 𝒳') (hι : IsThickening ι)
    (W : AlgebraicSpaces B S hS)
    (x : (algebraicSpaceStackFunctor.{u, w} B S hS).obj W ⟶ 𝒳)
    (hx : AlgebraicStacks.IsSmooth B S hS x)
    {U' : BigFppfOver B S hS}
    (b : (algebraicSpaceStackFunctor.{u, w} B S hS).obj (Space.yonedaSpace _ _ _ U') ⟶ 𝒳')
    (hb : AlgebraicStacks.IsSmooth B S hS b)
    {U : AlgebraicSpaces B S hS} (iU : U ⟶ Space.yonedaSpace _ _ _ U') [Mono iU.hom]
    (a : (algebraicSpaceStackFunctor.{u, w} B S hS).obj U ⟶ 𝒳)
    {γ : (algebraicSpaceStackFunctor.{u, w} B S hS).map iU ≫ b ≅ a ≫ ι}
    (hU : IsTwoFibreProduct (⟨_, _, _, γ⟩ : TwoCommSq b ι))
    {V₀ : AlgebraicSpaces B S hS} (p : V₀ ⟶ W) (q : V₀ ⟶ U)
    (γV : (algebraicSpaceStackFunctor.{u, w} B S hS).map p ≫ x ≅
      (algebraicSpaceStackFunctor.{u, w} B S hS).map q ≫ a)
    (hp : Space.IsSmooth B S hS p.hom) (hq : Space.IsSmooth B S hS q.hom)
    (T : BigFppfOver B S hS) (t : yoneda.obj T ⟶ W.obj) (ht : Space.IsEtale B S hS t)
    (hs : ∃ s : yoneda.obj T ⟶ V₀.obj, s ≫ p.hom = t)
    (y : (BigFppfOver.toScheme B S hS).obj T) :
    ∃ (A : BigFppfOver B S hS) (m : A ⟶ T) (hm : Space.IsEtale B S hS (yoneda.map m ≫ t))
      (ξ : EtaleSmoothLift B S hS ι hι W x hx),
      y ∈ Set.range ((BigFppfOver.toScheme B S hS).map m) ∧
      ξ.base = Space.SpacesEtale.ofRepresentable B S hS W A (yoneda.map m ≫ t) hm := by
  obtain ⟨s, hsp⟩ := hs
  let e : Space.yonedaSpace _ _ _ T ⟶ U :=
    (ObjectProperty.homMk s : Space.yonedaSpace _ _ _ T ⟶ V₀) ≫ q
  have he : Space.IsLocallyOfFinitePresentation B S hS e.hom :=
    Space.isLocallyOfFinitePresentation_comp_of_isEtale_comp B S hS
      (isAlgebraicSpace_yoneda B S hS T) V₀.property W.property U.property s p.hom q.hom
      (by rwa [hsp]) hp hq
  have ht' : (ObjectProperty.homMk t : Space.yonedaSpace _ _ _ T ⟶ W) =
      (ObjectProperty.homMk s : Space.yonedaSpace _ _ _ T ⟶ V₀) ≫ p :=
    ObjectProperty.hom_ext _ hsp.symm
  let η : (algebraicSpaceStackFunctor.{u, w} B S hS).map
      (ObjectProperty.homMk t : Space.yonedaSpace _ _ _ T ⟶ W) ≫ x ≅
      (algebraicSpaceStackFunctor.{u, w} B S hS).map e ≫ a :=
    eqToIso (congrArg (fun f => (algebraicSpaceStackFunctor.{u, w} B S hS).map f ≫ x) ht') ≪≫
      LiftingAffinesLocal.whiskerTwoIso'
        (ObjectProperty.homMk s : Space.yonedaSpace _ _ _ T ⟶ V₀) γV
  exact LiftingAffinesLocal.exists_local_etaleSmoothLift hι W x hx b hb iU a hU T t ht e he η y

/-- **Stacks 0CJV.** Let `ι : 𝒳 ⟶ 𝒳'` be a thickening of algebraic stacks over `S`, let `W` be an
algebraic space over `S` and let `x : W ⟶ 𝒳` be a smooth 1-morphism. Then there is a family of
smooth lifts of étale opens of `W` along `ι` whose bases form an étale covering of `W`: an étale
covering `{W_j ⟶ W}` with cartesian squares `W_j = 𝒳 ×_{𝒳'} W'_j` and `W'_j ⟶ 𝒳'` smooth. -/
@[stacks 0CJV]
theorem exists_isEtaleCovering_etaleSmoothLift
    {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (ι : 𝒳 ⟶ 𝒳') (hι : IsThickening ι)
    (W : AlgebraicSpaces B S hS)
    (x : (algebraicSpaceStackFunctor.{u, w} B S hS).obj W ⟶ 𝒳)
    (hx : AlgebraicStacks.IsSmooth B S hS x) :
    ∃ (J : Type (u + 1)) (ξ : J → EtaleSmoothLift B S hS ι hι W x hx),
      Space.IsEtaleCovering B S hS (fun j => ((ξ j).base.obj.left).obj)
        (fun j => ((ξ j).base.obj.hom).hom) := by
  obtain ⟨_, b, hb, hbs⟩ := exists_smooth_surjective_spaceChart 𝒳'
  choose U iU a γ hU ha has hmono using exists_thickeningChart_mono ι hι b hb hbs
  have := hmono
  choose V₀ p q γV hV' hp hpsurj using exists_smooth_surjective_twoFibreProduct x a ha has
  have hq : Space.IsSmooth B S hS q.hom :=
    isSmooth_fst_of_isTwoFibreProduct_of_isRelativelySmooth (isTwoFibreProduct_swap hV'.some)
      (isRelativelySmooth_of_isSmooth_space_source x hx)
  exact exists_etaleCovering_etaleSmoothLift_of_local B S hS ι hι W x hx V₀ p hp hpsurj
    (fun T t ht hs y => exists_local_etaleSmoothLift_of_twoFibreProduct B S hS ι hι W x hx b hb iU a
      hU.some p q γV hp hq T t ht hs y)

end AlgebraicGeometry.Stack

end
