module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFibres

/-!
# Chosen pullbacks in a 2-fibre product are componentwise (Stacks 02XI, 02XJ)

`StacksFrontier.CategoryTheory.TwoFibreProduct.OverFibres` identifies the fibre of
`CategoryTheory.TwoFibreProductOver` at an object `U` of the base with the 2-fibre product of the
fibre categories. That identification is an isomorphism of categories, but it says nothing about
the *chosen pullbacks*: the cleaving of the 2-fibre product that
`CategoryTheory.Functor.IsPreFibered` provides is an arbitrary choice, and its `𝒳`-component need
not be the chosen pullback in `𝒳`.

This file supplies the comparison. When `p𝒳` is fibred in groupoids every morphism of `𝒳` lying
over `f` is strongly cartesian — this is
`CategoryTheory.Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift` — and the
`𝒳`-component of the chosen cartesian lift of `f` in the 2-fibre product does lie over `f`
(`CategoryTheory.TwoFibreProductOver.isHomLift_a`). So it is a cartesian lift of `f` at the
`𝒳`-component of the target, and is therefore canonically isomorphic *in the fibre* to the chosen
one. The same argument on the `𝒴`-side gives the second comparison.

These comparisons are what a map out of the *split* model of the 2-fibre product needs: the split
fibre `CategoryTheory.Functor.SplitFiber` of the 2-fibre product over `V` has as objects the
pairs `(P, f : V ⟶ U)` with `P` an object of the fibre at `U`, and as morphisms the morphisms
between the *chosen pullbacks* `f^* P`; reading such a morphism componentwise is exactly
conjugation by the isomorphisms below.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.pullbackFiberFstIsoOfFiberedInGroupoids`: the chosen
  pullback of the `𝒳`-component is the `𝒳`-component of the chosen pullback.
* `CategoryTheory.TwoFibreProductOver.pullbackFiberSndIsoOfFiberedInGroupoids`: the same on the
  `𝒴`-side.

## Implementation notes

`StacksFrontier/CategoryTheory/Sites/Stack/TwoFibreProductMorSheafIndependentBase.lean` carries
comparisons with the same conclusion under the name
`CategoryTheory.TwoFibreProductOver.pullbackFiberFstIso`, and those are the ones to reuse whenever
their hypotheses are available. They are not interchangeable with the comparisons below, which is
why the two sets of names coexist:

* that file derives the cartesian property of the component from `F` and `G` being *fibred
  1-morphisms* over a fibred `p𝒮` (Stacks 02XQ), whereas the declarations here derive it from
  `p𝒳` (resp. `p𝒴`) being *fibred in groupoids* and need only the commuting triangles
  `F ⋙ p𝒮 = p𝒳`; neither hypothesis implies the other, and `[p𝒮.IsFibered]` is not needed here;
* that file identifies the hom universes of `𝒳`, `𝒴` and `𝒮`, while the declarations here leave
  them independent.

## References

* [Stacks Project, Tag 02XI](https://stacks.math.columbia.edu/tag/02XI)
* [Stacks Project, Tag 003V](https://stacks.math.columbia.edu/tag/003V)
* [Stacks Project, Tag 0CMT](https://stacks.math.columbia.edu/tag/0CMT)
-/

@[expose] public section

namespace CategoryTheory.TwoFibreProductOver

open Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒮 : Type u₄} [Category.{v₄} 𝒮]
  (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮)

section FibrePullback

variable [p𝒳.IsFibered] [p𝒴.IsFibered]
  [(structureFunctor p𝒳 p𝒴 p𝒮 F G).IsFibered]
  (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴)
  {U V : 𝒞} (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) (f : V ⟶ U)

/-- The `𝒳`-component of the chosen cartesian lift of `f` at an object of the fibre of the
2-fibre product. -/
noncomputable abbrev pullbackHomFst :
    (Functor.pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P f).1.x ⟶ P.1.x :=
  (Functor.IsPreFibered.pullbackMap P.2 f).a

/-- The `𝒴`-component of the chosen cartesian lift of `f` at an object of the fibre of the
2-fibre product. -/
noncomputable abbrev pullbackHomSnd :
    (Functor.pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P f).1.y ⟶ P.1.y :=
  (Functor.IsPreFibered.pullbackMap P.2 f).b

/-- The `𝒳`-component of the chosen cartesian lift of `f` lies over `f`. -/
instance isHomLift_pullbackHomFst :
    p𝒳.IsHomLift f (pullbackHomFst p𝒳 p𝒴 p𝒮 F G P f) :=
  isHomLift_a (Functor.IsPreFibered.pullbackMap P.2 f) f inferInstance

/-- The `𝒴`-component of the chosen cartesian lift of `f` lies over `f`. -/
instance isHomLift_pullbackHomSnd :
    p𝒴.IsHomLift f (pullbackHomSnd p𝒳 p𝒴 p𝒮 F G P f) :=
  isHomLift_b (Functor.IsPreFibered.pullbackMap P.2 f) f inferInstance

/-- **The `𝒳`-component of a chosen pullback in the 2-fibre product is a chosen pullback in
`𝒳`.** Both carry a cartesian lift of `f` into the `𝒳`-component of the target: the chosen one by
construction, and the component of the chosen lift of `f` in the 2-fibre product because `p𝒳` is
fibred in groupoids, so that *every* morphism of `𝒳` over `f` is strongly cartesian. -/
noncomputable def pullbackFiberFstIsoOfFiberedInGroupoids (h𝒳 : p𝒳.IsFiberedInGroupoids) :
    ((toFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG V).obj
        (Functor.pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P f)).fst ≅
      Functor.pullbackFiber p𝒳
        ((toFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U).obj P).fst f :=
  haveI : p𝒳.IsStronglyCartesian f (pullbackHomFst p𝒳 p𝒴 p𝒮 F G P f) :=
    h𝒳.isStronglyCartesian_homLift f (pullbackHomFst p𝒳 p𝒴 p𝒮 F G P f)
  Functor.fiberIsoOfCartesian f (pullbackHomFst p𝒳 p𝒴 p𝒮 F G P f)
    (Functor.IsPreFibered.pullbackMap
      ((toFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U).obj P).fst.2 f)
    inferInstance (Functor.IsPreFibered.pullbackMap.IsCartesian _ f)

omit [p𝒴.IsFibered] in
/-- The comparison of
`CategoryTheory.TwoFibreProductOver.pullbackFiberFstIsoOfFiberedInGroupoids` factors the
`𝒳`-component of the chosen lift of `f` through the chosen `𝒳`-lift of `f`. -/
@[reassoc (attr := simp)]
lemma pullbackFiberFstIsoOfFiberedInGroupoids_hom_fac (h𝒳 : p𝒳.IsFiberedInGroupoids) :
    Functor.Fiber.fiberInclusion.map
          (pullbackFiberFstIsoOfFiberedInGroupoids p𝒳 p𝒴 p𝒮 F G hF hG P f h𝒳).hom ≫
        Functor.IsPreFibered.pullbackMap
          ((toFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U).obj P).fst.2 f =
      pullbackHomFst p𝒳 p𝒴 p𝒮 F G P f :=
  have : p𝒳.IsStronglyCartesian f (pullbackHomFst p𝒳 p𝒴 p𝒮 F G P f) :=
    h𝒳.isStronglyCartesian_homLift f (pullbackHomFst p𝒳 p𝒴 p𝒮 F G P f)
  Functor.fiberIsoOfCartesian_hom_fac _ _ _ _ _

/-- **The `𝒴`-component of a chosen pullback in the 2-fibre product is a chosen pullback in
`𝒴`**, by the argument of
`CategoryTheory.TwoFibreProductOver.pullbackFiberFstIsoOfFiberedInGroupoids` on the other side. -/
noncomputable def pullbackFiberSndIsoOfFiberedInGroupoids (h𝒴 : p𝒴.IsFiberedInGroupoids) :
    ((toFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG V).obj
        (Functor.pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P f)).snd ≅
      Functor.pullbackFiber p𝒴
        ((toFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U).obj P).snd f :=
  haveI : p𝒴.IsStronglyCartesian f (pullbackHomSnd p𝒳 p𝒴 p𝒮 F G P f) :=
    h𝒴.isStronglyCartesian_homLift f (pullbackHomSnd p𝒳 p𝒴 p𝒮 F G P f)
  Functor.fiberIsoOfCartesian f (pullbackHomSnd p𝒳 p𝒴 p𝒮 F G P f)
    (Functor.IsPreFibered.pullbackMap
      ((toFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U).obj P).snd.2 f)
    inferInstance (Functor.IsPreFibered.pullbackMap.IsCartesian _ f)

omit [p𝒳.IsFibered] in
/-- The comparison of
`CategoryTheory.TwoFibreProductOver.pullbackFiberSndIsoOfFiberedInGroupoids` factors the
`𝒴`-component of the chosen lift of `f` through the chosen `𝒴`-lift of `f`. -/
@[reassoc (attr := simp)]
lemma pullbackFiberSndIsoOfFiberedInGroupoids_hom_fac (h𝒴 : p𝒴.IsFiberedInGroupoids) :
    Functor.Fiber.fiberInclusion.map
          (pullbackFiberSndIsoOfFiberedInGroupoids p𝒳 p𝒴 p𝒮 F G hF hG P f h𝒴).hom ≫
        Functor.IsPreFibered.pullbackMap
          ((toFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG U).obj P).snd.2 f =
      pullbackHomSnd p𝒳 p𝒴 p𝒮 F G P f :=
  have : p𝒴.IsStronglyCartesian f (pullbackHomSnd p𝒳 p𝒴 p𝒮 F G P f) :=
    h𝒴.isStronglyCartesian_homLift f (pullbackHomSnd p𝒳 p𝒴 p𝒮 F G P f)
  Functor.fiberIsoOfCartesian_hom_fac _ _ _ _ _

end FibrePullback

end CategoryTheory.TwoFibreProductOver

end
