module

public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorPresheafMap
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFibrePullback

/-!
# The base-change comparison of a projection of a 2-fibre product

A projection `𝒳 ×_𝒮 𝒴 ⟶ 𝒳` of a 2-fibre product is a fibred 1-morphism, and so carries the
canonical base-change comparison
`CategoryTheory.Functor.IsFibredOneMorphism.mapPullbackFiberIso` between the chosen pullback of
the `𝒳`-component and the `𝒳`-component of the chosen pullback. The same comparison is built, in
the other direction, by
`CategoryTheory.TwoFibreProductOver.pullbackFiberFstIsoOfFiberedInGroupoids`. This file identifies
the two, which is what lets the stagewise comparison of split fibres of a base change be read as
the pair of its projections.

Both comparisons are instances of `CategoryTheory.Functor.fiberIsoOfCartesian` on the same two
cartesian lifts of `f`, taken in opposite orders, so the identification is the general statement
that `CategoryTheory.Functor.fiberIsoOfCartesian` is antisymmetric in its two lifts.

## Main results

* `CategoryTheory.Functor.fiberIsoOfCartesian_symm`: exchanging the two cartesian lifts inverts
  the comparison.
* `CategoryTheory.TwoFibreProductOver.mapPullbackFiberIso_fst_eq` and
  `CategoryTheory.TwoFibreProductOver.mapPullbackFiberIso_snd_eq`.

## References

* [Stacks Project, Tag 02XI](https://stacks.math.columbia.edu/tag/02XI)
* [Stacks Project, Tag 003V](https://stacks.math.columbia.edu/tag/003V)
* [Stacks Project, Tag 0CMT](https://stacks.math.columbia.edu/tag/0CMT)
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace Functor

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳] {p : 𝒳 ⥤ 𝒮}

/-- **Exchanging the two cartesian lifts inverts the comparison of
`CategoryTheory.Functor.fiberIsoOfCartesian`.** Both the forward comparison of `(φ, φ')` and the
inverse of the comparison of `(φ', φ)` factor `φ` through `φ'`, which is cartesian. -/
lemma fiberIsoOfCartesian_symm {Z W : 𝒮} (b : Z ⟶ W) {a : 𝒳} {z z' : p.Fiber Z}
    (φ : z.1 ⟶ a) (φ' : z'.1 ⟶ a) (hφ : p.IsCartesian b φ) (hφ' : p.IsCartesian b φ') :
    fiberIsoOfCartesian b φ φ' hφ hφ' = (fiberIsoOfCartesian b φ' φ hφ' hφ).symm := by
  refine Iso.ext (fiber_hom_ext_of_cartesian b φ' hφ' _ _ ?_)
  rw [Iso.symm_hom, fiberIsoOfCartesian_hom_fac, fiberIsoOfCartesian_inv_fac]

end Functor

namespace TwoFibreProductOver

open Limits

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒮 : Type u₄} [Category.{v₄} 𝒮]
  (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮)

variable [p𝒳.IsFibered] [p𝒴.IsFibered]
  [(structureFunctor p𝒳 p𝒴 p𝒮 F G).IsFibered]
  (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴)
  {U V : 𝒞} (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) (f : V ⟶ U)

omit [p𝒴.IsFibered] in
/-- **The base-change comparison of the first projection is the inverse of the comparison of the
`𝒳`-components of a chosen pullback.** The `𝒳`-component of the chosen lift of `f` in the 2-fibre
product is the image under the projection of that lift, so the two comparisons are
`CategoryTheory.Functor.fiberIsoOfCartesian` on the same pair of cartesian lifts in opposite
orders. -/
lemma mapPullbackFiberIso_fst_eq (h𝒳 : p𝒳.IsFiberedInGroupoids)
    (hfst : Functor.IsFibredOneMorphism (structureFunctor p𝒳 p𝒴 p𝒮 F G) p𝒳
      (fst p𝒳 p𝒴 p𝒮 F G)) :
    hfst.mapPullbackFiberIso P f =
      (pullbackFiberFstIsoOfFiberedInGroupoids p𝒳 p𝒴 p𝒮 F G hF hG P f h𝒳).symm :=
  Functor.fiberIsoOfCartesian_symm f _ _ _ _

omit [p𝒳.IsFibered] in
/-- **The base-change comparison of the second projection is the inverse of the comparison of the
`𝒴`-components of a chosen pullback**, by the argument of
`CategoryTheory.TwoFibreProductOver.mapPullbackFiberIso_fst_eq` on the other side. -/
lemma mapPullbackFiberIso_snd_eq (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (hsnd : Functor.IsFibredOneMorphism (structureFunctor p𝒳 p𝒴 p𝒮 F G) p𝒴
      (snd p𝒳 p𝒴 p𝒮 F G)) :
    hsnd.mapPullbackFiberIso P f =
      (pullbackFiberSndIsoOfFiberedInGroupoids p𝒳 p𝒴 p𝒮 F G hF hG P f h𝒴).symm :=
  Functor.fiberIsoOfCartesian_symm f _ _ _ _

section Conjugation

variable {U' : 𝒞} (P' : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U') (f' : V ⟶ U')

omit [p𝒴.IsFibered] in
/-- **The two conjugations of a morphism of `𝒳`-components agree.** The split fibre of the first
projection conjugates by the base-change comparison of the projection, the stagewise comparison of
split fibres of a 2-fibre product by the comparison of the `𝒳`-components of a chosen pullback;
those are mutually inverse, so the two conjugations are the same morphism.

The identity is stated here, where the fibred 1-morphism is a hypothesis of exactly the type
`CategoryTheory.Functor.IsFibredOneMorphism.mapPullbackFiberIso` expects, rather than at the point
of use, where it arrives through the projection of a category fibred in groupoids and the two
spellings agree only at default transparency -- so that no rewriting tactic has to find the
pattern. -/
lemma conj_mapPullbackFiberIso_fst (h𝒳 : p𝒳.IsFiberedInGroupoids)
    (hfst : Functor.IsFibredOneMorphism (structureFunctor p𝒳 p𝒴 p𝒮 F G) p𝒳
      (fst p𝒳 p𝒴 p𝒮 F G))
    (g : ((toFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG V).obj
        ((structureFunctor p𝒳 p𝒴 p𝒮 F G).pullbackFiber P f)).fst ⟶
      ((toFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG V).obj
        ((structureFunctor p𝒳 p𝒴 p𝒮 F G).pullbackFiber P' f')).fst) :
    (pullbackFiberFstIsoOfFiberedInGroupoids p𝒳 p𝒴 p𝒮 F G hF hG P f h𝒳).inv ≫ g ≫
        (pullbackFiberFstIsoOfFiberedInGroupoids p𝒳 p𝒴 p𝒮 F G hF hG P' f' h𝒳).hom =
      (hfst.mapPullbackFiberIso P f).hom ≫ g ≫ (hfst.mapPullbackFiberIso P' f').inv := by
  rw [mapPullbackFiberIso_fst_eq p𝒳 p𝒴 p𝒮 F G hF hG P f h𝒳 hfst,
    mapPullbackFiberIso_fst_eq p𝒳 p𝒴 p𝒮 F G hF hG P' f' h𝒳 hfst]
  rfl

omit [p𝒳.IsFibered] in
/-- **The two conjugations of a morphism of `𝒴`-components agree**, by the argument of
`CategoryTheory.TwoFibreProductOver.conj_mapPullbackFiberIso_fst` on the other side. -/
lemma conj_mapPullbackFiberIso_snd (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (hsnd : Functor.IsFibredOneMorphism (structureFunctor p𝒳 p𝒴 p𝒮 F G) p𝒴
      (snd p𝒳 p𝒴 p𝒮 F G))
    (g : ((toFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG V).obj
        ((structureFunctor p𝒳 p𝒴 p𝒮 F G).pullbackFiber P f)).snd ⟶
      ((toFiberPullback p𝒳 p𝒴 p𝒮 F G hF hG V).obj
        ((structureFunctor p𝒳 p𝒴 p𝒮 F G).pullbackFiber P' f')).snd) :
    (pullbackFiberSndIsoOfFiberedInGroupoids p𝒳 p𝒴 p𝒮 F G hF hG P f h𝒴).inv ≫ g ≫
        (pullbackFiberSndIsoOfFiberedInGroupoids p𝒳 p𝒴 p𝒮 F G hF hG P' f' h𝒴).hom =
      (hsnd.mapPullbackFiberIso P f).hom ≫ g ≫ (hsnd.mapPullbackFiberIso P' f').inv := by
  rw [mapPullbackFiberIso_snd_eq p𝒳 p𝒴 p𝒮 F G hF hG P f h𝒴 hsnd,
    mapPullbackFiberIso_snd_eq p𝒳 p𝒴 p𝒮 F G hF hG P' f' h𝒴 hsnd]
  rfl

end Conjugation

end TwoFibreProductOver

end CategoryTheory

end
