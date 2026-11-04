module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChartBaseChangeRelation
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleStabilizerPreservingIsomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationConstruction
import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
import StacksFrontier.AlgebraicGeometry.Stacks.SeparationBaseChange

/-!
# The base change of an étale 1-morphism along a chart is étale (proof of Stacks 0DUQ)

Let `h : 𝒳' ⟶ 𝒳` be an étale 1-morphism of algebraic stacks over `S` which is representable by
algebraic spaces, and let `x : 𝒮_U ⟶ 𝒳` be a 1-morphism from the algebraic stack of an object `U`
of the big fppf site. The projection `𝒳' ×_𝒳 𝒮_U ⟶ 𝒮_U` is a base change of `h`, so it is
étale in the relative sense of Stacks 04XB (Stacks 045C), and so is its composite with any
equivalence over the site `𝒰' ⟶ 𝒳' ×_𝒳 𝒮_U`. When `𝒰'` is the algebraic stack of an object `W`
of the site, the morphism `W ⟶ U` of the site this composite names is an étale morphism of
schemes: this is "`U' ⟶ U` is étale" in the proof of Stacks 0DUQ, the hypothesis
`[Etale F.mapObjects.left]` of Stacks 0DT9.

## Main results

* `AlgebraicGeometry.Stack.ChartBaseChange.isRelativelyEtale_chartMap`: the composite
  `𝒰' ⟶ 𝒮_U` is relatively étale.
* `AlgebraicGeometry.Stack.ChartBaseChange.isEtale_representingMap_chartMap`: the morphism of
  representing algebraic spaces it induces is étale.
* `AlgebraicGeometry.Stack.ChartBaseChange.etale_toScheme_map_of_chartMap`: for represented
  `𝒰' = 𝒮_W`, the induced morphism of schemes `W ⟶ U` is étale.
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ChartBaseChange

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (h : 𝒳' ⟶ 𝒳) {U : BigFppfOver B S hS}
  (x : schemeStack.{u, w} B S hS U ⟶ 𝒳)
  {𝒰' : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  (eK : StacksRepresentableCFG.EquivalenceOver 𝒰'.val.p
    (chartBaseChangeSquare h x).pt.val.val.p)

/-- The 1-morphism `f : 𝒰' ⟶ 𝒮_U` is representable by algebraic spaces when `h` is. -/
theorem isRepresentableByAlgebraicSpaces_chartMap
    (hrep : IsRepresentableByAlgebraicSpaces B S hS h.hom.hom) :
    IsRepresentableByAlgebraicSpaces B S hS (chartMap h x eK).hom := by
  have hK : Functor.IsEquivalence eK.hom.functor := eK.toEquivalence.isEquivalence_functor
  have hid : Functor.IsEquivalence
      (BasedFunctor.id (schemeStack.{u, w} B S hS U).val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 _))
  exact (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS (chartMap h x eK).hom
    (chartBaseChangeSquare h x).snd.hom.hom ⟨eK.hom.functor, eK.hom.w⟩
    (BasedFunctor.id _) (Iso.refl _)).1
    (isRepresentableByAlgebraicSpaces_chartBaseChangeSquare_snd B S hS h x hrep)

/-- **The base change of an étale 1-morphism along a chart is relatively étale.** -/
theorem isRelativelyEtale_chartMap
    (hrep : IsRepresentableByAlgebraicSpaces B S hS h.hom.hom) (he : IsEtale B S hS h) :
    IsRelativelyEtale B S hS (chartMap h x eK) := by
  obtain ⟨-, hrel⟩ := isRelativelyEtale_of_isEtale B S hS h hrep he
  have hK : Functor.IsEquivalence eK.hom.functor := eK.toEquivalence.isEquivalence_functor
  have hid : Functor.IsEquivalence
      (BasedFunctor.id (schemeStack.{u, w} B S hS U).val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 _))
  exact ⟨isRepresentableByAlgebraicSpaces_chartMap h x eK hrep,
    relativeProperty_of_equivalences B S hS
    (fun _ _ m => Space.IsEtale B S hS m.hom) (chartMap h x eK).hom
    (chartBaseChangeSquare h x).snd.hom.hom ⟨eK.hom.functor, eK.hom.w⟩ (BasedFunctor.id _)
    (Iso.refl _)
    (relativeProperty_baseChange.{u, u, u + 1} B S hS
      (fun _ _ m => Space.IsEtale B S hS m.hom)
      𝒳'.val 𝒳.val (schemeStack.{u, w} B S hS U).val h.hom x.hom
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} h.hom x.hom).swap
      (Bicategory.isTwoFibreProduct_swap
        (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
          h.hom x.hom)) hrel)⟩

/-- **The morphism of representing algebraic spaces of the base-changed chart map is étale.** -/
theorem isEtale_representingMap_chartMap
    (hrep : IsRepresentableByAlgebraicSpaces B S hS h.hom.hom) (he : IsEtale B S hS h)
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒰'.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver (schemeStack.{u, w} B S hS U).val.val.p
      (presheafOfCategories (G ⋙ typeToCat)).p) :
    Space.IsEtale B S hS (representingMap B S hS _ _ F G eF eG (chartMap h x eK)) :=
  isEtale_representingMap_of_isRelativelyEtale B S hS (chartMap h x eK)
    (isRepresentableByAlgebraicSpaces_chartMap h x eK hrep) F G hF hG eF eG
    (isRelativelyEtale_chartMap h x eK hrep he)

/-- **`U' ⟶ U` is étale.** For `𝒰' = 𝒮_W` represented by an object `W` of the site, the
morphism `W ⟶ U` of the site named by `f : 𝒮_W ⟶ 𝒮_U` is an étale morphism of schemes. -/
theorem etale_toScheme_map_of_chartMap {W : BigFppfOver B S hS}
    (eK : StacksRepresentableCFG.EquivalenceOver (schemeStack.{u, w} B S hS W).val.val.p
      (chartBaseChangeSquare h x).pt.val.val.p)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS h.hom.hom) (he : IsEtale B S hS h)
    (fU : W ⟶ U)
    (hfU : yoneda.map fU = representingMap B S hS _ _ (yoneda.obj W) (yoneda.obj U)
      (PresheafOfCategories.sliceElementsEquivalenceOver W)
      (PresheafOfCategories.sliceElementsEquivalenceOver U) (chartMap h x eK)) :
    Etale ((BigFppfOver.toScheme B S hS).map fU) := by
  refine Space.etale_of_isEtale_yoneda_map B S hS ?_
  rw [hfU]
  exact isEtale_representingMap_chartMap h x eK hrep he _ _ (isAlgebraicSpace_yoneda B S hS W)
    (isAlgebraicSpace_yoneda B S hS U) _ _

end ChartBaseChange

end AlgebraicGeometry.Stack

end
