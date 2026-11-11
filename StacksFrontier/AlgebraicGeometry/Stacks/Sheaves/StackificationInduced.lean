module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Stackification
public import StacksFrontier.CategoryTheory.Sites.Stackification.InducedEquivalence

/-!
# Stackification does not change the fppf topos (Stacks 06WQ)

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf category
of a scheme `S`. If `f` induces an equivalence of stackifications, then the morphism of topoi
`Sh(𝒳_fppf) ⟶ Sh(𝒴_fppf)` of Stacks 06TS is an equivalence.

That `f` induces an equivalence of stackifications is stated as in the source: there are
stackifications `G : 𝒳 ⥤ 𝒳'` and `H : 𝒴 ⥤ 𝒴'` in the sense of Stacks 02ZN
(`CategoryTheory.Functor.IsFibredOneMorphism.IsStackification`) and a 1-morphism
`E : 𝒳' ⥤ 𝒴'` over the base which is an equivalence over the base and is compatible with `f` by a
vertical 2-isomorphism `f ⋙ H ≅ G ⋙ E`. By the universal property of stackification
(Stacks 0435) such an `E` is the 1-morphism of stackifications induced by `f`, determined up to
2-isomorphism.

## Main results

* `CategoryTheory.Functor.IsFibredOneMorphism.isStackificationEquivalence_of_isEquivalenceOver`:
  a 1-morphism into a category fibred in groupoids which induces an equivalence of
  stackifications satisfies the two local clauses of Stacks 02ZN,
  `CategoryTheory.Functor.IsFibredOneMorphism.IsStackificationEquivalence`.
* `AlgebraicGeometry.Stack.isEquivalence_inverseImage_of_isEquivalenceOver_stackifications`:
  **Stacks 06WQ**.

## Implementation notes

The tagged result is the previous one followed by
`AlgebraicGeometry.Stack.isEquivalence_inverseImage_of_isStackificationEquivalence`, which proves
the conclusion under the two local clauses.

## References

* [Stacks Project, Tag 06WQ](https://stacks.math.columbia.edu/tag/06WQ)
* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 0435](https://stacks.math.columbia.edu/tag/0435)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u uC v₁ v₂ w t

namespace CategoryTheory.Functor.IsFibredOneMorphism

variable {C : Type uC} [Category.{w} C] {X : Type v₁} [Category.{w} X]
  {Y : Type v₂} [Category.{w} Y] {p : X ⥤ C} {q : Y ⥤ C} [p.IsFibered] [q.IsFibered]
  {F : X ⥤ Y} (J : GrothendieckTopology C)

/-- **A 1-morphism inducing an equivalence of stackifications satisfies the two local clauses
of Stacks 02ZN.** Let `G : 𝒳 ⥤ 𝒳'` and `H : 𝒴 ⥤ 𝒴'` be stackifications in the sense of
Stacks 02ZN, and let `E : 𝒳' ⥤ 𝒴'` be a 1-morphism over the site which is an equivalence over the
site and is compatible with `F` by a vertical 2-isomorphism `F ⋙ H ≅ G ⋙ E`. If `𝒴` is fibred in
groupoids, then `F` satisfies `IsStackificationEquivalence`. -/
theorem isStackificationEquivalence_of_isEquivalenceOver (hq : q.IsFiberedInGroupoids)
    (hF : p.IsFibredOneMorphism q F) {X' : Type*} [Category.{w} X'] {Y' : Type*}
    [Category.{w} Y'] {p' : X' ⥤ C} {q' : Y' ⥤ C} [p'.IsFibered] [q'.IsFibered]
    {G : X ⥤ X'} {H : Y ⥤ Y'} {E : X' ⥤ Y'} (hG : p.IsFibredOneMorphism p' G)
    (hH : q.IsFibredOneMorphism q' H) (hGst : hG.IsStackification J)
    (hHst : hH.IsStackification J) (hE : p'.IsFibredOneMorphism q' E)
    (hEeq : IsEquivalenceOver p' q' E) (α : F ⋙ H ≅ G ⋙ E)
    (hα : ∀ a : X, q'.IsHomLift (𝟙 (p.obj a)) (α.hom.app a)) :
    hF.IsStackificationEquivalence J :=
  ⟨Stackification.isLocallyBijective_morPresheafMap_of_isEquivalenceOver hF hG hH hGst hHst hE
      hEeq α hα,
    Stackification.locally_essImage_of_isEquivalenceOver hq hF hG hH hGst hHst hE hEeq α hα⟩

end CategoryTheory.Functor.IsFibredOneMorphism

namespace AlgebraicGeometry.Stack

/-- **Stacks 06WQ.** Let `F : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over the
big fppf category of `S`. If `F` induces an equivalence of stackifications, then the morphism of
topoi `Sh(𝒳_fppf) ⟶ Sh(𝒴_fppf)` of Stacks 06TS is an equivalence.

That `F` induces an equivalence of stackifications is stated with stackifications
`G : 𝒳 ⥤ 𝒳'` and `H : 𝒴 ⥤ 𝒴'` in the sense of Stacks 02ZN
(`CategoryTheory.Functor.IsFibredOneMorphism.IsStackification`), and a 1-morphism
`E : 𝒳' ⥤ 𝒴'` over the base which is an equivalence over the base and is compatible with `F` by
a vertical 2-isomorphism `F ⋙ H ≅ G ⋙ E`; by the universal property of stackification
(Stacks 0435) such an `E` is the 1-morphism of stackifications induced by `F`.

The functor displayed is the inverse image of that morphism of topoi, which by Stacks 06TS is
restriction along `F`; the morphism of topoi is an equivalence exactly when its inverse image
is. -/
@[stacks 06WQ]
theorem isEquivalence_inverseImage_of_isEquivalenceOver_stackifications
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type v₁} [Category.{u} 𝒳] {𝒴 : Type v₂} [Category.{u} 𝒴]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (F : 𝒳 ⥤ 𝒴) (hF : p.IsFibredOneMorphism q F)
    {𝒳' : Type*} [Category.{u} 𝒳'] {𝒴' : Type*} [Category.{u} 𝒴']
    (p' : 𝒳' ⥤ BigFppfOver B S hS) (q' : 𝒴' ⥤ BigFppfOver B S hS) [p'.IsFibered]
    [q'.IsFibered] (G : 𝒳 ⥤ 𝒳') (hG : p.IsFibredOneMorphism p' G)
    (hGst : letI : p.IsFibered := hp.isFibered
      hG.IsStackification (BigFppfOver.topology B S hS))
    (H : 𝒴 ⥤ 𝒴') (hH : q.IsFibredOneMorphism q' H)
    (hHst : letI : q.IsFibered := hq.isFibered
      hH.IsStackification (BigFppfOver.topology B S hS))
    (E : 𝒳' ⥤ 𝒴') (hE : p'.IsFibredOneMorphism q' E) (hEeq : Functor.IsEquivalenceOver p' q' E)
    (α : F ⋙ H ≅ G ⋙ E) (hα : ∀ a : 𝒳, q'.IsHomLift (𝟙 (p.obj a)) (α.hom.app a)) :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology
      (BigFppfOver.topology B S hS)).1
    (F.sheafPushforwardContinuous (Type (max t u v₁ v₂))
      (p.inheritedTopology (BigFppfOver.topology B S hS))
      (q.inheritedTopology (BigFppfOver.topology B S hS))).IsEquivalence := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  exact isEquivalence_inverseImage_of_isStackificationEquivalence.{u, v₁, v₂, t} B S hS p q hp hq
    F hF
    (Functor.IsFibredOneMorphism.isStackificationEquivalence_of_isEquivalenceOver
      (BigFppfOver.topology B S hS) hq hF hG hH hGst hHst hE hEeq α hα)

end AlgebraicGeometry.Stack

end
