module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyFunctor

/-! # The universal property of the stackification of a category fibred in groupoids

Let `(𝒞, J)` be a site, let `p : 𝒮 ⥤ 𝒞` be a category fibred in groupoids, and let `G : 𝒮 ⥤ 𝒮'`
exhibit the stack in groupoids `p' : 𝒮' ⥤ 𝒞` as the stackification of `𝒮`. Given a stack in
groupoids `q : 𝒳 ⥤ 𝒞` and a 1-morphism `F : 𝒮 ⥤ 𝒳` of categories over `𝒞`, there is a
1-morphism `H : 𝒮' ⥤ 𝒳` over `𝒞` and a 2-isomorphism `G ⋙ H ≅ F`. This is the special case of
`CategoryTheory.Functor.Stackification.extend` and `CategoryTheory.Functor.Stackification.unit`
for categories fibred in groupoids.

## Main definitions

* `CategoryTheory.Functor.Stackification.extendGroupoid`: the 1-morphism `H : 𝒮' ⥤ 𝒳`.
* `CategoryTheory.Functor.Stackification.unitGroupoid`: the 2-isomorphism `G ⋙ H ≅ F`.

## Main results

* `CategoryTheory.Functor.Stackification.extendGroupoid_comp_eq`: `H` is strictly over `𝒞`.
* `CategoryTheory.Functor.Stackification.extendGroupoid_isFibredOneMorphism`: `H` is a 1-morphism
  of fibred categories over `𝒞`.
* `CategoryTheory.Functor.Stackification.isHomLift_unitGroupoid_app`: every component of the
  2-isomorphism lies over an identity morphism of `𝒞`.

## Implementation notes

The object universes are independent, as are the hom universes of `𝒞` and of `𝒳`; only `𝒮` and
`𝒮'` share a hom universe.

A stack in groupoids is spelled as `CategoryTheory.Functor.IsFiberedInGroupoids` together with
`CategoryTheory.Functor.IsStack`, not as `CategoryTheory.Functor.IsStackInGroupoids`, which does
not give the sieve-indexed descent that `CategoryTheory.Functor.Stackification.extend` uses.

That `G` is a stackification is spelled out by two hypotheses: `hmor`, that the map
`CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap` of presheaves of morphisms is locally
injective and locally surjective, and `hobj`, that every object of a fibre of `𝒮'` is, along a
covering sieve, in the essential image of the functor on fibres.

## References

* [Stacks 0436](https://stacks.math.columbia.edu/tag/0436).
-/

@[expose] public section

namespace CategoryTheory

namespace Functor

namespace Stackification

section Groupoid

universe vb v v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒮 : Type u₂} [Category.{v} 𝒮] {𝒮' : Type u₃}
  [Category.{v} 𝒮'] {𝒳 : Type u₄} [Category.{v₄} 𝒳] {J : GrothendieckTopology 𝒞}
  {p : 𝒮 ⥤ 𝒞} {p' : 𝒮' ⥤ 𝒞} {q : 𝒳 ⥤ 𝒞} {G : 𝒮 ⥤ 𝒮'} {F : 𝒮 ⥤ 𝒳}
  (hp : p.IsFiberedInGroupoids) (hp' : p'.IsFiberedInGroupoids) (hsp' : p'.IsStack J)
  (hq : q.IsFiberedInGroupoids) (hsq : q.IsStack J)
  (hG : G ⋙ p' = p) (hF : F ⋙ q = p)
  (hmor : haveI : p.IsFibered := hp.isFibered
    haveI : p'.IsFibered := hsp'.isFibered
    ∀ (U : 𝒞) (x y : p.Fiber U),
      Presheaf.IsLocallyInjective (J.over U)
          ((hp'.isFibredOneMorphism hG).morPresheafMap x y) ∧
        Presheaf.IsLocallySurjective (J.over U)
          ((hp'.isFibredOneMorphism hG).morPresheafMap x y))
  (hobj : haveI : p'.IsFibered := hsp'.isFibered
    ∀ (U : 𝒞) (x' : p'.Fiber U), ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (fiberFunctorOfCompEq hG V).essImage (pullbackFiber p' x' f))

/-- Let `(𝒞, J)` be a site, let `p : 𝒮 ⥤ 𝒞` be a category fibred in groupoids, let `G : 𝒮 ⥤ 𝒮'`
exhibit the stack in groupoids `p'` as the stackification of `𝒮`, and let `F : 𝒮 ⥤ 𝒳` be a
1-morphism of categories over `𝒞` into a stack in groupoids. This is the extension `H : 𝒮' ⥤ 𝒳`
of `F` along `G`. -/
@[stacks 0436]
noncomputable def extendGroupoid : 𝒮' ⥤ 𝒳 :=
  haveI : p.IsFibered := hp.isFibered
  haveI : p'.IsFibered := hsp'.isFibered
  haveI : q.IsFibered := hsq.isFibered
  extend (hp'.isFibredOneMorphism hG) (hq.isFibredOneMorphism hF) hmor
    (fun U x y => hsq.isMorSheaf U x y) hobj hsq.hasEffectiveDescent

/-- The extension `H : 𝒮' ⥤ 𝒳` is strictly over `𝒞`: `H ⋙ q = p'`. -/
@[stacks 0436]
theorem extendGroupoid_comp_eq :
    extendGroupoid hp hp' hsp' hq hsq hG hF hmor hobj ⋙ q = p' :=
  have : p.IsFibered := hp.isFibered
  have : p'.IsFibered := hsp'.isFibered
  have : q.IsFibered := hsq.isFibered
  extend_comp_eq (hp'.isFibredOneMorphism hG) (hq.isFibredOneMorphism hF) hmor
    (fun U x y => hsq.isMorSheaf U x y) hobj hsq.hasEffectiveDescent

/-- The extension `H : 𝒮' ⥤ 𝒳` is a 1-morphism of fibred categories over `𝒞`. -/
theorem extendGroupoid_isFibredOneMorphism :
    haveI : p'.IsFibered := hsp'.isFibered
    haveI : q.IsFibered := hsq.isFibered
    p'.IsFibredOneMorphism q (extendGroupoid hp hp' hsp' hq hsq hG hF hmor hobj) :=
  hq.isFibredOneMorphism (extendGroupoid_comp_eq hp hp' hsp' hq hsq hG hF hmor hobj)

/-- The 2-isomorphism `G ⋙ H ≅ F` between `F` and the composite of `G` with its extension. -/
@[stacks 0436]
noncomputable def unitGroupoid :
    G ⋙ extendGroupoid hp hp' hsp' hq hsq hG hF hmor hobj ≅ F :=
  haveI : p.IsFibered := hp.isFibered
  haveI : p'.IsFibered := hsp'.isFibered
  haveI : q.IsFibered := hsq.isFibered
  unit (hp'.isFibredOneMorphism hG) (hq.isFibredOneMorphism hF) hmor
    (fun U x y => hsq.isMorSheaf U x y) hobj hsq.hasEffectiveDescent

/-- Every component of the 2-isomorphism `G ⋙ H ≅ F` lies over an identity morphism of `𝒞`. -/
@[stacks 0436]
lemma isHomLift_unitGroupoid_app (A : 𝒮) :
    q.IsHomLift (𝟙 (p.obj A)) ((unitGroupoid hp hp' hsp' hq hsq hG hF hmor hobj).hom.app A) :=
  have : p.IsFibered := hp.isFibered
  have : p'.IsFibered := hsp'.isFibered
  have : q.IsFibered := hsq.isFibered
  isHomLift_unit_app (hp'.isFibredOneMorphism hG) (hq.isFibredOneMorphism hF) hmor
    (fun U x y => hsq.isMorSheaf U x y) hobj hsq.hasEffectiveDescent A

end Groupoid

end Stackification

end Functor

end CategoryTheory
