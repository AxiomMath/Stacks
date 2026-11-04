module

public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorPresheafMap
public import StacksFrontier.CategoryTheory.Sites.Stackification.TransportAlongEquivalenceOver

/-!
# Essential images transport backwards along an equivalence over the site on the target

Let `(𝒞, J)` be a site, let `p : 𝒜 ⥤ 𝒞`, `q : 𝒳 ⥤ 𝒞` and `r : 𝒴 ⥤ 𝒞` be fibred categories, let
`G : 𝒜 ⥤ 𝒳` be a 1-morphism over `𝒞` and let `Φ : 𝒳 ⥤ 𝒴` be a 1-morphism over `𝒞` which is an
equivalence over `𝒞`.

`CategoryTheory.Functor.Stackification.essImage_comp_of_isEquivalenceOver` transports clause (2)
of Stacks 02ZN along an equivalence on the **source** of a 1-morphism. This file does the
**target**: if the restriction of `Φ x` along `f : V ⟶ U` is in the essential image of `G ⋙ Φ` on
the fibre over `V`, then the restriction of `x` itself is in the essential image of `G` there.

That is the direction a comparison of two presentations of one stack needs. Stacks 05YQ exhibits
the category `ℋ_d` of degree-`d` finite locally free covers as a stackification of the pointwise
groupoid fibration of free rank-`d` algebra structures, over which an object of `ℋ_d` is in the
essential image **Zariski-locally** on its base — a basis of a finite locally free algebra whose
first vector is the unit exists over a standard open cover. The quotient stack `[X/G]` of the
conjugation action is a second stackification of the same fibration, equivalent to `ℋ_d` over the
site, and its objects are therefore in the essential image of the fibration Zariski-locally too;
but that has to be read off the equivalence, the stackification's own
`AlgebraicGeometry.Stack.essImage_toQuotientStack` producing only an fppf covering.

## Main results

* `CategoryTheory.Functor.Stackification.essImage_of_essImage_comp_of_isEquivalenceOver`: the
  transport above, for one arrow `f : V ⟶ U` at a time, so that whatever covering family carries
  the hypothesis carries the conclusion.
* `CategoryTheory.Functor.Stackification.essImage_of_essImage_comp_of_isEquivalenceOver_sieve`:
  the same with a covering sieve, in the shape clause (2) of Stacks 02ZN has.

## Implementation notes

Everything is formal, and the *same* covering sieve works. Three known facts do the work: the
fibre functor of a composite is the composite of the fibre functors
(`CategoryTheory.Functor.fiberFunctorOfCompEq_comp_eq`, an equality by `rfl`); the fibre functor
of a 1-morphism over the base commutes with the chosen pullbacks
(`CategoryTheory.Functor.IsFibredOneMorphism.mapPullbackFiberIso`); and the fibre functor of a
fully faithful 1-morphism over the base is fully faithful
(`CategoryTheory.Functor.fullyFaithful_fiberFunctorOfCompEq` at
`CategoryTheory.Functor.IsEquivalenceOver.full` and `.faithful`), so an isomorphism between two
of its values is the image of one.

No topology is used in the per-arrow form, and no hypothesis on `𝒜` beyond fibredness; in
particular the three total categories may have independent morphism universes, unlike in
`StacksFrontier.CategoryTheory.Sites.Stackification.TransportAlongEquivalenceOver`, where the map of
morphism presheaves forces a common one.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

namespace CategoryTheory.Functor.Stackification

open CategoryTheory

universe vb v₁ v₂ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒜 : Type u₂} [Category.{v₁} 𝒜]
  {𝒳 : Type u₃} [Category.{v₂} 𝒳] {𝒴 : Type u₄} [Category.{v₂} 𝒴]
  {p : 𝒜 ⥤ 𝒞} {q : 𝒳 ⥤ 𝒞} {r : 𝒴 ⥤ 𝒞} {G : 𝒜 ⥤ 𝒳} {Φ : 𝒳 ⥤ 𝒴}
  [p.IsFibered] [q.IsFibered] [r.IsFibered]

omit [p.IsFibered] in
/-- **Clause (2) of Stacks 02ZN transports backwards along an equivalence over the site on the
target**, one arrow at a time. If the restriction of `Φ x` along `f : V ⟶ U` is in the essential
image of the fibre functor of `G ⋙ Φ`, then the restriction of `x` along `f` is in the essential
image of the fibre functor of `G`.

The witness is the same object of the fibre of `p` over `V`: the isomorphism supplied is one
between two values of the fibre functor of `Φ`, which is fully faithful, so it is the image of an
isomorphism in the fibre of `q`. -/
theorem essImage_of_essImage_comp_of_isEquivalenceOver
    (hG : p.IsFibredOneMorphism q G) (hΦ : q.IsFibredOneMorphism r Φ)
    (hΦeq : IsEquivalenceOver q r Φ) {U V : 𝒞} (f : V ⟶ U) (x : q.Fiber U)
    (h : (fiberFunctorOfCompEq (hG.comp hΦ).comp_eq V).essImage
      (pullbackFiber r ((fiberFunctorOfCompEq hΦ.comp_eq U).obj x) f)) :
    (fiberFunctorOfCompEq hG.comp_eq V).essImage (pullbackFiber q x f) := by
  obtain ⟨a, ⟨e⟩⟩ := h
  refine ⟨a, ⟨?_⟩⟩
  have hff := (fullyFaithful_fiberFunctorOfCompEq hΦ.comp_eq hΦeq.full hΦeq.faithful V).some
  refine hff.preimageIso ?_
  exact e ≪≫ hΦ.mapPullbackFiberIso x f

omit [p.IsFibered] in
/-- **Clause (2) of Stacks 02ZN transports backwards along an equivalence over the site on the
target**, in the shape the clause has: the same covering sieve of the base object works. -/
theorem essImage_of_essImage_comp_of_isEquivalenceOver_sieve
    (hG : p.IsFibredOneMorphism q G) (hΦ : q.IsFibredOneMorphism r Φ)
    (hΦeq : IsEquivalenceOver q r Φ) (J : GrothendieckTopology 𝒞)
    (hobj : ∀ (U : 𝒞) (y : r.Fiber U), ∃ R ∈ J U,
      ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
        (fiberFunctorOfCompEq (hG.comp hΦ).comp_eq V).essImage (pullbackFiber r y f))
    (U : 𝒞) (x : q.Fiber U) :
    ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (fiberFunctorOfCompEq hG.comp_eq V).essImage (pullbackFiber q x f) := by
  obtain ⟨R, hR, hmem⟩ := hobj U ((fiberFunctorOfCompEq hΦ.comp_eq U).obj x)
  exact ⟨R, hR, fun V f hf =>
    essImage_of_essImage_comp_of_isEquivalenceOver hG hΦ hΦeq f x (hmem hf)⟩

end CategoryTheory.Functor.Stackification

end
