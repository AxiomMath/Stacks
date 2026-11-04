module

public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FullyFaithfulEquivalence

/-!
# An equivalence criterion whose target is only asked for its morphism sheaves

Let `(𝒞, J)` be a site, let `p : 𝒳 ⥤ 𝒞` and `q : 𝒴 ⥤ 𝒞` be fibred categories over `𝒞` and let
`F : 𝒳 ⥤ 𝒴` be a fully faithful 1-morphism of fibred categories over `𝒞` which is locally
essentially surjective on fibres. Then `F` is an equivalence over `𝒞`.

`CategoryTheory.Functor.isEquivalenceOver_iff_locallyEssSurjOnFibers` (**Stacks 046N**) states
this as an equivalence, with both `p` and `q` assumed to be stacks. The implication proved here
asks less of each side: of the source only effective descent, and of the target only that its
morphism presheaves are sheaves — conditions (3) and (2) of Stacks 026F respectively. Neither
side is asked for condition (3) and (2) together, and the target is not asked for condition (3)
at all.

## Implementation notes

This is the `mpr` direction of Stacks 046N with its hypotheses taken apart: that proof uses
`h₁ : p.IsStack J` only through `h₁.isFibered` and `h₁.hasEffectiveDescent`, and
`h₂ : q.IsStack J` only through `h₂.isFibered` and `h₂.isMorSheaf`.

The weaker form applies where Stacks 046N does not: condition (3) of Stacks 026F for the 2-fibre
product, `CategoryTheory.TwoFibreProductOver.hasEffectiveDescent_structureFunctor`, identifies the
hom universe of the base site with the common hom universe of the three categories of the cospan,
and so does the packaged `CategoryTheory.TwoFibreProductOver.isStack_structureFunctor` (**Stacks
026G**). A 2-fibre product of a quotient stack over a big fppf site therefore has no
`CategoryTheory.Functor.IsStack` available: its three categories have their morphisms one universe
above the site's. Condition (2) at independent universes is
`CategoryTheory.TwoFibreProductOver.IndependentBase.isMorSheaf_structureFunctor`, so a criterion
that asks the target only for condition (2) applies to such a 2-fibre product while Stacks 046N
itself does not.

## Main results

* `CategoryTheory.Functor.isEquivalenceOver_of_locallyEssSurjOnFibers`: the criterion.

## References

* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 046N](https://stacks.math.columbia.edu/tag/046N)
-/

@[expose] public section

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴]

/-- **A fully faithful 1-morphism of fibred categories which is locally essentially surjective on
fibres is an equivalence over the site**, provided descent is effective in the source and the
morphism presheaves of the target are sheaves.

This is the `mpr` direction of Stacks 046N
(`CategoryTheory.Functor.isEquivalenceOver_iff_locallyEssSurjOnFibers`) with the two stack
hypotheses replaced by the single clause of each that it consumes. The local preimages assemble
into a descent datum for `p`, effective descent produces an object of the fibre of `𝒳`, and the
morphism sheaves of `q` identify its image with the given object
(`CategoryTheory.Functor.exists_iso_of_locally_essImage`); essential surjectivity on every fibre
then upgrades to an equivalence over `𝒞`. -/
theorem isEquivalenceOver_of_locallyEssSurjOnFibers
    {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒴} {J : GrothendieckTopology 𝒞}
    [p.IsFibered] [hq : q.IsFibered]
    (hdesc : HasEffectiveDescent p J)
    (hmor : ∀ (U : 𝒞) (a b : q.Fiber U), IsMorSheaf q J U a b)
    (hF : IsFibredOneMorphism p q F) [F.Full] [F.Faithful]
    (hloc : LocallyEssSurjOnFibers hq hF.comp_eq J) :
    Nonempty (IsEquivalenceOver p q F) := by
  have hess : ∀ U : 𝒞, (Fiber.mapOfComp p q F hF.comp_eq U).EssSurj := by
    intro U
    refine ⟨fun x => ?_⟩
    obtain ⟨R, hR, hRess⟩ := hloc U x
    exact exists_iso_of_locally_essImage hF hdesc (hmor U) x hR hRess
  exact ⟨isEquivalenceOver_of_exists_vertical_iso hF.comp_eq
    (exists_vertical_iso_of_fiber_essSurj hF.comp_eq hess)⟩

end CategoryTheory.Functor

end
