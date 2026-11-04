module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallyUnramifiedEtaleCharts

/-!
# Formal unramifiedness of a morphism of algebraic spaces from one étale chart square

A morphism of the big fppf site over `S` has formally unramified Yoneda image exactly when
its underlying morphism of schemes is formally unramified. Consequently, if a morphism of
presheaves fits in a commuting square of étale charts whose chart morphism is formally
unramified as a morphism of schemes, then the composite of the chart of the source with the
morphism is formally unramified. These are the steps of the implication (3) ⟹ (1) of
[Stacks Project, Tag 04G8] which do not descend along the chart.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.formallyUnramified_yoneda_map_of_formallyUnramified_map` passes
  from formal unramifiedness of the underlying morphism of schemes of a morphism of the big
  fppf site to formal unramifiedness of its Yoneda image, and
  `AlgebraicGeometry.Space.formallyUnramified_yoneda_map_iff_formallyUnramified_map` is the
  resulting equivalence.
* `AlgebraicGeometry.Space.formallyUnramified_chart_comp` makes the composite of an étale
  chart of the source with the morphism formally unramified.
* `AlgebraicGeometry.Space.formallyUnramified_of_exists_surjectiveEtaleChart` is the
  implication (3) ⟹ (1) of [Stacks Project, Tag 04G8] relative to the descent direction of
  [Stacks Project, Tag 04CY], which is carried as the explicit hypothesis `h04CY`, and
  `AlgebraicGeometry.Space.formallyUnramified_iff_holdsOnEveryEtaleChart` assembles it with
  the two proved implications into the equivalence of all three conditions of the tag, still
  relative to that one hypothesis.

## Implementation notes

Formal unramifiedness of a morphism of presheaves, Tag 049S, tests square-zero thickenings
*inside the chosen big fppf site*, and only those whose two members are affine, whereas
Mathlib's `AlgebraicGeometry.FormallyUnramified` tests all of them. The passage from the
site-level condition to the condition on schemes is
`AlgebraicGeometry.Space.formallyUnramified_map_of_formallyUnramified`. The passage back is
immediate: Mathlib's `AlgebraicGeometry.FormallyUnramified.hom_ext` cancels two morphisms of
schemes out of an arbitrary closed immersion with nilpotent kernel ideal, and a morphism of
the site is determined by its underlying morphism of schemes because
`AlgebraicGeometry.BigFppfOver.toScheme` is faithful. This is the unramified counterpart of
`AlgebraicGeometry.Space.formallySmooth_yoneda_map_of_formallySmoothScheme`, and unlike the
smooth case it needs no size hypothesis at all, because `hom_ext` is a cancellation law
rather than an existence statement.

With that bridge the first two steps of the proof of (3) ⟹ (1) are available: the chart of
the target is formally unramified by Tag 04AL, so the composite of the chart of the source
with the morphism — which is the chart morphism followed by the chart of the target — is
formally unramified by Tag 049T. What remains is to *descend* formal unramifiedness along
the chart of the source, which is Tag 04CY in its direction (5): for `p` representable,
surjective and étale, formal unramifiedness of `p ≫ q` gives formal unramifiedness of `q`.
That direction is not available in this development — only the composition direction, Tag
04CY (3), is, as `AlgebraicGeometry.Space.formallyUnramified_comp_of_etale` — so it is
carried here as the explicit hypothesis `h04CY` of
`AlgebraicGeometry.Space.formallyUnramified_of_exists_surjectiveEtaleChart`, and that
theorem accordingly carries no `@[stacks 04G8]` attribute.

The hypothesis `h04CY` additionally assumes that the middle presheaf is an algebraic space.
The proof of Tag 04CY (5) ends by identifying two sections of the middle functor which agree
after pullback along an étale covering, which uses a sheaf property that the tag's statement
— quantified over arbitrary set-valued functors — does not assume. The added hypothesis is
what the consumer here has anyway, since Tag 04G8 is a statement about algebraic spaces.

## References

* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
* [Stacks Project, Tag 049T](https://stacks.math.columbia.edu/tag/049T)
* [Stacks Project, Tag 04AL](https://stacks.math.columbia.edu/tag/04AL)
* [Stacks Project, Tag 04CY](https://stacks.math.columbia.edu/tag/04CY)
* [Stacks Project, Tag 04G8](https://stacks.math.columbia.edu/tag/04G8)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### The site-level condition and the condition on schemes -/

/-- A morphism of the big fppf site over `S` whose underlying morphism of schemes is
formally unramified in Mathlib's sense has formally unramified Yoneda image in the sense of
[Stacks Project, Tag 049S].

Two solutions of a site-level lifting problem are morphisms into the source whose
composites with the morphism agree and whose restrictions along the thickening agree, so
`AlgebraicGeometry.FormallyUnramified.hom_ext` identifies their underlying morphisms of
schemes, and `AlgebraicGeometry.BigFppfOver.toScheme` is faithful. -/
theorem formallyUnramified_yoneda_map_of_formallyUnramified_map (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {P Q : BigFppfOver B S hS} (ψ : P ⟶ Q)
    (hψ : _root_.AlgebraicGeometry.FormallyUnramified
      ((BigFppfOver.toScheme B S hS).map ψ)) :
    FormallyUnramified (yoneda.map ψ) := by
  intro T T' _ _ i hi x y _ z₁ z₂ hz₁ hz₂
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion
    ((BigFppfOver.toScheme B S hS).map i) := hi.1
  apply Functor.map_injective (F := BigFppfOver.toScheme B S hS)
  apply _root_.AlgebraicGeometry.FormallyUnramified.hom_ext
    ((BigFppfOver.toScheme B S hS).map i) ⟨2, by simpa using hi.2⟩
    ((BigFppfOver.toScheme B S hS).map ψ)
  · simp only [← Functor.map_comp]
    exact congrArg _ (hz₁.1.trans hz₂.1.symm)
  · simp only [← Functor.map_comp]
    exact congrArg _ (hz₁.2.trans hz₂.2.symm)

/-- For a morphism of the big fppf site over `S`, the site-level formal unramifiedness of
[Stacks Project, Tag 049S] of its Yoneda image and formal unramifiedness of its underlying
morphism of schemes agree.

The forward implication is
`AlgebraicGeometry.Space.formallyUnramified_map_of_formallyUnramified` and the backward one
is `AlgebraicGeometry.Space.formallyUnramified_yoneda_map_of_formallyUnramified_map`. -/
theorem formallyUnramified_yoneda_map_iff_formallyUnramified_map (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {P Q : BigFppfOver B S hS} (ψ : P ⟶ Q) :
    FormallyUnramified (yoneda.map ψ) ↔
      _root_.AlgebraicGeometry.FormallyUnramified
        ((BigFppfOver.toScheme B S hS).map ψ) :=
  ⟨formallyUnramified_map_of_formallyUnramified B S hS ψ,
    formallyUnramified_yoneda_map_of_formallyUnramified_map B S hS ψ⟩

/-! ### The steps of (3) ⟹ (1) which do not descend along the chart -/

/-- **Stacks 04G8, the composite of the chart of the source with the morphism.** Let `f` be a
morphism of presheaves on the big fppf site of `S`, let `a` and `b` be charts of its source
and target fitting in a commuting square over a morphism `h` of the site, let `b` be étale,
and let the underlying morphism of schemes of `h` be formally unramified. Then `a ≫ f` is
formally unramified.

The chart `b` is formally unramified by [Stacks Project, Tag 04AL], the Yoneda image of `h`
is formally unramified by
`AlgebraicGeometry.Space.formallyUnramified_yoneda_map_of_formallyUnramified_map`, and
`a ≫ f` is their composite by the commuting square, so [Stacks Project, Tag 049T] applies.
Neither an algebraicity hypothesis nor surjectivity of either chart is used. -/
theorem formallyUnramified_chart_comp (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    {U V : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (h : U ⟶ V)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hdiag : yoneda.map h ≫ b = a ≫ f)
    (hh : _root_.AlgebraicGeometry.FormallyUnramified
      ((BigFppfOver.toScheme B S hS).map h)) :
    FormallyUnramified (a ≫ f) := by
  rw [← hdiag]
  exact formallyUnramified_comp (yoneda.map h) b
    (formallyUnramified_yoneda_map_of_formallyUnramified_map B S hS h hh)
    (formallyUnramified_of_etale B S hS b hb)

/-- **Stacks 04G8, condition (3) implies condition (1), relative to Tag 04CY.** If a
morphism `f` out of an algebraic space over `S` has one commuting square of surjective
étale scheme charts whose chart morphism is formally unramified as a morphism of schemes,
then `f` is formally unramified in the sense of [Stacks Project, Tag 049S].

The hypothesis `h04CY` is the descent direction of [Stacks Project, Tag 04CY], its part (5),
with the middle functor assumed to be an algebraic space: for a representable, surjective,
étale transformation `p` into an algebraic space, formal unramifiedness of `p ≫ q` gives
formal unramifiedness of `q`. Only the composition direction of that tag is available in this
development, so `h04CY` is carried as an explicit hypothesis and this theorem carries no
`@[stacks 04G8]` attribute. Everything else is
`AlgebraicGeometry.Space.formallyUnramified_chart_comp`. -/
theorem formallyUnramified_of_exists_surjectiveEtaleChart (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    (h04CY : ∀ {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : F ⟶ G) (q : G ⟶ H),
      IsAlgebraicSpace B S hS G →
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p →
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p →
      FormallyUnramified (p ≫ q) → FormallyUnramified q)
    (hex : ∃ (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y)
      (h : U ⟶ V),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b ∧
      yoneda.map h ≫ b = a ≫ f ∧
      _root_.AlgebraicGeometry.FormallyUnramified
        ((BigFppfOver.toScheme B S hS).map h)) :
    FormallyUnramified f := by
  obtain ⟨U, V, a, b, h, haEtale, hbEtale, haSurj, _hbSurj, hdiag, hh⟩ := hex
  exact h04CY a f hX haSurj haEtale
    (formallyUnramified_chart_comp B S hS f a b h hbEtale hdiag hh)

/-- **Stacks 04G8, conditions (1) and (2), relative to Tag 04CY.** A morphism of algebraic
spaces over `S` is formally unramified in the sense of [Stacks Project, Tag 049S] if and only
if the scheme morphism in every commuting square of étale scheme charts of it is formally
unramified, granted the descent direction `h04CY` of [Stacks Project, Tag 04CY].

The forward implication is
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_formallyUnramified` and uses nothing
beyond itself; the backward one goes through condition (3), produced by
`AlgebraicGeometry.Space.exists_surjectiveEtaleChart_of_holdsOnEveryEtaleChart`, and then
through `AlgebraicGeometry.Space.formallyUnramified_of_exists_surjectiveEtaleChart`. So all
three conditions of the tag are equivalent as soon as `h04CY` is available, and that single
hypothesis is all that the tag still owes here; the statement therefore carries no
`@[stacks 04G8]` attribute. -/
theorem formallyUnramified_iff_holdsOnEveryEtaleChart (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (h04CY : ∀ {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : F ⟶ G) (q : G ⟶ H),
      IsAlgebraicSpace B S hS G →
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p →
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p →
      FormallyUnramified (p ≫ q) → FormallyUnramified q) :
    FormallyUnramified f ↔
      HoldsOnEveryEtaleChart B S hS
        (@_root_.AlgebraicGeometry.FormallyUnramified.{u} : MorphismProperty Scheme.{u}) f :=
  ⟨holdsOnEveryEtaleChart_of_formallyUnramified B S hS f,
    fun hall => formallyUnramified_of_exists_surjectiveEtaleChart B S hS hX f h04CY
      (exists_surjectiveEtaleChart_of_holdsOnEveryEtaleChart B S hS hX hY f hall)⟩

end AlgebraicGeometry.Space

end
