module

public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmoothTag
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmoothChartBiconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
import StacksCore.Tactic.StacksAttribute

/-!
# A smooth morphism of algebraic spaces is étale-locally formally smooth

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`.  The implication from
smoothness to formal smoothness of [Stacks Project, Tag 04AM] splits, in the source, into two
steps: (I) the lifting problems of `f` are solvable over an affine étale neighbourhood of every
point of the thickening, and (II) those local solutions are glued, by trivializing the
pseudo-torsor they form.

`AlgebraicGeometry.Space.FormallySmoothEtaleLocally` is step (I) as a property of `f`, and
`AlgebraicGeometry.Space.formallySmoothEtaleLocally_of_surjectiveEtaleChart` proves it from one
commuting square of étale charts whose chart of the source is surjective and whose morphism of
schemes is formally smooth.  This file records that a *smooth* morphism supplies such a square
outright, so that step (I) holds for it with no hypothesis at all.

What that pins down is step (II): for a smooth morphism of algebraic spaces the whole of the
implication `smooth → formally smooth` is the single implication
`FormallySmoothEtaleLocally f → FormallySmooth f`, whose hypothesis is now available
unconditionally.

## Main results

* `AlgebraicGeometry.Space.formallySmoothEtaleLocally_of_isSmooth`: **step (I) of Stacks 04AM
  for a smooth morphism of algebraic spaces**, with no carried hypothesis.

## Implementation notes

The square is the atlas square: an atlas of the target, surjective and étale, lifted through
`f` by `AlgebraicGeometry.Space.exists_surjective_etale_presentation_lift`.  Its morphism of
schemes is smooth because `AlgebraicGeometry.Space.IsSmooth` is exactly the condition that the
morphism of schemes of *every* commuting square of étale charts is smooth, and it is formally
smooth by `Stacks.Smooth.formallySmoothScheme_of_smooth`, the implication
(1) ⟹ (2) of [Stacks Project, Tag 02H6] for schemes.

No tag is placed: Tag 04AM already has clause-stringed carriers, and this is one step of one of
its implications rather than the implication.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04CY](https://stacks.math.columbia.edu/tag/04CY)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
* [Stacks Project, Tag 061K](https://stacks.math.columbia.edu/tag/061K)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Step (I) of the implication from smoothness of Stacks 04AM, for a smooth morphism of
algebraic spaces.**  Every infinitesimal lifting problem of a smooth morphism of algebraic
spaces over `S` is solvable over an affine object étale over the thickening whose image
contains any prescribed point of it, compatibly with the given section of the source.

The atlas square of `f` has its morphism of schemes smooth, since
`AlgebraicGeometry.Space.IsSmooth` asks that of every commuting square of étale charts, hence
formally smooth by the scheme case of [Stacks Project, Tag 02H6]; that is the hypothesis of
`AlgebraicGeometry.Space.formallySmoothEtaleLocally_of_surjectiveEtaleChart`. -/
theorem formallySmoothEtaleLocally_of_isSmooth {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : IsSmooth B S hS f) :
    FormallySmoothEtaleLocally B S hS f := by
  obtain ⟨V, b, hbSurj, hbEtale⟩ := hY.exists_atlas
  obtain ⟨U, a, ψ, hdiag, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurj hbEtale
  have hψ : AlgebraicGeometry.Smooth ((BigFppfOver.toScheme B S hS).map ψ) :=
    hf U V a b ψ haEtale hbEtale hdiag.symm
  exact formallySmoothEtaleLocally_of_surjectiveEtaleChart B S hS a b ψ haEtale hbEtale haSurj
    hdiag (Stacks.Smooth.formallySmoothScheme_of_smooth _)

end AlgebraicGeometry.Space

end
