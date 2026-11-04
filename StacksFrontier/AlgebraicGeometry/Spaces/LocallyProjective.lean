module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestriction

/-!
# Locally projective modules on an algebraic space

A quasi-coherent module on an algebraic space is *locally projective* when its restriction to
every étale scheme chart is locally projective in the sense of Tag 05JP, that is, when its
sections over every affine open of every chart are a projective module over the functions on
that open.

## Main definitions

* `AlgebraicGeometry.Space.IsLocallyProjective`: local projectivity of a quasi-coherent module
  on an algebraic space.

## Implementation notes

Tag 060Q identifies the chartwise condition used here with the existence of a single surjective
étale chart on which the module is locally projective.  The chartwise form is taken as the
definition because it is the one that restricts along a morphism of charts without choosing a
presentation.

The universe of the module sections is independent of the universe of the schemes; restriction
to a chart raises it to the maximum of the two, which is where
`AlgebraicGeometry.Scheme.Modules.IsLocallyProjective` is then applied.

## References

* [Stacks Project, Tag 060R](https://stacks.math.columbia.edu/tag/060R)
* [Stacks Project, Tag 060Q](https://stacks.math.columbia.edu/tag/060Q)
* [Stacks Project, Tag 05JP](https://stacks.math.columbia.edu/tag/05JP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

/-- **Stacks 060R.** A quasi-coherent module on an algebraic space is locally projective if its
restriction to every étale scheme chart is locally projective. -/
@[stacks 060R]
noncomputable abbrev IsLocallyProjective (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (F : QuasicoherentSheaves.{u, m} B S hS X hX) : Prop :=
  ∀ U : SmallEtale B S hS X,
    Scheme.Modules.IsLocallyProjective (restrictToChart B S hS hX F.obj U)

end AlgebraicGeometry.Space

end
