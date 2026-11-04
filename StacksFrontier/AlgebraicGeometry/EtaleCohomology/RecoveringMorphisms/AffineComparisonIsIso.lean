module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.AffineComparisonAssembly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.ComparisonIsIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.PresentationExistence

/-!
# The comparison of Stacks 04I6 is an isomorphism at every affine étale chart

`AlgebraicGeometry.isIso_comparisonSheafHom` says that the comparison `g⁻¹h_V ⟶ h_{X ×_Y V}` of
step (3) of the proof of [Stacks Project, Tag 04I6] is an isomorphism at an affine étale chart `V`
of an affine `Y` *carrying a standard presentation*, which it takes as a hypothesis.  Every affine
étale chart carries one, by `Stacks.EtaleCohomology.exists_standardPresentationOverSmallEtale`, so
the hypothesis can be discharged chart by chart; and the comparison re-indexed by the small affine
étale site, `AlgebraicGeometry.affineComparisonSheafHom`, is the same morphism
(`AlgebraicGeometry.affineComparisonSheafHom_eq`, which holds by `rfl`).

With that, the `hiso` hypothesis of
`AlgebraicGeometry.affineRepresentableComparisonOfIsIso` is discharged and the comparison *datum*
`AlgebraicGeometry.AffineRepresentableComparison` is constructed outright for any locally ringed
`(g, g^♯)` over an affine `Y` — no presentation, no iso-ness and no affineness of a chart left as a
hypothesis.

## Main definitions

* `AlgebraicGeometry.affineRepresentableComparison` — **the comparison datum of Stacks 04I6 at the
  affine charts**, constructed rather than hypothesised.

## Main results

* `AlgebraicGeometry.isIso_affineComparisonSheafHom` — the comparison is an isomorphism at every
  object of the small affine étale site.

## Implementation notes

The affineness instance on the underlying chart is supplied from
`ObjectProperty.FullSubcategory.property`: `AlgebraicGeometry.IsAffine` does not synthesize through
`AlgebraicGeometry.SmallAffineEtale.toScheme`.  Since it is a `Prop`, the instance that
`AlgebraicGeometry.affineComparisonSheafHom` uses internally and the one in scope here are equal by
proof irrelevance, so `AlgebraicGeometry.isIso_comparisonSheafHom` applies directly and
`AlgebraicGeometry.affineComparisonSheafHom_eq` does not have to be rewritten with.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme}
  (g : RingedToposHom
    (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
    (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
  (f : X ⟶ Y)
  (hf : (B.inclusion.map f).appTop =
    g.globalSectionsMap (SmallEtale.finalIsTerminal B X.obj X.property)
      (SmallEtale.finalIsTerminal B Y.obj Y.property))
  [IsAffine Y.obj]

include hf in
/-- **The comparison of step (3) of [Stacks Project, Tag 04I6] is an isomorphism at every object of
the small affine étale site of `Y`.** -/
theorem isIso_affineComparisonSheafHom (hg : g.IsLocallyRinged)
    (V₀ : SmallAffineEtale B Y.obj Y.property) :
    IsIso (affineComparisonSheafHom B g f hf V₀) := by
  have := V₀.property
  obtain ⟨n, P, ⟨pres⟩⟩ :=
    Stacks.EtaleCohomology.exists_standardPresentationOverSmallEtale (B := B) (hS := Y.property)
      V₀.obj
  exact isIso_comparisonSheafHom B g f hf V₀.obj pres hg

include hf in
/-- **The comparison datum of Stacks 04I6 at the affine étale charts of `Y`, constructed.**  For a
*locally* ringed morphism `(g, g^♯)` of the small étale ringed topoi, an affine `Y`, and `f` the
morphism of schemes chosen in the first paragraph of the source's proof,

`g⁻¹h_{V} ≅ h_{X ×_Y V}` naturally in the affine étale chart `V`. -/
def affineRepresentableComparison (hg : g.IsLocallyRinged) :
    AffineRepresentableComparison B g f :=
  affineRepresentableComparisonOfIsIso B g f hf (isIso_affineComparisonSheafHom B g f hf hg)

end AlgebraicGeometry

end
