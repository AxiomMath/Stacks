module

public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ArbitraryBaseMain
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.MorphismFromStructureMap

/-!
# Stacks 04KL over a base, reduced to the chart morphisms being over the base

`AlgebraicGeometry.Space.IsRecoveredFromSmallEtale` is [Stacks Project, Tag 04KL] over a base
in the form its consumers use: a locally ringed morphism `ψ` of the small étale ringed topoi of
two algebraic spaces over `S` which is 2-compatible with a pair of structure morphisms to a
third is induced by exactly one morphism of algebraic spaces over `S`.

This file records what is left of it. The existence half over an arbitrary base is
`AlgebraicGeometry.Space.existsUnique_spaceHom_twoIso_of_isChartOverBase`, which asks of `ψ`
only that its chart morphisms be over `S`
(`AlgebraicGeometry.Space.IsChartOverBase`); the uniqueness half is Tag 04M6, which holds over
any base. So the whole of `IsRecoveredFromSmallEtale` follows from the single implication

  2-compatible with the structure morphisms  ⟹  `IsChartOverBase`,

and that implication is the one thing missing.

## Main results

* `AlgebraicGeometry.Space.isRecoveredFromSmallEtale_of_isChartOverBase`: Tag 04KL over a base
  from that implication.

## Implementation notes

The implication is not proved here. `ψ` enters `AlgebraicGeometry.Space.IsChartOverBase`
through `AlgebraicGeometry.Space.chartSchemeHom`, which is `Spec` of the ring map
`AlgebraicGeometry.Space.chartRingHom` on the global functions of an affine chart, so reading
the 2-compatibility there needs two things.

The first is the composition law
`chartSchemeHom (χ ∘ ψ) = chartSchemeHom ψ ≫ chartSchemeHom χ`, through which the
2-compatibility — whose composite is `AlgebraicGeometry.Space.smallEtaleComp` — is read. That
law is now available, as `AlgebraicGeometry.Space.chartSchemeHom_smallEtaleComp` in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleChartComposition.lean`, with its ring-level
form `AlgebraicGeometry.Space.chartRingHom_smallEtaleComp` holding for arbitrary charts. It
applies to the section built from a section of `χ⁻¹h_W` over a chart of the middle space and a
section of `ψ⁻¹h_V` over a chart of the source; an arbitrary section of `(χ ∘ ψ)⁻¹h_W` need
only factor that way étale-locally on the source chart, so the local factorization is still
owed.

The second, an identification of `chartSchemeHom` of the morphism of ringed topoi of a morphism
of algebraic spaces (Tag 03G8) with the chart morphism it tautologically carries, is now
available and needs no representability:
`AlgebraicGeometry.Space.chartSchemeHom_chartFiberToInvRep` in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleChartInverseImage.lean`. It rests on
`AlgebraicGeometry.Space.W_chartFiberToInvRep` of that file, which exhibits `f_small⁻¹h_V` as
the sheafification of the presheaf `AlgebraicGeometry.Space.chartFiber` of chart maps over `f`
— Tag 04K2, part (3), at the universe of the structure rings, which is the universe the
morphism of ringed topoi carries its topos at — and
`AlgebraicGeometry.Space.sieveOfSection_range_chartFiberToInvRep_mem` is the resulting local
factorization of an arbitrary section of `f_small⁻¹h_V` into chart maps. What that yields at
once is `AlgebraicGeometry.Space.isChartOverBase_smallEtaleRingedToposHom` in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleChartOverBase.lean`: the chart morphisms of
`(f_small, f♯)` are over the base, for an arbitrary `f` and an arbitrary base `S`.

That is the condition for the leg `(pP)_small` of the 2-compatibility, not for `ψ`, and three
things separate them. The chart morphisms of a morphism of ringed topoi have not been shown
invariant under a 2-isomorphism, so `IsChartOverBase` does not yet transport from `(pP)_small`
to the composite. Reading `IsChartOverBase ψ` off the composite through the composition law
needs an affine étale chart `W` of `A` together with a chart map from `V` to `W` over `pQ`, and
that exists only étale-locally on `V`. And `V` enters `AlgebraicGeometry.Space.invRep`
covariantly, so a covering of `V` does not restrict a section of `ψ⁻¹h_V`; what is wanted
instead is that the sections over the members of a covering of `V` cover `ψ⁻¹h_V` locally, i.e.
that `ψ⁻¹` carries the local epimorphism of a covering to a local epimorphism.

The route this replaces went through direct images, where the comparison with chart base change
is Tag 03G8 (`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representable`) and the structure
map read through it is `AlgebraicGeometry.Space.chartComparison_structureSharp`; both of those
need `f` *representable*, which `AlgebraicGeometry.Space.IsRecoveredFromSmallEtale` does not
supply, since it quantifies over all `pP` and `pQ`.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
* [Stacks Project, Tag 04M6](https://stacks.math.columbia.edu/tag/04M6)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] smallEtaleTopology_subcanonical

/-- **Stacks 04KL over a base, reduced to the chart morphisms.** If every locally ringed
morphism of the small étale ringed topoi of two algebraic spaces over `S` which is 2-compatible
with a pair of structure morphisms has its chart morphisms over `S`, then
`AlgebraicGeometry.Space.IsRecoveredFromSmallEtale` holds.

Existence is `AlgebraicGeometry.Space.existsUnique_spaceHom_twoIso_of_isChartOverBase`, read
over the base `S`; uniqueness is the Tag 04M6 half it already contains. -/
theorem isRecoveredFromSmallEtale_of_isChartOverBase
    (hb : ∀ {A P Q : AlgebraicSpaces B S hS} (pP : P ⟶ A) (pQ : Q ⟶ A)
      (ψ : RingedToposHom (smallEtaleRingedTopos B S hS P) (smallEtaleRingedTopos B S hS Q)),
      ψ.IsLocallyRinged →
      Nonempty (SmallEtaleTwoIso B S hS
        (smallEtaleComp B S hS (smallEtaleRingedToposHom B S hS pQ) ψ)
        (smallEtaleRingedToposHom B S hS pP)) →
      IsChartOverBase ψ) :
    IsRecoveredFromSmallEtale B S hS := by
  intro A P Q pP pQ ψ hloc hcompat
  obtain ⟨f, ⟨t⟩, huniq⟩ :=
    existsUnique_spaceHom_twoIso_of_isChartOverBase (hb pP pQ ψ hloc hcompat) hloc
  exact ⟨f, ⟨t.symm⟩, fun y hy ↦ huniq y ⟨hy.some.symm⟩⟩

end AlgebraicGeometry.Space

end
