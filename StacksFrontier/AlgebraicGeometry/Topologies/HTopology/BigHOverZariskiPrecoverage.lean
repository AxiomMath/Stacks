module

public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpStackCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.SheafCriterion

/-!
# The Zariski precoverage of the big h category over `S` is the comap of the Zariski precoverage

`AlgebraicGeometry.BigHOver.zariskiTopology`, the topology condition (1) of Stacks 0EX9 refers
to, is the Grothendieck topology *generated* by `AlgebraicGeometry.BigHOver.zariskiPrecoverage`.
A statement about every covering sieve of the generated topology therefore does not reduce to a
statement about the generating families by itself: the generated topology has more covering
sieves than the precoverage has families, and the reduction is a theorem.

`CategoryTheory.Pseudofunctor.IsStack.of_precoverage` is that theorem for the stack condition and
`CategoryTheory.Pseudofunctor.IsPrestack.of_precoverage` for the prestack condition. Each asks
the precoverage for three properties — it contains the isomorphisms, it is stable under base
change, it is stable under composition — and the base category for pullbacks, which here are
`AlgebraicGeometry.hasPullbacks_bigHOver`. None of the three was available for
`AlgebraicGeometry.BigHOver.zariskiPrecoverage`, so neither reduction could be run at the
Zariski topology of the big h category over `S`.

This file identifies that precoverage with the comap of the Zariski precoverage of schemes along
the inclusion of the site, which gives all three at once.

## Main results

* `AlgebraicGeometry.BigHOver.zariskiPrecoverage_eq_comap`: **the Zariski precoverage of the big
  h category over `S` is `CategoryTheory.Precoverage.comap` of
  `AlgebraicGeometry.Scheme.zariskiPrecoverage` along
  `AlgebraicGeometry.BigHOver.toScheme`.**
* `AlgebraicGeometry.BigHOver.zariskiPrecoverage_hasIsos`,
  `AlgebraicGeometry.BigHOver.zariskiPrecoverage_isStableUnderBaseChange`,
  `AlgebraicGeometry.BigHOver.zariskiPrecoverage_isStableUnderComposition`: **the three
  properties the two reductions ask of the precoverage.**

## Implementation notes

The identification is not a definitional unfolding, and it is slightly more than bookkeeping in
one direction. Membership in `AlgebraicGeometry.BigHOver.zariskiPrecoverage` is stated by
exhibiting a `CategoryTheory.PreZeroHypercover.{u + 1}` of the object whose presieve is the given
one and whose image under `AlgebraicGeometry.BigHOver.toScheme` is a Zariski covering of schemes;
membership in the comap asks directly that `CategoryTheory.Presieve.map` of the presieve along
the inclusion be a Zariski covering. A pre-`0`-hypercover is exactly an indexed family of
morphisms, its presieve is `CategoryTheory.Presieve.ofArrows` of that family, and
`CategoryTheory.Presieve.map_ofArrows` says that the image presieve of such a family is the
family of images — so one direction is that rewrite. The other needs a hypercover for an
arbitrary presieve, which is `CategoryTheory.Presieve.exists_eq_ofArrows`: every presieve is
`CategoryTheory.Presieve.ofArrows` of a family indexed by a type of `Type (max u₁ v₁)`, and for
the big h category over `S` — a `Type (u + 1)` whose morphisms lie in `Type u` — that is
`Type (u + 1)`, which is exactly the index universe a
`CategoryTheory.PreZeroHypercover.{u + 1}` wants. The two sides would not meet if the
definition had asked for a smaller index universe.

Mathlib proves the three properties for a comap from the corresponding properties of the target
precoverage, the base-change one needing the functor to preserve fibre products. For the
inclusion of the site that is
`AlgebraicGeometry.schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan` at the site's
cutoff, the same input `AlgebraicGeometry.BigHOver.mem_zariskiPrecoverage_pullback₂` consumes; it
is not found by instance search without that hypothesis in scope, which is why each instance
below puts it there.

## References

* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.BigHOver

universe u

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The Zariski precoverage of the big h category over `S` is the comap of the Zariski
precoverage of schemes along the inclusion of the site.**  A presieve of the site is a Zariski
covering family exactly when the family of its images under
`AlgebraicGeometry.BigHOver.toScheme` is a jointly surjective family of open immersions.

The forwards direction is `CategoryTheory.Presieve.map_ofArrows`, the image presieve of an
indexed family being the family of images.  The backwards direction needs a
`CategoryTheory.PreZeroHypercover.{u + 1}` for an arbitrary presieve, which
`CategoryTheory.Presieve.exists_eq_ofArrows` supplies: the site is a `Type (u + 1)` with
morphisms in `Type u`, so the index type it produces is in `Type (u + 1)`. -/
theorem zariskiPrecoverage_eq_comap :
    zariskiPrecoverage B S hS = Scheme.zariskiPrecoverage.{u}.comap (toScheme B S hS) := by
  ext X R
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨E, rfl, hE⟩
    simpa [PreZeroHypercover.presieve₀, PreZeroHypercover.map, Presieve.map_ofArrows] using hE
  · obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
    refine ⟨⟨ι, Y, f⟩, rfl, ?_⟩
    simpa [PreZeroHypercover.presieve₀, PreZeroHypercover.map, Presieve.map_ofArrows] using h

/-- Singleton families by isomorphisms of the site are Zariski covering families: an
isomorphism of schemes is a surjective open immersion. -/
instance zariskiPrecoverage_hasIsos : (zariskiPrecoverage B S hS).HasIsos := by
  rw [zariskiPrecoverage_eq_comap]
  infer_instance

/-- Zariski covering families of the site are stable under base change, the inclusion of the
site preserving fibre products. -/
instance zariskiPrecoverage_isStableUnderBaseChange :
    (zariskiPrecoverage B S hS).IsStableUnderBaseChange := by
  let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  let : PreservesLimitsOfShape WalkingCospan (toScheme B S hS) := inferInstance
  rw [zariskiPrecoverage_eq_comap]
  infer_instance

/-- Zariski covering families of the site are stable under composition. -/
instance zariskiPrecoverage_isStableUnderComposition :
    (zariskiPrecoverage B S hS).IsStableUnderComposition := by
  rw [zariskiPrecoverage_eq_comap]
  infer_instance

end AlgebraicGeometry.BigHOver

end
