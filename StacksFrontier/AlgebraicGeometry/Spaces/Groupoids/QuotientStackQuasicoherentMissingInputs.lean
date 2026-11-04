module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackQuasicoherentModules
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasicoherentRestrictionAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasicoherentRestrictionAlgebraicSpaceExtensions
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.StackificationModules
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.StackificationModulesExtensions

/-!
# Stacks 06WT reduced to the pointwise quotient

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `A` over a
scheme `S` of a big fppf site, let `𝒳 = [U/R]` be its quotient stack (Stacks 044Q) and `[U/_pR]`
its pointwise quotient.  **Stacks 06WT** asserts that `QCoh(𝒪_𝒳)` is equivalent to the category
`QCoh(U, R, s, t, c)` of quasi-coherent modules on the groupoid (Stacks 0441,
`AlgebraicGeometry.Space.QuasicoherentModule`).

This file states inputs of the proof of Stacks 06WT as named propositions, proves Stacks 06WR for
the stackification map `[U/_pR] ⟶ [U/R]`, and deduces that Stacks 06WT for `[U/R]` is equivalent
to the same statement for `[U/_pR]`.

## Main definitions

* `AlgebraicGeometry.Stack.PresentationRestrictionIsEquivalence`: Stacks 0GQD for the standard
  presentation of every algebraic space of the site.
* `AlgebraicGeometry.Stack.PointwiseQuotientGroupoidEquivalence`: quasi-coherent modules on
  `[U/_pR]` are equivalent to quasi-coherent modules on the groupoid.
* `AlgebraicGeometry.Stack.StackificationQuasicoherentPullbackIsEquivalence`: restriction of
  quasi-coherent modules along `[U/_pR] ⟶ [U/R]` is an equivalence.

## Main results

* `AlgebraicGeometry.Stack.stackificationQuasicoherentPullbackIsEquivalence`: Stacks 06WR for the
  stackification map.
* `AlgebraicGeometry.Stack.nonempty_quasicoherentEquivalenceGroupoid_of_missingInputs`:
  Stacks 06WT for `[U/R]`, assuming it for `[U/_pR]`.
* `AlgebraicGeometry.Stack.pointwiseQuotientGroupoidEquivalence_iff`: Stacks 06WT for `[U/R]` and
  for `[U/_pR]` are equivalent.

## Implementation notes

Quasi-coherent modules on the two quotient stacks are taken at module universe `u + 1`, and those
on the groupoid at module universe `u`.  The equivalences are stated as `Nonempty (… ≌ …)`, so
they do not determine a forward functor.

## References

* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 044S](https://stacks.math.columbia.edu/tag/044S)
* [Stacks Project, Tag 044T](https://stacks.math.columbia.edu/tag/044T)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
* [Stacks Project, Tag 06TM](https://stacks.math.columbia.edu/tag/06TM)
* [Stacks Project, Tag 06WH](https://stacks.math.columbia.edu/tag/06WH)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
* [Stacks Project, Tag 06WR](https://stacks.math.columbia.edu/tag/06WR)
* [Stacks Project, Tag 0GQD](https://stacks.math.columbia.edu/tag/0GQD)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)

/-- **Stacks 0GQD for the standard presentation of an algebraic space.**  For every algebraic
space `F` of the site, restriction to the small étale site of `F` is an equivalence
`QCoh(𝒪_𝒴) ⟶ QCoh(𝒪_F)`, where `𝒴` is the category of elements
`AlgebraicGeometry.Stack.fibredCategory` of `F`, a category fibred in groupoids representable by
`F` with the identity comparison. -/
abbrev PresentationRestrictionIsEquivalence : Prop :=
  ∀ (F : AlgebraicSpaces C S hS)
    (hres : Space.RestrictionPreservesQuasicoherent.{u, u + 1, u, u} C S hS F
      (fibredCategory C S hS F.obj).val.p (fibredCategory C S hS F.obj).property
      (StacksRepresentableCFG.EquivalenceOver.refl _)),
    (Space.quasicoherentRestriction.{u, u + 1, u, u} C S hS F
      (fibredCategory C S hS F.obj).val.p
      (fibredCategory C S hS F.obj).property
      (StacksRepresentableCFG.EquivalenceOver.refl _) hres).IsEquivalence

variable {C S hS} {A : AlgebraicSpaces C S hS}

/-- **Stacks 06WT for the pointwise quotient.**  Quasi-coherent modules on the pointwise quotient
`[U/_pR]` are equivalent to quasi-coherent modules on the groupoid. -/
abbrev PointwiseQuotientGroupoidEquivalence
    (G : GroupoidInAlgebraicSpaces C S hS A) : Prop :=
  Nonempty (FibredSite.quasicoherentModules.{u, u + 1, u + 1, u + 1} C S hS
      (quotientPrestack G).p (isFiberedInGroupoids_quotientPrestack G) ≌
    Space.QuasicoherentModule C S hS G)

/-- The restriction `AlgebraicGeometry.Stack.quotientPrestackQuasicoherentPullback` of
quasi-coherent modules along the stackification map `[U/_pR] ⟶ [U/R]` is an equivalence. -/
abbrev StackificationQuasicoherentPullbackIsEquivalence
    (G : GroupoidInAlgebraicSpaces C S hS A) : Prop :=
  (quotientPrestackQuasicoherentPullback G).IsEquivalence

/-- **Stacks 06WR for the stackification map `[U/_pR] ⟶ [U/R]`**: restriction of quasi-coherent
modules along it is an equivalence. -/
theorem stackificationQuasicoherentPullbackIsEquivalence
    (G : GroupoidInAlgebraicSpaces C S hS A) :
    StackificationQuasicoherentPullbackIsEquivalence G :=
  isEquivalence_quasicoherentPullback_of_isStackificationEquivalence'.{u, u + 1, u + 1, u + 1}
    C S hS (quotientPrestack G).p (quotientStack G).p
    (isFiberedInGroupoids_quotientPrestack G) (isFiberedInGroupoids_quotientStack G)
    (toQuotientStack G) (isFibredOneMorphism_toQuotientStack G)
    ⟨isLocallyBijective_toQuotientStack G, essImage_toQuotientStack G⟩

/-- Quasi-coherent modules on the quotient stack `[U/R]` of a groupoid in algebraic spaces are
equivalent to quasi-coherent modules on the groupoid (Stacks 06WT), provided the same holds for
the pointwise quotient `[U/_pR]`. -/
theorem nonempty_quasicoherentEquivalenceGroupoid_of_missingInputs
    (G : GroupoidInAlgebraicSpaces C S hS A)
    (hqinv : PointwiseQuotientGroupoidEquivalence G) :
    Nonempty (FibredSite.quasicoherentModules.{u, u + 1, u + 1, u + 1} C S hS
        (quotientStack G).p (isFiberedInGroupoids_quotientStack G) ≌
      Space.QuasicoherentModule C S hS G) := by
  let := stackificationQuasicoherentPullbackIsEquivalence G
  exact hqinv.map fun E =>
    (quotientPrestackQuasicoherentPullback G).asEquivalence.trans E

/-- Stacks 06WT for the quotient stack `[U/R]` and Stacks 06WT for the pointwise quotient
`[U/_pR]` are equivalent statements. -/
theorem pointwiseQuotientGroupoidEquivalence_iff
    (G : GroupoidInAlgebraicSpaces C S hS A) :
    PointwiseQuotientGroupoidEquivalence G ↔
      Nonempty (FibredSite.quasicoherentModules.{u, u + 1, u + 1, u + 1} C S hS
          (quotientStack G).p (isFiberedInGroupoids_quotientStack G) ≌
        Space.QuasicoherentModule C S hS G) := by
  let := stackificationQuasicoherentPullbackIsEquivalence G
  exact ⟨nonempty_quasicoherentEquivalenceGroupoid_of_missingInputs G,
    fun h => h.map fun E =>
      (quotientPrestackQuasicoherentPullback G).asEquivalence.symm.trans E⟩

end AlgebraicGeometry.Stack

end
