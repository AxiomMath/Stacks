module

public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Cohomology.ClosedImmersionSections
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.ProjectiveLineVanishing
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveResidueField
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveTwists
public import StacksFrontier.AlgebraicGeometry.Surfaces.ThickeningRestriction

/-!
# Functions extend across the thickenings of an exceptional curve of the first kind

Let `E ⊆ X` be an exceptional curve of the first kind, presented as the projective line by
`e : 𝐏¹_k ≅ E`, and let `Eₙ₊₁ = (D ^ (n + 1)).subscheme` be the infinitesimal thickenings of its
ideal sheaf `D`. `AlgebraicGeometry.Scheme.IdealSheafData.surjective_thickeningRestriction` makes
restriction of global functions `Γ(Eₙ₊₂, 𝒪) ⟶ Γ(Eₙ₊₁, 𝒪)` surjective as soon as
`H¹(X, 𝒪_X(-D ^ (n + 1))|_D)` vanishes, and carries that vanishing as a hypothesis. This file
*discharges* it: for an exceptional curve of the first kind the vanishing is the vanishing of
`H¹(𝐏¹_k, 𝒪(n + 1))`, so the transition maps of the inverse system defining
`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodRing` are surjective with no
cohomological hypothesis at all, and so are the projections out of the limit.

## The chain

Four steps compose, each already available:

* `Stacks.Cohomology.ClosedImmersion.isZero_rightDerived_one_sectionsFunctor_pushforward` moves
  the vanishing from `X` to `E`: the cohomology of a direct image along a closed immersion
  vanishes with the cohomology upstairs.
* `Stacks.ClosedImmersion.unitIsoOfIsIso` identifies a module `𝒢` on `E` with `e_*e^*𝒢`, the
  unit of the adjunction being an isomorphism along an isomorphism of schemes. The same closed
  immersion comparison, applied to the isomorphism `e`, then moves the vanishing from `E` to
  `𝐏¹_k`. (The `Stacks.Cohomology.Hgroup` form of this transport is
  `Stacks.Cohomology.SchemeIso.isZero_Hgroup_pullback_iff`; the composite below stays in the
  `Stacks.Cohomology.sectionsFunctor` spelling that
  `AlgebraicGeometry.Scheme.IdealSheafData.surjective_thickeningRestriction` consumes, so no
  comparison between the two spellings is needed.)
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.nonempty_pullback_negativeTwist_pow_iso_twistingSheaf` identifies `e^*(𝒪_X(-dE)|_E)` with
  the `d`-th twist. Only its *existence* is used, which is all that an equality of Picard
  classes supplies, and all that a vanishing statement needs.
* `Stacks.ProjectiveSpace.Cohomology.isZero_lineCohomology_one_of_neg_one_le` is the vanishing
  `H¹(𝐏¹_k, 𝒪(d)) = 0` for `d ≥ -1`, read off Serre's computation.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.isZero_rightDerived_one_sections_pullback_negativeTwist_pow` — `H¹(E, 𝒪_X(-dE)|_E) = 0`.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.isZero_rightDerived_one_sections_pushforward_pullback_negativeTwist_pow` — the same on `X`,
  in the shape the surjectivity criterion consumes.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.surjective_thickeningRestriction` — **the transition maps are surjective**, with no
  cohomological hypothesis.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.surjective_formalNeighborhoodProjection` — the projections out of the limit are surjective.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.isField_quotient_formalNeighborhoodFiltration_one` — **the residue ring `A / I₁` is a
  field**, with no carried hypothesis. This is the `quotient_isField` input of
  `AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData` discharged outright.

No `@[stacks]` attribute is attached. None of these statements is the assertion of a tag: the
surjectivity is an intermediate step of the proof of [Stacks, Tag 0C2K] whose cohomological
input is [Stacks, Tag 0C4T], and both tags are carried where they are stated.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {D : X.IdealSheafData} {k : Type u} [Field k]
  {e : projectiveLineProj k ≅ D.subscheme}

/-- **`H¹(E, 𝒪_X(-dE)|_E) = 0` for an exceptional curve of the first kind.** The restriction of
the ideal sheaf of the `d`-fold divisor pulls back along `e` to the `d`-th twist on `𝐏¹_k`, whose
first cohomology vanishes because `d ≥ -1`; cohomology is carried back across the isomorphism `e`
by the unit of the pullback–pushforward adjunction together with the closed-immersion
comparison. -/
public theorem
    IsExceptionalCurveOfFirstKind.isZero_rightDerived_one_sections_pullback_negativeTwist_pow
    (hE : IsExceptionalCurveOfFirstKind D k e) (d : ℕ) :
    IsZero (((Stacks.Cohomology.sectionsFunctor D.subscheme ⊤).rightDerived 1).obj
      ((Scheme.Modules.pullback D.subschemeι).obj
        (Stacks.Divisors.negativeTwist (D ^ d)))) := by
  refine IsZero.of_iso ?_
    (((Stacks.Cohomology.sectionsFunctor D.subscheme ⊤).rightDerived 1).mapIso
      (Stacks.ClosedImmersion.unitIsoOfIsIso e.hom _))
  refine (Stacks.Cohomology.ClosedImmersion.isZero_rightDerived_sectionsFunctor_pushforward_iff
    e.hom _ 1).2 ?_
  refine IsZero.of_iso
    (Stacks.ProjectiveSpace.Cohomology.isZero_lineCohomology_one_of_neg_one_le k
      (le_trans (by decide) (Int.natCast_nonneg d)))
    (((Stacks.Cohomology.sectionsFunctor (projectiveLineProj k) ⊤).rightDerived 1).mapIso
      (hE.nonempty_pullback_negativeTwist_pow_iso_twistingSheaf d).some)

namespace IsExceptionalCurveOfFirstKind

/-- **The cohomological input of [Stacks, Tag 0C4T] holds for an exceptional curve of the first
kind.** The first cohomology on `X` of the direct image of `𝒪_X(-dE)|_E` vanishes, which is the
hypothesis of `AlgebraicGeometry.Scheme.IdealSheafData.surjective_thickeningRestriction`. -/
public theorem isZero_rightDerived_one_sections_pushforward_pullback_negativeTwist_pow
    (hE : IsExceptionalCurveOfFirstKind D k e) (d : ℕ) :
    IsZero (((Stacks.Cohomology.sectionsFunctor X ⊤).rightDerived 1).obj
      ((Scheme.Modules.pushforward D.subschemeι).obj
        ((Scheme.Modules.pullback D.subschemeι).obj
          (Stacks.Divisors.negativeTwist (D ^ d))))) :=
  Stacks.Cohomology.ClosedImmersion.isZero_rightDerived_one_sectionsFunctor_pushforward
    D.subschemeι _ (hE.isZero_rightDerived_one_sections_pullback_negativeTwist_pow d)

end IsExceptionalCurveOfFirstKind

/-- **The transition maps of the inverse system of thickenings of an exceptional curve of the
first kind are surjective.** A global function on one infinitesimal thickening extends to the
next, with no cohomological hypothesis: the vanishing that
`AlgebraicGeometry.Scheme.IdealSheafData.surjective_thickeningRestriction` asks for is the
vanishing of `H¹(𝐏¹_k, 𝒪(m + 1))`. -/
public theorem IsExceptionalCurveOfFirstKind.surjective_thickeningRestriction
    (hE : IsExceptionalCurveOfFirstKind D k e) (m : ℕ) :
    Function.Surjective (thickeningRestriction D m) :=
  have : Stacks.Divisors.IsEffectiveCartierDivisor D := hE.isEffectiveCartierDivisor
  _root_.AlgebraicGeometry.Scheme.IdealSheafData.surjective_thickeningRestriction D m
    (hE.isZero_rightDerived_one_sections_pushforward_pullback_negativeTwist_pow (m + 1))

/-- **The projections out of the ring of compatible functions on the thickenings of an
exceptional curve of the first kind are surjective.** Every global function on a thickening is
the restriction of a compatible family of global functions on all of them. -/
public theorem IsExceptionalCurveOfFirstKind.surjective_formalNeighborhoodProjection
    (hE : IsExceptionalCurveOfFirstKind D k e) (n : ℕ) :
    Function.Surjective (formalNeighborhoodProjection D n) :=
  _root_.AlgebraicGeometry.Scheme.IdealSheafData.surjective_formalNeighborhoodProjection D
    hE.surjective_thickeningRestriction n

/-- **The residue ring of the formal neighbourhood of an exceptional curve of the first kind is a
field, with no carried hypothesis.** This is
`AlgebraicGeometry.Scheme.IdealSheafData.isField_quotient_of_isExceptionalCurveOfFirstKind` with
its surjectivity hypothesis discharged, and so the `quotient_isField` input of
`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData` proved outright for an
exceptional curve of the first kind. -/
public theorem IsExceptionalCurveOfFirstKind.isField_quotient_formalNeighborhoodFiltration_one
    (hE : IsExceptionalCurveOfFirstKind D k e) :
    IsField (formalNeighborhoodRing D ⧸ formalNeighborhoodFiltration D 1) :=
  isField_quotient_of_isExceptionalCurveOfFirstKind D k hE hE.surjective_thickeningRestriction

end AlgebraicGeometry.Scheme.IdealSheafData

end
