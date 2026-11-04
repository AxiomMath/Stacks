module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.ShiftedBundleSummand
public import Mathlib.CategoryTheory.Retract

/-!
# A perfect complex on a quasi-compact open is a summand of a restriction

Let `X` be an affine scheme and `U ⊆ X` a quasi-compact open. Every perfect object `P` of
`D(𝒪_U)` is a direct summand of the restriction to `U` of a perfect object of `D(𝒪_X)`. This is
the affine case of [Stacks, Tag 09IQ].

## Main results

* `Stacks.DerivedQCoh.OpenLift.exists_isPerfectComplex_retract_restrict_of_isPerfect` is the
  tag for `X` affine: it produces a perfect complex `M` of `𝒪_X`-modules together with a
  `CategoryTheory.Retract` of `P` into the image under the localization functor of the
  degreewise restriction of `M`.

## Implementation notes

"Direct summand" is `CategoryTheory.Retract`, Mathlib's split-mono/split-epi pair: an inclusion
`i : P ⟶ M|_U`, a retraction `r : M|_U ⟶ P` and the identity `i ≫ r = 𝟙 P`. This is the
faithful reading of the tag, which asserts nothing about the complementary summand.

The proof is immediate from [Stacks, Tag 08EG]: that tag produces an integer `r`, a finite
locally free `𝒪_U`-module `ℱ` and a perfect complex `M` on `X` with `ℱ[-r] ⊕ P ≅ M|_U`, and the
second biproduct injection and projection make `P` a retract of the biproduct, hence of
`M|_U`. The finite locally free sheaf and the shift, which are the content of 08EG, are simply
discarded.

That `M` is a *perfect complex* is the stronger of the two available readings of "perfect object
of `D(𝒪_X)`": `Stacks.Cohomology.PerfectComplexes.IsPerfect (DerivedCategory.Q.obj M)` holds by
definition, with the identity isomorphism as the required representation. Restriction is taken
degreewise on the complex, as in 08EG, so no exactness witnesses for a derived restriction
functor are needed.

The quasi-compact quasi-separated case of 09IQ is *not* proved here: the source deduces it from
[Stacks, Tag 09IM], whose induction over an affine cover needs [Stacks, Tag 08EK] and
[Stacks, Tag 08EH]. Neither of those two carries a `@[stacks]` registration, but their
categorical content is in the library and should be reused rather than redone:
`CategoryTheory.Pretriangulated.exists_isCompactObject_iso_biprod_shift` is 08EK and
`CategoryTheory.Pretriangulated.exists_roof` is 08EH, both in
`StacksFrontier/CategoryTheory/Triangulated/CompactLift.lean`, and
`Stacks.Duality.QcqsGeneration.exists_isCompactObject_restrict_iso_biprod_shift` in
`StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/QcqsCompactGeneration.lean` is already
the geometric instance of 08EK for a quasi-compact open of an affine scheme, in the
compact-object rather than the perfect reading. What that route does **not** supply is the
`E₁ = E ⊗^𝐋 I` clause of 08EH, which is the only reason the source's 08EK and 09IM can conclude
that the lifted object is still supported on `T`; see the discussion in
`StacksFrontier/CategoryTheory/Triangulated/CompactLift.lean`.

## References

* [Stacks Project, Tag 09IQ](https://stacks.math.columbia.edu/tag/09IQ)
* [Stacks Project, Tag 08EG](https://stacks.math.columbia.edu/tag/08EG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect
open Stacks.Cohomology.PerfectComplexes

universe u

namespace Stacks.DerivedQCoh.OpenLift

attribute [local instance 10000] HasDerivedCategory.standard

/-- **[Stacks, Tag 09IQ] for `X` affine.** Let `X` be an affine scheme and `U ⊆ X` a
quasi-compact open. Every perfect object `P` of `D(𝒪_U)` is a direct summand -- a retract -- of
the restriction to `U` of a perfect complex of `𝒪_X`-modules. -/
@[stacks 09IQ "for X affine; the quasi-compact quasi-separated case is deduced in the source
from 09IM, whose induction over an affine cover needs 08EK and 08EH, neither of which this
library has"]
theorem exists_isPerfectComplex_retract_restrict_of_isPerfect
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    (P : DerivedCategory U.toScheme.Modules)
    (hP : IsPerfect (X := U.toScheme.toRingedSpace) P) :
    ∃ M : CochainComplex (OXMod.{u, u, u} X.toRingedSpace) ℤ,
      IsPerfectComplex M ∧
      Nonempty (Retract P (DerivedCategory.Q.obj
        (((AlgebraicGeometry.RingedSpace.restrictModules.{u, u} X.toRingedSpace
          U).mapHomologicalComplex (ComplexShape.up ℤ)).obj M))) := by
  obtain ⟨r, F, M, -, hM, ⟨e⟩⟩ :=
    exists_finiteLocallyFree_biprod_iso_restrict_of_isPerfect X U hU P hP
  exact ⟨M, hM, ⟨{ i := biprod.inr ≫ e.hom, r := e.inv ≫ biprod.snd, retract := by simp }⟩⟩

end Stacks.DerivedQCoh.OpenLift

end
