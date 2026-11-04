module

public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.PerfectBoundedCoherent
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization

/-!
# Perfect objects and bounded coherent objects on a regular scheme

Let `X` be a regular scheme. Then the perfect objects of `D(𝒪_X)` and the objects of
`D^b_{Coh}(𝒪_X)` coincide, provided `X` is quasi-compact — which for a regular scheme is the
same as being Noetherian. This file proves that every perfect object is bounded with coherent
cohomology, which is the converse half of [Stacks, Tag 0FDC].

## Main results

* `AlgebraicGeometry.isLocallyNoetherian_of_isRegular`: a regular scheme is locally Noetherian.
* `Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect_of_isRegular`: the
  converse half of [Stacks, Tag 0FDC]. On a quasi-compact regular scheme every perfect object of
  the derived category of `𝒪_X`-modules is bounded with coherent cohomology.

## Implementation notes

The hypotheses are the ones the source states for its converse: `X` is regular and
quasi-compact. Regularity is unused beyond supplying local Noetherianity, which with
quasi-compactness is Noetherianity, and that is all
`Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect` ([Stacks, Tag 0FXU])
needs; so the statement here is not a strengthening of that result but its reading at the
hypotheses of [Stacks, Tag 0FDC].

Local Noetherianity of a regular scheme is extracted from the characterization
`AlgebraicGeometry.isRegular_tfae` ([Stacks, Tag 02IT]) of regularity as local Noetherianity
together with regularity of every local ring. The definition
`AlgebraicGeometry.IsRegular` only asks for *some* affine open neighbourhood with regular ring of
sections around each point, and `AlgebraicGeometry.IsRegularRing` contains Noetherianity, so the
characterization is what turns that into a statement about every affine open.

The *forward* half of [Stacks, Tag 0FDC] — on an arbitrary regular scheme every object of
`D^b_{Coh}(𝒪_X)` is perfect — is not proved here, and the attribute below does not claim it. It is
`Stacks.AlgebraicGeometry.PerfectCohomology.isPerfect_of_isBoundedCoherent_of_isRegular`, and the
two halves are assembled into the equivalence by
`Stacks.AlgebraicGeometry.PerfectCohomology.isPerfect_iff_isBoundedCoherent_of_isRegular`.

## References

* [Stacks Project, Tag 0FDC](https://stacks.math.columbia.edu/tag/0FDC)
* [Stacks Project, Tag 0FXU](https://stacks.math.columbia.edu/tag/0FXU)
* [Stacks Project, Tag 02IT](https://stacks.math.columbia.edu/tag/02IT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u d

namespace AlgebraicGeometry

/-- **A quasi-compact regular scheme is Noetherian.** This is the parenthetical identification
made by [Stacks, Tag 0FDC]: for a regular scheme, quasi-compactness is Noetherianity. -/
theorem isNoetherian_of_isRegular {X : Scheme.{u}} (hX : IsRegular X) [CompactSpace X] :
    IsNoetherian X :=
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  ⟨⟩

end AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.PerfectCohomology

/-- **The converse half of [Stacks, Tag 0FDC].** Let `X` be a regular scheme which is
quasi-compact — equivalently, Noetherian and regular. Then every perfect object of the derived
category of `𝒪_X`-modules lies in `D^b_{Coh}(𝒪_X)`: it is bounded and all of its cohomology
sheaves are coherent.

Regularity enters only through local Noetherianity, so this is
`Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect`
([Stacks, Tag 0FXU]) read at the hypotheses of [Stacks, Tag 0FDC]. -/
@[stacks 0FDC "converse direction only: a perfect object on a quasi-compact regular scheme is \
bounded with coherent cohomology"]
theorem isBoundedCoherent_of_isPerfect_of_isRegular
    (X : Scheme.{u}) (hX : IsRegular X) [CompactSpace X]
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)]
    (K : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K) :
    DerivedCategoryB.derivedCategoryBBounded
      (fun M : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace => M.IsCoherent) K :=
  have : IsNoetherian X := isNoetherian_of_isRegular hX
  isBoundedCoherent_of_isPerfect X K hK

end Stacks.AlgebraicGeometry.PerfectCohomology

end
