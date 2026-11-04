module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportedBiprodShiftLift
public import StacksFrontier.AlgebraicGeometry.RestrictionAlongNestedOpens

/-!
# The inclusion of one open in another, and the two ways of writing its restriction

For opens `U ≤ W` of a scheme `X` the inclusion `U ⟶ W` is written two ways in this development,
and the two spellings meet in the two-open step of [Stacks, Tag 09IM].

* `AlgebraicGeometry.Scheme.homOfLE`, read on underlying sheafed spaces. This is the spelling of
  the two legs of the Cartesian square `Stacks.RestrictionSpellings.isPullback_ofRestrict_inf`,
  hence the one in which the overlap of a two-open glueing arrives from [Stacks, Tag 08DG] — see
  `Stacks.Perfect.SupportedLiftTwoOpens.exists_isPerfect_supported_hom_of_overlap_iso`.
* the inclusion of `Stacks.Cohomology.ClosedSupportPerfect.nestedOpenOfLE U W`, the copy of `U`
  inside `W`, followed by the comparison
  `Stacks.Cohomology.ClosedSupportPerfect.restrictNestedIsoRestrict`. This is the spelling of
  [Stacks, Tag 08EK] and of the affine case of [Stacks, Tag 09IM], where the inner open is given
  as an open of the subspace — see
  `Stacks.Perfect.SupportedBiprodShift.derivedRestrictNestedObjIso` and
  `exists_isPerfect_supported_hom_biprod_shift_iso_restrict_of_isAffine` of
  `Stacks.Perfect.SupportedLiftAffine`.

The two are *equal*, not merely isomorphic, and this file proves it once:
`Stacks.NestedRestrictionOfLE.homOfLE_toShHom_eq`. On derived categories the equality then gives
a natural isomorphism, `Stacks.NestedRestrictionOfLE.derivedPullbackNestedHomOfLEIso`,
identifying restriction along `X.homOfLE h` with restriction to the copy of `U` inside `W`
followed by the comparison of the two presentations of `X|_U`.

## Main results

* `Stacks.NestedRestrictionOfLE.eq_nested_of_comp`: **any** morphism `X|_U ⟶ X|_W` of ringed
  spaces which is compatible with the two inclusions into `X` is the nested inclusion. The
  inclusion of an open subspace is a monomorphism, so there is only one such morphism.
* `Stacks.NestedRestrictionOfLE.homOfLE_toShHom_comp_ofRestrict` and
  `Stacks.NestedRestrictionOfLE.homOfLE_toShHom_eq`: `AlgebraicGeometry.Scheme.homOfLE` is that
  morphism.
* `Stacks.NestedRestrictionOfLE.derivedPullbackNestedHomOfLEIso`: the resulting comparison of
  derived restriction functors.
* `Stacks.NestedRestrictionOfLE.isCompact_nestedOpenOfLE`: the copy of a quasi-compact open
  inside a larger open is quasi-compact, which is the hypothesis the affine case of
  [Stacks, Tag 09IM] takes on the open it is applied at.
* `Stacks.NestedRestrictionOfLE.isCompact_inf`: in a quasi-separated space the intersection of
  two quasi-compact opens is quasi-compact — the overlap of the two-open step.

## Implementation notes

`AlgebraicGeometry.Scheme.homOfLE` is characterised by `AlgebraicGeometry.Scheme.homOfLE_ι`, so
the equality is proved by cancelling the inclusion of `W`, which is a monomorphism, being an open
immersion; the nested inclusion satisfies the same identity by
`Stacks.Perfect.SupportedBiprodShift.restrictNestedIsoRestrict_hom_comp_ofRestrict`. The
cancellation is performed in `Stacks.NestedRestrictionOfLE.eq_nested_of_comp`, at a ringed space
where every object is written as `AlgebraicGeometry.SheafedSpace.restrict`: at the scheme level
the two subspaces are spelled `U.toScheme.toSheafedSpace`, which is the `restrict` form only
after unfolding.

Nothing here defines a restriction along `X.homOfLE h`; the derived comparison is
`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical` on the factorisation.

## References

* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
* [Stacks Project, Tag 08EK](https://stacks.math.columbia.edu/tag/08EK)
* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.ClosedSupportPerfect (nestedOpenOfLE restrictNestedIsoRestrict)
open Stacks.Perfect.SupportedBiprodShift (restrictNestedIsoRestrict_hom_comp_ofRestrict)

universe u

namespace Stacks.NestedRestrictionOfLE

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Point-set facts about the opens involved -/

/-- **The copy of a quasi-compact open inside a larger open is quasi-compact.** For `U ≤ W` opens
of a ringed space, `Stacks.Cohomology.ClosedSupportPerfect.nestedOpenOfLE U W` is the preimage of
`U` in `W`, and the subtype inclusion of `W` is an embedding carrying it onto `U`. -/
theorem isCompact_nestedOpenOfLE {X : RingedSpace.{u, u}} (U W : Opens X) (hUW : U ≤ W)
    (hU : IsCompact ((U : Opens X) : Set X)) :
    IsCompact ((nestedOpenOfLE U W : Opens (X.restrict W.isOpenEmbedding)) :
      Set (X.restrict W.isOpenEmbedding)) := by
  change IsCompact ((Subtype.val : ↥W → X.carrier) ⁻¹' (U : Set X))
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  have himage : (Subtype.val : ↥W → X.carrier) ''
      ((Subtype.val : ↥W → X.carrier) ⁻¹' (U : Set X)) = (U : Set X) := by
    ext x
    refine ⟨?_, fun hx => ⟨⟨x, hUW hx⟩, hx, rfl⟩⟩
    rintro ⟨y, hy, rfl⟩
    exact hy
  rwa [himage]

/-- **In a quasi-separated space the intersection of two quasi-compact opens is quasi-compact.** -/
theorem isCompact_inf {Y : TopCat.{u}} [QuasiSeparatedSpace Y] (U V : Opens Y)
    (hU : IsCompact ((U : Opens Y) : Set Y)) (hV : IsCompact ((V : Opens Y) : Set Y)) :
    IsCompact ((U ⊓ V : Opens Y) : Set Y) :=
  QuasiSeparatedSpace.inter_isCompact _ _ U.2 hU V.2 hV

/-! ### The inclusion of one open in another -/

/-- **There is only one morphism `X|_U ⟶ X|_W` compatible with the inclusions into `X`,** and it
is the inclusion of the copy of `U` inside `W` read through the comparison
`Stacks.Cohomology.ClosedSupportPerfect.restrictNestedIsoRestrict`.

The inclusion of an open subspace is an open immersion, hence a monomorphism, and the nested
inclusion satisfies the identity by
`Stacks.Perfect.SupportedBiprodShift.restrictNestedIsoRestrict_hom_comp_ofRestrict`. -/
theorem eq_nested_of_comp {X : RingedSpace.{u, u}} (U W : Opens X) (hUW : U ≤ W)
    (f : X.restrict U.isOpenEmbedding ⟶ X.restrict W.isOpenEmbedding)
    (hf : f ≫ X.ofRestrict W.isOpenEmbedding = X.ofRestrict U.isOpenEmbedding) :
    f = (restrictNestedIsoRestrict U W hUW).inv ≫
      (X.restrict W.isOpenEmbedding).ofRestrict (nestedOpenOfLE U W).isOpenEmbedding := by
  rw [← cancel_mono (X.ofRestrict W.isOpenEmbedding), hf, Category.assoc,
    ← restrictNestedIsoRestrict_hom_comp_ofRestrict U W hUW, Iso.inv_hom_id_assoc]

variable (X : Scheme.{u}) {U W : X.Opens}

/-- **`X.homOfLE h` is compatible with the inclusions of the two opens into `X`.** This is
`AlgebraicGeometry.Scheme.homOfLE_ι` read on underlying sheafed spaces, where the inclusion of an
open subscheme is `AlgebraicGeometry.SheafedSpace.ofRestrict` on the nose. -/
theorem homOfLE_toShHom_comp_ofRestrict (h : U ≤ W) :
    (X.homOfLE h).toLRSHom.toShHom ≫ X.toRingedSpace.ofRestrict W.isOpenEmbedding =
      X.toRingedSpace.ofRestrict U.isOpenEmbedding :=
  congrArg (fun k : U.toScheme ⟶ X => k.toLRSHom.toShHom) (X.homOfLE_ι h)

/-- **The inclusion of one open in another is the nested inclusion.** For `U ≤ W` opens of a
scheme, `AlgebraicGeometry.Scheme.homOfLE h` read on underlying sheafed spaces is the inclusion
of the copy of `U` inside `W`, composed with the comparison of the two presentations of `X|_U`. -/
theorem homOfLE_toShHom_eq (h : U ≤ W) :
    (X.homOfLE h).toLRSHom.toShHom =
      (restrictNestedIsoRestrict U W h).inv ≫
        (X.toRingedSpace.restrict W.isOpenEmbedding).ofRestrict
          (nestedOpenOfLE U W).isOpenEmbedding :=
  eq_nested_of_comp U W h _ (homOfLE_toShHom_comp_ofRestrict X h)

/-! ### The comparison of derived restriction functors -/

/-- **Restriction to the copy of `U` inside `W` is restriction along `X.homOfLE h`,** after the
comparison of the two presentations of `X|_U`, as an isomorphism of functors `D(𝒪_W) ⥤ D(𝒪_U)`.

The whiskering is the *first* factor rather than the last: written the other way round, the
derived category of the doubly restricted space is elaborated before the second functor is
known, and `CategoryTheory.HasDerivedCategory` is resolved at the wrong universe for it. -/
def derivedPullbackNestedHomOfLEIso (h : U ≤ W) :
    AlgebraicGeometry.RingedSpace.derivedRestrictModules
          (X.toRingedSpace.restrict W.isOpenEmbedding) (nestedOpenOfLE U W) ⋙
        derivedPullback (restrictNestedIsoRestrict U W h).inv ≅
      derivedPullback ((X.homOfLE h).toLRSHom.toShHom) :=
  Functor.isoWhiskerRight
      (AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoDerivedPullback
        (X.toRingedSpace.restrict W.isOpenEmbedding) (nestedOpenOfLE U W))
      (derivedPullback (restrictNestedIsoRestrict U W h).inv) ≪≫
    Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      (restrictNestedIsoRestrict U W h).inv
      ((X.toRingedSpace.restrict W.isOpenEmbedding).ofRestrict
        (nestedOpenOfLE U W).isOpenEmbedding) ≪≫
    eqToIso (congrArg (fun f : X.toRingedSpace.restrict U.isOpenEmbedding ⟶
        X.toRingedSpace.restrict W.isOpenEmbedding => derivedPullback f)
      (homOfLE_toShHom_eq X h).symm)

end Stacks.NestedRestrictionOfLE

end
