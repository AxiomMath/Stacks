module

public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.ToposLocalization
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedTopoi.InverseImage
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Morphisms
import StacksCore.Tactic.StacksAttribute

/-!
# The localization of a locally ringed topos is locally ringed

Let `X` be a ringed topos whose presenting ringed site is locally ringed (Stacks 04EU), and let
`F` be a sheaf of sets on it. Stacks 04IE localizes `X` at `F`: the site is the site of elements
of `F`, and the structure sheaf is the restriction of `O` along the projection to the site of
`X`. This file proves that the presenting ringed site of that localization is again locally
ringed, which is the first assertion of part (5) of Stacks 04IH.

## Main results

* `AlgebraicGeometry.RingedTopos.localizedRingedTopos_isLocallyRinged`: **Stacks 04IH (5), first
  assertion**, the localization of a locally ringed topos at a sheaf is locally ringed.

## Implementation notes

No new argument about sections is needed, and in particular neither condition is reproved on the
site of elements. The structure sheaf of the localization is, up to the canonical identification
`AlgebraicGeometry.RingedTopos.localizationInverseImageCommRingIso`, the inverse image of `O`
along the localization morphism of topoi; so the statement is an instance of Stacks 04H7 part
(1), `AlgebraicGeometry.RingedSite.isLocallyRinged_inverseImage`, transported along that
identification by `AlgebraicGeometry.RingedSite.isLocallyRinged_of_iso`. Both conditions of
`AlgebraicGeometry.RingedSite.IsLocallyRinged` are carried by the inverse image for the reasons
recorded there: nonvanishing of `1` because the inverse image is a left exact left adjoint, and
the local-unit condition through its categorical form.

The sectionwise form of the same transfer is already in the library for the single-universe
presentation `Stacks04H9.RingedTopos`, as
`Stacks.Sheaves.LocalizedRingedTopos.nontrivial_on_nonempty_localized` and
`.locallyUnitOrCounit_localized`. Those two are not usable here: they are stated for the
conditions of Stacks 04H9, whereas `AlgebraicGeometry.RingedSite.IsLocallyRinged` takes
nonvanishing of `1` in the categorical form of Stacks 05D7, and no bridge between the two forms
is available.

**On the clause this file carries.** Stacks 04IH has eight numbered parts; this is the first
assertion of part (5), that the localization of a locally ringed topos at a sheaf is again a
locally ringed topos. The second assertion of part (5), that the localization morphism is a
morphism of locally ringed topoi, is
`AlgebraicGeometry.RingedTopos.localizationMorphism_isLocallyRinged` in
`StacksFrontier/AlgebraicGeometry/Recovery04IH/LocalizationMorphismsLocallyRinged.lean`; the
localization of a *morphism* of ringed topoi, Stacks 04IF, is part (7) and is
`AlgebraicGeometry.RingedToposHom.localized_isLocallyRinged` in
`StacksFrontier/AlgebraicGeometry/Recovery04IH/LocalizedMorphismsLocallyRinged.lean`. (An earlier
note here said the tag has ten clauses and that 04IF was unavailable; both were wrong.)

The same part (5) is also registered in two sectionwise spellings:
`Stacks.Sheaves.LocalizedRingedTopos.isLocallyRingedSite_localizedRingedTopos` and
`Stacks.Sheaves.LocallyRingedSite.localizedRingedTopos_isLocallyRinged`. This statement is the
one in the categorical spelling `AlgebraicGeometry.RingedSite.IsLocallyRinged`, which is the
hypothesis the morphism clauses above consume.

## References

* [Stacks Project, Tag 04EU](https://stacks.math.columbia.edu/tag/04EU)
* [Stacks Project, Tag 04H7](https://stacks.math.columbia.edu/tag/04H7)
* [Stacks Project, Tag 04IE](https://stacks.math.columbia.edu/tag/04IE)
* [Stacks Project, Tag 04IH](https://stacks.math.columbia.edu/tag/04IH)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedTopos

/-- **Stacks 04IH (5), first assertion.** The localization `(Sh(C)/F, O_F)` of a locally ringed
topos at a sheaf of sets is again a locally ringed topos: its structure sheaf is the inverse
image of `O` along the localization morphism of topoi, and local ringedness passes to an inverse
image. -/
@[stacks 04IH "(5), first assertion: the localization `(Sh(C)/F, O_F)` of a locally ringed topos
at a sheaf is again a locally ringed topos, in the categorical spelling of local ringedness"]
theorem localizedRingedTopos_isLocallyRinged (X : RingedTopos.{u, u, u}) (F : X.Topos)
    (hX : RingedSite.IsLocallyRinged (toRingedSite X)) :
    RingedSite.IsLocallyRinged (toRingedSite (localizedRingedTopos X F)) :=
  RingedSite.isLocallyRinged_of_iso (localizationInverseImageCommRingIso X F)
    (RingedSite.isLocallyRinged_inverseImage (elementSite X F) (elementTopology X F)
      (toRingedSite X) (localizationToposMorphism X F) hX)

end AlgebraicGeometry.RingedTopos

end
