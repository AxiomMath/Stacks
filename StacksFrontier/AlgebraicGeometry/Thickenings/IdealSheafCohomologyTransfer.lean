module

public import StacksFrontier.AlgebraicGeometry.Thickenings.PicardSequence

/-!
# Transporting the cohomology of the ideal sheaf of a thickening along an isomorphism of modules

The exact sequence of [Stacks Project, Tag 0C6R] (`Stacks.Thickenings.picardBoundary` and
`Stacks.Thickenings.exact_picardRestriction`) ends in the cohomology of
`Stacks.Thickenings.idealAddSheafOnSub`, the defining ideal sheaf of a first-order thickening
`i : X ⟶ X'` restricted to `X` and viewed as a sheaf of abelian groups. A consumer who wants to
*kill* that cohomology — as the proof of [Stacks Project, Tag 0F2D] does, by identifying the
ideal sheaf with a structure sheaf whose `H²` is known to vanish — has the identification
available as an isomorphism of **sheaves of modules**, not of sheaves of abelian groups.

This file supplies the transport. There is nothing to construct: `Stacks.Thickenings.idealAddSheaf`
is by definition `CategoryTheory.SheafOfModules.toSheaf` applied to
`Stacks.Thickenings.idealModuleSheaf`, so an isomorphism of sheaves of modules is carried to an
isomorphism of sheaves of abelian groups by that functor, and
`Stacks.Thickenings.cohomologyEquivOfIso` then moves cohomology across it.

## Main results

* `Stacks.Thickenings.cohomologyIdealAddSheafOnSubEquivOfIso`: for a first-order thickening
  `i : X ⟶ X'` and an isomorphism `ℐ ≅ M` of sheaves of modules on `X'`, an isomorphism
  `Hⁿ(X, ℐ|_X) ≅ Hⁿ(X', M)` of abelian groups.
* `Stacks.Thickenings.forall_eq_zero_cohomology_idealAddSheafOnSub_of_iso`: consequently, if
  `H²(X', M)` vanishes then so does `H²(X, ℐ|_X)`, which is the hypothesis
  `Stacks.PuncturedSpectrumPicard.surjective_picardRestriction_of_forall_eq_zero` and
  `Stacks.PuncturedSpectrumPicard.exists_isCompatible` ask for.

## Implementation notes

The two steps are `Stacks.Thickenings.idealCohomologyEquiv`, which compares the cohomology of
the restricted ideal sheaf on `X` with that of the ideal sheaf on `X'` (available because a
thickening is a homeomorphism), and functoriality of `CategoryTheory.SheafOfModules.toSheaf`
followed by `Stacks.Thickenings.cohomologyEquivOfIso`. Both are data, and so is the result: the
isomorphism is produced, not merely asserted to exist.

This does **not** produce such an isomorphism `ℐ ≅ M` for any particular thickening. For the
tower of infinitesimal neighbourhoods of [Stacks Project, Tag 0F2D] the target `M` would be the
structure sheaf of the bottom stage, and the isomorphism is the multiplication-by-`fⁿ⁺¹` map
determined by a nonzerodivisor `f` cutting out that stage. What this file records is that once
such an isomorphism is given *as a morphism of sheaves of modules*, no further comparison of
categories is needed to reach the `H²` hypothesis: the apparent mismatch between
`TopCat.Sheaf AddCommGrpCat`, where the cohomology is taken, and
`CategoryTheory.SheafOfModules`, where the conormal and ideal sheaves live, is only the
application of a functor.

## References

* [Stacks Project, Tag 0C6R](https://stacks.math.columbia.edu/tag/0C6R)
* [Stacks Project, Tag 0F2D](https://stacks.math.columbia.edu/tag/0F2D)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Thickenings

attribute [local implicit_reducible]
  TopCat.Sheaf
  structureSheafRing
  SheafOfModules.toSheaf

/- `Ext`-groups of abelian sheaves on a topological space are computed in the universe of the
sections, because the category of abelian sheaves has enough injectives. The instance
`Stacks.Thickenings.hasExtAbelianSheaf` is local where it is declared, and
`CategoryTheory.Sheaf.H` cannot be written without it. -/
attribute [local instance] hasExtAbelianSheaf

variable {X X' : Scheme.{u}} (i : X ⟶ X') (hi : IsFirstOrderThickening i)

/-- **The cohomology of the ideal sheaf of a first-order thickening, transported along an
isomorphism of sheaves of modules.** If the defining ideal sheaf `ℐ` of a first-order thickening
`i : X ⟶ X'`, as a sheaf of modules on `X'`, is isomorphic to `M`, then the cohomology of `ℐ`
restricted to `X` — the group the exact sequence of [Stacks Project, Tag 0C6R] ends in — is the
cohomology of `M` on `X'`.

The first step is `Stacks.Thickenings.idealCohomologyEquiv`: a thickening is a homeomorphism, so
restricting the ideal sheaf to `X` does not change its cohomology. The second is functoriality
of `CategoryTheory.SheafOfModules.toSheaf`, of which `Stacks.Thickenings.idealAddSheaf` is an
instance by definition, followed by `Stacks.Thickenings.cohomologyEquivOfIso`. -/
def cohomologyIdealAddSheafOnSubEquivOfIso
    {M : SheafOfModules.{u} (structureSheafRing X'.toSheafedSpace)}
    (e : idealModuleSheaf i ≅ M) (n : ℕ) :
    CategoryTheory.Sheaf.H.{u} (idealAddSheafOnSub i) n ≃+
      CategoryTheory.Sheaf.H.{u}
        ((SheafOfModules.toSheaf (structureSheafRing X'.toSheafedSpace)).obj M) n :=
  (idealCohomologyEquiv i hi n).trans
    (cohomologyEquivOfIso
      ((SheafOfModules.toSheaf (structureSheafRing X'.toSheafedSpace)).mapIso e) n)

include hi in
/-- **Vanishing `H²` for the ideal sheaf of a first-order thickening, from an isomorphism of
sheaves of modules.** If the defining ideal sheaf of a first-order thickening `i : X ⟶ X'` is
isomorphic as a sheaf of modules to `M` and the second cohomology of `M` on `X'` vanishes, then
the second cohomology of the restricted ideal sheaf on `X` vanishes.

This is the hypothesis that
`Stacks.PuncturedSpectrumPicard.surjective_picardRestriction_of_forall_eq_zero` and
`Stacks.PuncturedSpectrumPicard.exists_isCompatible` take, so this lemma reduces that hypothesis
to a statement about sheaves of modules. -/
theorem forall_eq_zero_cohomology_idealAddSheafOnSub_of_iso
    {M : SheafOfModules.{u} (structureSheafRing X'.toSheafedSpace)}
    (e : idealModuleSheaf i ≅ M)
    (hM : ∀ y : CategoryTheory.Sheaf.H.{u}
      ((SheafOfModules.toSheaf (structureSheafRing X'.toSheafedSpace)).obj M) 2, y = 0)
    (x : CategoryTheory.Sheaf.H.{u} (idealAddSheafOnSub i) 2) :
    x = 0 :=
  (cohomologyIdealAddSheafOnSubEquivOfIso i hi e 2).map_eq_zero_iff.mp (hM _)

end Stacks.Thickenings

end
