module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalizedRingedTopos
public import StacksCore.Tactic.StacksAttribute

/-!
# Localization of a locally ringed topos at a sheaf

Let `X` be a ringed topos, presented by a site `(C, J)` with a sheaf of commutative rings
`O`, and let `F` be a sheaf of sets on `C`. Part (5) of Stacks Tag 04IH asserts that the
localization of `X` at `F` — the ringed topos on the site of elements of `F` built in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalizedRingedTopos` — is again *locally
ringed*.

Being locally ringed is Stacks Definition 18.40.4, two conditions on the presenting ringed
site: that `0` and `1` are distinct sections over every object that is not
sheaf-theoretically empty, and that every section is, on some covering, a unit or a co-unit.

## Main definitions

* `Stacks.Sheaves.LocalizedRingedTopos.IsLocallyRingedSite`: the two conditions of Stacks
  Definition 18.40.4 on the ringed site presenting a ringed topos, as a conjunction.

## Main results

* `Stacks.Sheaves.LocalizedRingedTopos.isLocallyRingedSite_localizedRingedTopos`: the
  localization of a locally ringed topos at a sheaf is locally ringed.
* `Stacks.Sheaves.LocalizedRingedTopos.isLocallyRingedSite_of_isLocallyRinged`:
  `Stacks.Sheaves.LocallyRingedTopos.IsLocallyRinged` implies the two site conditions.

## Implementation notes

`IsLocallyRingedSite` is the two-condition notion of Stacks Definition 18.40.4, with
condition (1) in its equivalent sections-level spelling. It differs from
`Stacks.Sheaves.LocallyRingedTopos.IsLocallyRinged`, which also requires every stalk to be a
local ring.

## References

* [Stacks Project, Tag 04IH](https://stacks.math.columbia.edu/tag/04IH)
* [Stacks Project, Tag 04EU](https://stacks.math.columbia.edu/tag/04EU)
-/

@[expose] public section

open CategoryTheory Opposite

namespace Stacks.Sheaves.LocalizedRingedTopos

universe u

/-- A ringed topos is **locally ringed** when its presenting ringed site satisfies the two
conditions of Stacks Definition 18.40.4:

* on every object `U` that is not sheaf-theoretically empty — that is, the empty sieve does
  not cover `U` — the sections `0` and `1` of `O(U)` are distinct;
* every section of `O` is, on some covering, a unit or a co-unit. -/
def IsLocallyRingedSite (X : Stacks.Sheaves.LocallyRingedTopos.RingedTopos.{u}) : Prop :=
  (∀ U : X.C, (⊥ : Sieve U) ∉ X.J U →
      (0 : (((sheafToPresheaf X.J CommRingCat.{u}).obj X.O).obj (op U) : CommRingCat.{u}))
        ≠ 1) ∧
    ∀ (U : X.C)
      (a : (((sheafToPresheaf X.J CommRingCat.{u}).obj X.O).obj (op U) : CommRingCat.{u})),
      Stacks.Sheaves.LocallyRingedTopos.LocallyUnitOrCounit X U a

/-- A ringed topos satisfying `Stacks.Sheaves.LocallyRingedTopos.IsLocallyRinged` satisfies the
two conditions of Stacks Definition 18.40.4. -/
theorem isLocallyRingedSite_of_isLocallyRinged {X :
  Stacks.Sheaves.LocallyRingedTopos.RingedTopos.{u}}
    (hX : Stacks.Sheaves.LocallyRingedTopos.IsLocallyRinged X) : IsLocallyRingedSite X :=
  ⟨hX.nontrivial_on_nonempty, hX.local_units⟩

/-- The localization of a locally ringed topos at a sheaf is again a locally ringed topos. -/
@[stacks 04IH "(5), first assertion: the localization at a sheaf is again locally ringed"]
theorem isLocallyRingedSite_localizedRingedTopos (X :
  Stacks.Sheaves.LocallyRingedTopos.RingedTopos.{u})
    (F : X.Topos) (hX : IsLocallyRingedSite X) :
    IsLocallyRingedSite (localizedRingedTopos X F) :=
  ⟨nontrivial_on_nonempty_localized hX.1, locallyUnitOrCounit_localized hX.2⟩

end Stacks.Sheaves.LocalizedRingedTopos

end
