module

public import StacksFrontier.Deformation.Examples.Linear.NodalCubicLocal

/-!
# A rank-two `(P')_g`-module that is NOT the local lift — and the record of why

Eighth layer of the instantiation of `Deformation.FlatModuleLiftBaseChangeStatement`.

**WARNING, AND THE POINT OF KEEPING THIS FILE.** The object `L_g = (N'₁)_ĝ` built below is a
perfectly good `A'`-flat `(P')_g`-module, and the three results about it are true. It is **not a
lift of `M_g`**, and the comparison equivalence that `hlocal` demands of it is **false**, so the
plan this file's first version recorded cannot be carried out. `N'₁ = A'[α]/(α² + α − Y)` is free
of rank *two* over `A'`, so `L_g/t·L_g` is free of rank two over `(NC)_{…}`, whereas
`M_g = (NC)_{…}` is free of rank *one*. For `g = Y` it is visible outright: `α² + α − Y` already
has the root `Z/Y` over `(NC)_Y` — that is exactly `exists_isASSol_of_isUnit_ncY` — so
`L_Y/t·L_Y ≅ (NC)_Y × (NC)_Y`, which has nontrivial idempotents and is not `(NC)_Y`.

The mistake is worth keeping visible because it is the natural one. Adjoining the Artin–Schreier
root is **right on the `Q'` side**, where the root genuinely has to be adjoined, and **wrong on the
local side**, where the root is already present: `Y` is a unit in `(P')_g` for every
`g ∈ J' = Y·P'` (`isUnit_omegaP_away`), so `α = Z/Y` lives in `(P')_g` itself and adjoining a
second copy doubles the rank.

The correct local lift is the one layer seven named and this file talked itself out of — `(P')_g`
modulo `x − t·α` — and it is built in
`StacksFrontier.Deformation.Examples.Linear.NodalCubicLocalAway` and
`StacksFrontier.Deformation.Examples.Linear.NodalCubicLocalModule`, where the two obstacles this
file raised against it are dealt with: the chosen inverse of `Y` is avoided by cutting with
`u = Y·x − t·Z` instead, which does not depend on `g`; and flatness is obtained not from a
presentation of `(P')_g` but by *identifying* the quotient with `((A')_Y)_{π g}`, a localization
of a localization of `A'`.

## The argument of this file that does survive

The reason given here for not routing the lift through `(P')_Y` and
`Deformation.HasFlatModuleLift.baseChange` still stands, and it is why no transport appears
anywhere in layers 13–15: `J'` is principal, so for `g = Y·c` the image of `Y` divides a unit and
is a unit, and the root exists at each `g` directly from `Z² + Y·Z = Y³`. The cost that transport
would have added also still stands: `HasFlatModuleLift`'s witness is an object of
`ModuleCat.{max u₃ v} P'` carrying a `Module.compHom` structure, whereas `hlocal` asks for
`Module A' L` with `IsScalarTower A' (Localization.Away g) L`.

## Main definitions

* `Deformation.Examples.ArtinSchreier.LocalLift`: `(N'₁)_ĝ`. **Not a lift of `M_g`** — see above.
* `Deformation.Examples.ArtinSchreier.awayToLocalLift`: the map `(P')_g → (N'₁)_ĝ`.

## Main results

* `Deformation.Examples.ArtinSchreier.flat_LocalLift`: `Module.Flat A' ((N'₁)_ĝ)` — true, and
  reused in spirit by `NodalCubicLocalModule.flat_AYAway`.
* `Deformation.Examples.ArtinSchreier.isUnit_g_localLift`: `g` is a unit in `(N'₁)_ĝ`.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
-/

@[expose] public noncomputable section

open Polynomial
open Deformation.Examples.MaurerCartanWindow

universe u

namespace Deformation.Examples.ArtinSchreier

/-- `N'₁ = A'[α]/(α² + α − Y)` localized at the image of `g` under `x ↦ t·α`.

**This is not a lift of `M_g`**: it is free of rank two over `A'` where `M_g` has rank one. See
this file's module documentation; the local lift is
`Deformation.Examples.ArtinSchreier.LocalModule`. -/
abbrev LocalLift (g : PBase) : Type := Localization.Away (pBaseToNOne g)

/-- `(N'₁)_ĝ` is flat over `A'`: `N'₁` is free of rank two over `A'` and `(N'₁)_ĝ` is a
localization of it, so this is `Module.Flat.trans` of a free module and a flat one. True, but
about the wrong object for `hlocal` — see this file's module documentation. -/
theorem flat_LocalLift (g : PBase) : Module.Flat ABase (LocalLift g) := by
  have := free_NOne
  have : Module.Flat ABase NOne := Module.Flat.of_free
  have : Module.Flat NOne (LocalLift g) :=
    IsLocalization.flat (Localization.Away (pBaseToNOne g))
      (Submonoid.powers (pBaseToNOne g))
  exact Module.Flat.trans ABase NOne (LocalLift g)

/-- `g` becomes a unit in `L_g`, by construction of the localization. -/
theorem isUnit_g_localLift (g : PBase) :
    IsUnit (algebraMap NOne (LocalLift g) (pBaseToNOne g)) :=
  IsLocalization.map_units _
    (⟨pBaseToNOne g, Submonoid.mem_powers _⟩ : Submonoid.powers (pBaseToNOne g))

/-- The map `(P')_g → (N'₁)_ĝ`, which makes `(N'₁)_ĝ` a module over `(P')_g`. It exists because
`g` is a unit there, so the universal property of the localization applies. -/
def awayToLocalLift (g : PBase) : Localization.Away g →+* LocalLift g :=
  IsLocalization.lift (M := Submonoid.powers g)
    (g := (algebraMap NOne (LocalLift g)).comp pBaseToNOne) (by
      intro y
      obtain ⟨k, hk⟩ := y.2
      have hval : ((algebraMap NOne (LocalLift g)).comp pBaseToNOne) (y : PBase) =
          (algebraMap NOne (LocalLift g) (pBaseToNOne g)) ^ k := by
        rw [← hk, RingHom.comp_apply, map_pow, map_pow]
      rw [hval]
      exact IsUnit.pow _ (isUnit_g_localLift g))

end Deformation.Examples.ArtinSchreier

end
