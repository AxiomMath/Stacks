module

public import StacksFrontier.Deformation.Examples.Linear.NodalCubicModule

/-!
# The local liftability input of the Stacks 0DZ2 counterexample

Seventh layer of the instantiation of `Deformation.FlatModuleLiftBaseChangeStatement`. Stacks
0DZ2 assumes that for every `g` in the ideal `J'` the localization `M_g` has an `A'`-flat
`(P')_g`-module lift. This file proves the **mathematical content** of that hypothesis for the
counterexample, uniformly in `g` and with no transport:

for every `g ∈ J' = Y·P'`, the Artin–Schreier equation `α·α + α = Y` has a solution over
`(P')_g`.

The reason it is uniform is that `J'` is **principal**. For `g = Y·c` the image of `Y` divides a
unit in `(P')_g`, hence is itself a unit there (`isUnit_omegaP_away`), and then
`exists_isASSol_of_isUnit_ncY` of
`StacksFrontier.Deformation.Examples.Linear.NodalCubicBase` produces the root `α = Z/Y` — because
`Z² + Y·Z = Y³` is the defining relation of the nodal cubic. So there is one verification here,
not a family, and no appeal to the forward half of Stacks 0DZ2 to carry a single local lift from
`(P')_Y` to the other `(P')_g`.

By the classification `Deformation.Examples.ArtinSchreier.twisted_lift_iff`, a solution of that
equation over a base is exactly an `A'`-flat lift of `M` over the twisted thickening of that
base. What remained between this file and `hlocal` as
`Deformation.FlatModuleLiftBaseChangeStatement` states it was **mostly** packaging — but not
entirely, and the part that was not is recorded below: the module whose existence this root
asserts has to be a quotient of `(P')_g`, not an `(P')_g`-algebra with the root adjoined, and
getting that wrong makes the comparison equivalence false rather than merely unproved.

## The local hypothesis `hlocal`

`hlocal` is stated in the shape

`∃ (L : Type u) (_ : AddCommGroup L) (_ : Module (Localization.Away g) L) (_ : Module A' L)`
`(_ : IsScalarTower A' (Localization.Away g) L), Module.Flat A' L ∧ Nonempty (…)`

with the comparison taken in `Localization.Away (algebraMap P' P g)` against
`Localization.Away (algebraMap P' P g) ⊗[P] M`, and with the `Algebra` between the two
localizations supplied by `Localization.awayMap`. It is discharged by
`Deformation.Examples.ArtinSchreier.hlocal_nodal`. Three points of the
construction deserve comment:

1. the lift itself. One might try `(Localization.Away g)[α]/(α² + α − Y)` modulo `x − t·α`,
   whose adjoined-root version is built in
   `StacksFrontier.Deformation.Examples.Linear.NodalCubicLocalLift`. **Adjoining the root here is wrong**: `Y` is already a unit over `(P')_g`, so
   the root `Z/Y` is already present and adjoining a second copy makes a rank-two module where
   `M_g` has rank one. The lift is `(P')_g ⧸ (Y·x − t·Z)`
   (`StacksFrontier.Deformation.Examples.Linear.NodalCubicLocalModule`), with `Y·x − t·Z` being
   `x − t·Z/Y` with the denominator cleared so that it does not depend on `g`;
2. the comparison equivalence, which one might expect to be a chain of `cancelBaseChange`
   steps. **No chain is needed.** With the lift presented as a quotient of `(P')_g` and `M` as
   `P/(x)`, `Algebra.TensorProduct.quotIdealMapEquivTensorQuot` — which is linear over the left
   factor, i.e. over `(P)_ḡ`, exactly the linearity the statement demands — turns both sides into
   quotients of `(P)_ḡ`, and the comparison becomes the identity of two ideals: `t` dies in
   `(P)_ḡ`, so `u = Y·x − t·Z` has image `Y·x`, and `Y` is a unit there, so `(Y·x) = (x)`;
3. the conversion from `Deformation.HasFlatModuleLift.baseChange`'s `ModuleCat` witness is not
   needed at all, because no transport from `(P')_Y` is used — which is what `J'` principal buys,
   as this file says.

## Main results

* `Deformation.Examples.ArtinSchreier.algebraMap_NC_PBase_ncY`: the image of `Y` from the base in
  `P'` is `omegaP`, so the two ways of naming the class agree.
* `Deformation.Examples.ArtinSchreier.isUnit_omegaP_away`: **`Y` is a unit in `(P')_g` for every
  `g ∈ J'`** — this is what `J'` principal buys.
* `Deformation.Examples.ArtinSchreier.exists_isASSol_away`: **the Artin–Schreier equation for `Y`
  is solvable over `(P')_g` for every `g ∈ J'`**, by `α = Z/Y`. This is the local liftability
  hypothesis of Stacks 0DZ2 for the counterexample, up to the packaging named above.
* `Deformation.Examples.ArtinSchreier.hlocal_nodal`, in
  `StacksFrontier.Deformation.Examples.Linear.NodalCubicHlocal`: **`hlocal` itself**.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
-/

@[expose] public noncomputable section

open Polynomial
open Deformation.Examples.MaurerCartanWindow

universe u

namespace Deformation.Examples.ArtinSchreier

/-- The structure map `NC → A'` is `cst`. -/
theorem algebraMap_NC_ABase (a : NC) : algebraMap NC ABase a = cst NC a := rfl

/-- **The image of `Y` from the base in `P'` is `omegaP`.** The two ways of naming the
Artin–Schreier class in `P'` — through the base `NC` and through `A'` — agree. -/
theorem algebraMap_NC_PBase_ncY : algebraMap NC PBase ncY = omegaP := by
  rw [IsScalarTower.algebraMap_apply NC ABase PBase ncY, algebraMap_NC_ABase]
  rfl

/-- **`Y` is a unit in `(P')_g` for every `g` of `J' = Y·P'`.** This is exactly what taking `J'`
principal buys: `g = Y·c`, the image of `g` is a unit in `(P')_g` by construction, and a divisor
of a unit is a unit. It is why the local liftability hypothesis of Stacks 0DZ2 is one
verification for the counterexample rather than a family of them. -/
theorem isUnit_omegaP_away {g : PBase} (hg : g ∈ Ideal.span {omegaP}) :
    IsUnit (algebraMap PBase (Localization.Away g) omegaP) := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hg
  have hu : IsUnit (algebraMap PBase (Localization.Away (omegaP * c)) (omegaP * c)) :=
    IsLocalization.map_units _
      (⟨omegaP * c, Submonoid.mem_powers _⟩ : Submonoid.powers (omegaP * c))
  rw [map_mul] at hu
  exact isUnit_of_mul_isUnit_left hu

/-- **The local liftability input.** For every `g ∈ J' = Y·P'` the Artin–Schreier equation
`α·α + α = Y` has a solution over `(P')_g`, namely `α = Z/Y`, which exists there because `Y` is a
unit by `isUnit_omegaP_away` and `Z² + Y·Z = Y³` is the defining relation of the nodal cubic.

By `Deformation.Examples.ArtinSchreier.twisted_lift_iff` a solution of this equation over a base
is precisely an `A'`-flat lift of `M` over the twisted thickening of that base, so this is the
mathematical content of the local liftability hypothesis of Stacks 0DZ2 for the counterexample.
The remaining distance to `hlocal` as `Deformation.FlatModuleLiftBaseChangeStatement` states it
is packaging, itemised in this file's module documentation. -/
theorem exists_isASSol_away {g : PBase} (hg : g ∈ Ideal.span {omegaP}) :
    ∃ b : Localization.Away g,
      IsASSol (algebraMap NC (Localization.Away g) ncY) b := by
  refine exists_isASSol_of_isUnit_ncY (algebraMap NC (Localization.Away g)) ?_
  have h : algebraMap NC (Localization.Away g) ncY =
      algebraMap PBase (Localization.Away g) omegaP := by
    rw [← algebraMap_NC_PBase_ncY, ← IsScalarTower.algebraMap_apply NC PBase _]
  rw [h]
  exact isUnit_omegaP_away hg

end Deformation.Examples.ArtinSchreier

end
