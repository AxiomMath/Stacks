module

public import StacksFrontier.Deformation.Examples.Linear.NodalCubicQuotientHquot

/-!
# The Artin–Schreier root over `(A')_Y`, and the element that cuts out the local lift

Thirteenth layer of the instantiation of `Deformation.FlatModuleLiftBaseChangeStatement`, and the
**correction** of layer eight.

## The defect in layer eight, and why it is fatal there

`StacksFrontier.Deformation.Examples.Linear.NodalCubicLocalLift` proposes
`L_g = (N'₁)_ĝ` with `N'₁ = A'[α]/(α² + α − Y)` as the local lift of `M` over `(P')_g`. That
object is **not a lift of `M_g`**, and no amount of packaging makes it one. `N'₁` is free of rank
*two* over `A'`, so `L_g/t·L_g` is free of rank two over `(NC)_{…}`, whereas
`M_g = (NC)_{…}` is free of rank *one*. Concretely, for `g = Y` the polynomial `α² + α − Y`
already has the root `Z/Y` over `(NC)_Y` — that is exactly `exists_isASSol_of_isUnit_ncY` — so
`L_Y/t·L_Y ≅ (NC)_Y × (NC)_Y`, which is not isomorphic to `(NC)_Y`. The comparison equivalence
that `hlocal` demands of `L_g` is therefore **false**, not merely unproved.

The source of the slip is that adjoining the Artin–Schreier root is right on the `Q'` side, where
the root genuinely has to be adjoined, and wrong on the local side, where **the root is already
there**: `Y` is a unit in `(P')_g` for every `g ∈ J' = Y·P'`, and `α = Z/Y` solves `α² + α = Y`
inside `(P')_g` itself. Adjoining a second copy doubles the rank.

## What replaces it

The lift is the one layer seven named and layer eight talked itself out of: `(P')_g` modulo
`x − t·α`. Two changes make it painless.

* **Clear the denominator.** Rather than the element `x − t·(Z/Y)` of `(P')_g`, which needs a
  chosen inverse of `Y` and so varies with `g`, cut by the image of the single element

  `u = Y·x − t·Z ∈ P'`,

  which is `Y·(x − t·Z/Y)` and generates the same ideal because `Y` is a unit in `(P')_g`
  (`isUnit_omegaP_away`). `u` does not depend on `g` at all, and the ideal it generates in `(P')_g`
  is the image of a *fixed* ideal of `P'`. That is what makes the comparison of the next layers an
  ideal computation rather than a construction.
* **Get flatness from a localization of `A'`, not from a quotient of `(P')_g`.** Layer eight's
  worry — that `g` may involve `x`, so `(P')_g` is not `base-localize-then-adjoin-x` — is real, but
  it bites only if one tries to read flatness off a presentation of `(P')_g`. Instead this file
  builds the ring map

  `π : P' → (A')_Y`,  `x ↦ t·β`,  `β = Z/Y`,

  which exists for the same reason `pBaseToNOne` does: substituting `x = t·β` into
  `x² = t·x + t²·Y` leaves `t²·(β² − β − Y) = 0`. The next layer identifies `(P')_g/(u)` with
  `((A')_Y)_{π g}`, a localization of a localization of `A'`, and `Module.Flat A' −` follows by
  `Module.Flat.trans` twice. No basis of `(P')_g` is ever needed.

## Main definitions

* `Deformation.Examples.ArtinSchreier.AYBase`: `(A')_Y`.
* `Deformation.Examples.ArtinSchreier.betaAY`: the Artin–Schreier root `Z/Y` there, written out
  rather than chosen, so that its image in any `(P')_g/(u)` is pinned.
* `Deformation.Examples.ArtinSchreier.pBaseToAY`: the map `P' → (A')_Y` sending `x ↦ t·β`.
* `Deformation.Examples.ArtinSchreier.uElt`: the element `u = Y·x − t·Z` of `P'`.

## Main results

* `Deformation.Examples.ArtinSchreier.betaAY_isASSol`: `β² + β = Y` in `(A')_Y`.
* `Deformation.Examples.ArtinSchreier.pBaseToAY_uElt`: `π u = 0`, so `π` factors through `P'/(u)`
  — the compatibility the next layer's isomorphism runs on.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
-/

@[expose] public noncomputable section

open Polynomial
open Deformation.Examples.MaurerCartanWindow

universe u

namespace Deformation.Examples.ArtinSchreier

/-! ### `(A')_Y` and the Artin–Schreier root in it -/

/-- `Y` as an element of `A' = NC[t]/t³`. -/
def ayElt : ABase := cst NC ncY

/-- `Z` as an element of `A' = NC[t]/t³`. -/
def azElt : ABase := cst NC ncZ

/-- `(A')_Y`, the localization of `A'` in which the Artin–Schreier class of `Y` dies. -/
abbrev AYBase : Type := Localization.Away ayElt

/-- The inverse of `Y` in `(A')_Y`, written out. -/
def ayInv : AYBase :=
  IsLocalization.mk' AYBase 1 (⟨ayElt, Submonoid.mem_powers _⟩ : Submonoid.powers ayElt)

/-- `Y · Y⁻¹ = 1` in `(A')_Y`. -/
theorem ay_mul_ayInv : algebraMap ABase AYBase ayElt * ayInv = 1 := by
  have h := IsLocalization.mk'_spec AYBase (1 : ABase)
    (⟨ayElt, Submonoid.mem_powers _⟩ : Submonoid.powers ayElt)
  rw [map_one] at h
  rw [ayInv, mul_comm]
  exact h

/-- **The Artin–Schreier root `β = Z/Y` over `(A')_Y`**, the product of `Z` and `ayInv`. -/
def betaAY : AYBase := algebraMap ABase AYBase azElt * ayInv

/-- The defining relation of the nodal cubic, pushed into `(A')_Y`. -/
theorem ncRel_AY :
    algebraMap ABase AYBase azElt * algebraMap ABase AYBase azElt +
        algebraMap ABase AYBase ayElt * algebraMap ABase AYBase azElt =
      algebraMap ABase AYBase ayElt ^ 3 := by
  have h := congrArg ((algebraMap ABase AYBase).comp (cst NC)) ncRel'
  simpa [ayElt, azElt] using h

/-- **`β² + β = Y` in `(A')_Y`.** Multiplying through by `Y²` turns this into the defining
relation `Z² + Y·Z = Y³` of the nodal cubic. -/
theorem betaAY_isASSol :
    betaAY * betaAY + betaAY = algebraMap ABase AYBase ayElt := by
  have hrel := ncRel_AY
  have hv := ay_mul_ayInv
  rw [betaAY]
  linear_combination (ayInv * ayInv) * hrel +
    (algebraMap ABase AYBase ayElt * algebraMap ABase AYBase ayElt * ayInv +
      algebraMap ABase AYBase ayElt - algebraMap ABase AYBase azElt * ayInv) * hv

/-! ### The map `P' → (A')_Y` -/

/-- `2 = 0` in `(A')_Y`. -/
theorem two_eq_zero_AYBase : (2 : AYBase) = 0 := by
  rw [← map_ofNat (algebraMap ABase AYBase) 2, two_eq_zero_ABase, map_zero]

/-- **The map `π : P' → (A')_Y`**, `x ↦ t·β`. It is well defined for the same reason
`pBaseToNOne` is: substituting `x = t·β` into `x² = t·x + t²·Y` leaves `t²·(β² − β − Y)`, and
`β² + β = Y` with `2 = 0` makes that zero. -/
def pBaseToAY : PBase →+* AYBase :=
  AdjoinRoot.lift (algebraMap ABase AYBase)
    (algebraMap ABase AYBase (tau NC) * betaAY) (by
      have h2 : (2 : AYBase) = 0 := two_eq_zero_AYBase
      have hrel := betaAY_isASSol
      change Polynomial.eval₂ (algebraMap ABase AYBase)
        (algebraMap ABase AYBase (tau NC) * betaAY) pPoly = 0
      rw [show pPoly = X ^ 2 + -(C (tau NC) * X + C (tau NC * tau NC * cst NC ncY)) from rfl]
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_neg, Polynomial.eval₂_mul,
        Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, map_mul]
      have hY : algebraMap ABase AYBase (cst NC ncY) = algebraMap ABase AYBase ayElt := rfl
      rw [hY]
      linear_combination
        (algebraMap ABase AYBase (tau NC) * algebraMap ABase AYBase (tau NC)) * hrel
        - (algebraMap ABase AYBase (tau NC) * algebraMap ABase AYBase (tau NC) * betaAY) * h2)

/-- `π` restricts on `A'` to the localization map `A' → (A')_Y`. -/
theorem pBaseToAY_algebraMap (a : ABase) :
    pBaseToAY (algebraMap ABase PBase a) = algebraMap ABase AYBase a :=
  AdjoinRoot.lift_of _

/-- `π` sends the root `x` of `P'` to `t·β`. -/
theorem pBaseToAY_root :
    pBaseToAY (AdjoinRoot.root pPoly) = algebraMap ABase AYBase (tau NC) * betaAY :=
  AdjoinRoot.lift_root _

/-! ### The element that cuts out the lift -/

/-- **`u = Y·x − t·Z`**, the element of `P'` whose image generates the ideal cutting out the local
lift. Over `(P')_g` it is `Y·(x − t·Z/Y)`, and `Y` is a unit there, so it generates the ideal
`(x − t·β)` one actually wants — without a chosen inverse, and without depending on `g`. -/
def uElt : PBase :=
  omegaP * AdjoinRoot.root pPoly - tauP * algebraMap ABase PBase azElt

/-- **`π u = 0`.** This is the compatibility that lets `(A')_Y` receive a map from `(P')_g/(u)`:
`π u = Y·t·β − t·Z = t·(Y·β − Z) = t·Z·(Y·Y⁻¹ − 1) = 0`. -/
theorem pBaseToAY_uElt : pBaseToAY uElt = 0 := by
  have hv := ay_mul_ayInv
  rw [uElt, map_sub, map_mul, map_mul, pBaseToAY_root]
  have hom : pBaseToAY omegaP = algebraMap ABase AYBase ayElt := pBaseToAY_algebraMap _
  have hta : pBaseToAY tauP = algebraMap ABase AYBase (tau NC) := pBaseToAY_algebraMap _
  have haz : pBaseToAY (algebraMap ABase PBase azElt) = algebraMap ABase AYBase azElt :=
    pBaseToAY_algebraMap _
  rw [hom, hta, haz, betaAY]
  linear_combination
    (algebraMap ABase AYBase (tau NC) * algebraMap ABase AYBase azElt) * hv

/-- The ideal of `P'` generated by `u`, which is what the local lift is the quotient by. -/
abbrev uIdeal : Ideal PBase := Ideal.span {uElt}

end Deformation.Examples.ArtinSchreier

end
