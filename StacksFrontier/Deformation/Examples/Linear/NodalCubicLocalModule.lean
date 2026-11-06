module

public import StacksFrontier.Deformation.Examples.Linear.NodalCubicLocalAway

/-!
# The local lift of the Stacks 0DZ2 counterexample, with the right rank

The local lift in the instantiation of `Deformation.FlatModuleLiftBaseChangeStatement`:

`L_g = (P')_g ⧸ u·(P')_g`,  `u = Y·x − t·Z`,

together with `Module.Flat A' L_g`.

## Flatness of the quotient

`L_g` is a **quotient** of `(P')_g`, so `(P)_ḡ ⊗_{(P')_g} L_g` is a quotient of `(P)_ḡ` by a
mapped ideal (`Algebra.TensorProduct.quotIdealMapEquivTensorQuot`, which is linear over `(P)_ḡ`).
A quotient is not flat in general, and `P'/(u)` is *not* `A'`-flat before `Y` is inverted, since
it degenerates at the node. Flatness follows from an identification with a localization:

`(P')_g ⧸ (u) ≅ ((A')_Y)_{π g}`,  `π : P' → (A')_Y`, `x ↦ t·β`.

The right side is a localization of a localization of `A'`, so `Module.Flat A' −` is
`Module.Flat.trans` twice. The isomorphism is built from universal properties in both directions
and checked on generators: out of the quotient by `Ideal.Quotient.mk_surjective`, out of each
localization by `IsLocalization.ringHom_ext`, and out of `P'` by `AdjoinRoot.ringHom_ext`, which
leaves exactly two cases — the base `A'` and the root `x`. In the root case, `u = 0` says
`Y·x = t·Z` in the quotient, so `x = t·Z·Y⁻¹ = t·β`, which is the value `π` assigns to `x`.

`Y` is a unit in `(P')_g` for every `g ∈ J' = Y·P'` (`isUnit_omegaP_away`), which is what makes
`Y⁻¹` available and is the only place the hypothesis `g ∈ J'` is used.

## Main definitions

* `Deformation.Examples.ArtinSchreier.LocalModule`: `L_g = (P')_g ⧸ u·(P')_g`.
* `Deformation.Examples.ArtinSchreier.localModuleAlgEquivAYAway`: the identification with
  `((A')_Y)_{π g}`, as `A'`-algebras.

## Main results

* `Deformation.Examples.ArtinSchreier.algebraMap_uElt_eq_zero`: `u = 0` in `L_g`, i.e.
  `Y·x = t·Z`.
* `Deformation.Examples.ArtinSchreier.flat_LocalModule`: **`Module.Flat A' L_g`**.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
-/

@[expose] public noncomputable section

open Polynomial
open Deformation.Examples.MaurerCartanWindow

universe u

namespace Deformation.Examples.ArtinSchreier

/-! ### The quotient `(P')_g ⧸ (u)` -/

/-- `(P')_g`, the localization of `P'` at `g`. -/
abbrev PAway (g : PBase) : Type := Localization.Away g

/-- The ideal `u·(P')_g`, the image of the fixed ideal `(u)` of `P'`. -/
abbrev localIdeal (g : PBase) : Ideal (PAway g) :=
  uIdeal.map (algebraMap PBase (PAway g))

/-- **The local lift** `L_g = (P')_g ⧸ u·(P')_g`, i.e. `(P')_g` modulo `x − t·β` with the
denominator cleared. -/
abbrev LocalModule (g : PBase) : Type := PAway g ⧸ localIdeal g

/-- The quotient map `(P')_g → L_g` after `P' → (P')_g` is the structure map `P' → L_g`. -/
theorem algebraMap_PAway_LocalModule (g : PBase) (p : PBase) :
    Ideal.Quotient.mk (localIdeal g) (algebraMap PBase (PAway g) p) =
      algebraMap PBase (LocalModule g) p := by
  rw [IsScalarTower.algebraMap_apply PBase (PAway g) (LocalModule g),
    Ideal.Quotient.algebraMap_eq]

/-- **`u = 0` in `L_g`**, i.e. `Y·x = t·Z`. -/
theorem algebraMap_uElt_eq_zero (g : PBase) :
    algebraMap PBase (LocalModule g) uElt = 0 := by
  rw [← algebraMap_PAway_LocalModule, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)

/-- The structure map `A' → L_g` factors through `P'`. -/
private theorem algebraMap_ABase_LocalModule (g : PBase) (a : ABase) :
    algebraMap ABase (LocalModule g) a =
      algebraMap PBase (LocalModule g) (algebraMap ABase PBase a) :=
  IsScalarTower.algebraMap_apply ABase PBase (LocalModule g) a

/-- `Y·x = t·Z` in `L_g`, which is `algebraMap_uElt_eq_zero` read as a relation, with both scalars
named through `A'`. -/
theorem omegaP_mul_root_eq (g : PBase) :
    algebraMap ABase (LocalModule g) ayElt *
        algebraMap PBase (LocalModule g) (AdjoinRoot.root pPoly) =
      algebraMap ABase (LocalModule g) (tau NC) *
        algebraMap ABase (LocalModule g) azElt := by
  have h := algebraMap_uElt_eq_zero g
  rw [uElt, map_sub, map_mul, map_mul, sub_eq_zero] at h
  rw [algebraMap_ABase_LocalModule g ayElt, algebraMap_ABase_LocalModule g (tau NC),
    algebraMap_ABase_LocalModule g azElt]
  exact h

/-- `Y` is a unit in `L_g` for `g ∈ J'`, inherited from `(P')_g`. -/
theorem isUnit_ayElt_localModule {g : PBase} (hg : g ∈ Ideal.span {omegaP}) :
    IsUnit (algebraMap ABase (LocalModule g) ayElt) := by
  have h := (isUnit_omegaP_away hg).map (Ideal.Quotient.mk (localIdeal g))
  rw [show (Ideal.Quotient.mk (localIdeal g)) (algebraMap PBase (PAway g) omegaP) =
      algebraMap ABase (LocalModule g) ayElt from by
    rw [algebraMap_PAway_LocalModule, omegaP,
      ← IsScalarTower.algebraMap_apply ABase PBase (LocalModule g)]
    rfl] at h
  exact h

/-- `g` is a unit in `L_g`, inherited from `(P')_g`. -/
theorem isUnit_g_localModule (g : PBase) :
    IsUnit (algebraMap PBase (LocalModule g) g) := by
  have h : IsUnit (algebraMap PBase (PAway g) g) :=
    IsLocalization.map_units _ (⟨g, Submonoid.mem_powers _⟩ : Submonoid.powers g)
  have h2 := h.map (Ideal.Quotient.mk (localIdeal g))
  rwa [algebraMap_PAway_LocalModule] at h2

/-! ### The localization `((A')_Y)_{π g}` -/

/-- `((A')_Y)_{π g}`, a localization of a localization of `A'`. -/
abbrev AYAway (g : PBase) : Type := Localization.Away (pBaseToAY g)

/-- **`((A')_Y)_{π g}` is flat over `A'`**: two localizations composed. -/
theorem flat_AYAway (g : PBase) : Module.Flat ABase (AYAway g) := by
  have : Module.Flat ABase AYBase :=
    IsLocalization.flat (Localization.Away ayElt) (Submonoid.powers ayElt)
  have : Module.Flat AYBase (AYAway g) :=
    IsLocalization.flat (Localization.Away (pBaseToAY g)) (Submonoid.powers (pBaseToAY g))
  exact Module.Flat.trans ABase AYBase (AYAway g)

/-- `π g` becomes a unit in `((A')_Y)_{π g}`, by construction. -/
theorem isUnit_pBaseToAY_g (g : PBase) :
    IsUnit (algebraMap AYBase (AYAway g) (pBaseToAY g)) :=
  IsLocalization.map_units _
    (⟨pBaseToAY g, Submonoid.mem_powers _⟩ : Submonoid.powers (pBaseToAY g))

/-! ### The map out of the quotient -/

/-- `π` extended across the localization at `g`: `(P')_g → ((A')_Y)_{π g}`. -/
def pAwayToAYAway (g : PBase) : PAway g →+* AYAway g :=
  IsLocalization.lift (M := Submonoid.powers g)
    (g := (algebraMap AYBase (AYAway g)).comp pBaseToAY) (by
      intro y
      obtain ⟨k, hk⟩ := y.2
      have hval : ((algebraMap AYBase (AYAway g)).comp pBaseToAY) (y : PBase) =
          (algebraMap AYBase (AYAway g) (pBaseToAY g)) ^ k := by
        rw [← hk, RingHom.comp_apply, map_pow, map_pow]
      rw [hval]
      exact IsUnit.pow _ (isUnit_pBaseToAY_g g))

/-- `pAwayToAYAway g` sends the image of `p ∈ P'` to the image of `π p`. -/
theorem pAwayToAYAway_algebraMap (g : PBase) (p : PBase) :
    pAwayToAYAway g (algebraMap PBase (PAway g) p) =
      algebraMap AYBase (AYAway g) (pBaseToAY p) :=
  IsLocalization.lift_eq _ p

/-- **The map `L_g → ((A')_Y)_{π g}`.** It exists because `π u = 0` (`pBaseToAY_uElt`), so the
ideal `u·(P')_g` is killed. -/
def localModuleToAYAway (g : PBase) : LocalModule g →+* AYAway g :=
  Ideal.Quotient.lift _ (pAwayToAYAway g) (by
    have hle : localIdeal g ≤ RingHom.ker (pAwayToAYAway g) := by
      rw [Ideal.map_le_iff_le_comap, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
        Ideal.mem_comap, RingHom.mem_ker, pAwayToAYAway_algebraMap, pBaseToAY_uElt, map_zero]
    exact fun y hy => hle hy)

/-- `localModuleToAYAway g` sends the image of `p ∈ P'` to the image of `π p`. -/
theorem localModuleToAYAway_mk (g : PBase) (p : PBase) :
    localModuleToAYAway g (algebraMap PBase (LocalModule g) p) =
      algebraMap AYBase (AYAway g) (pBaseToAY p) := by
  rw [← algebraMap_PAway_LocalModule]
  exact (Ideal.Quotient.lift_mk _ _ _).trans (pAwayToAYAway_algebraMap g p)

/-! ### The map into the quotient -/

/-- `(A')_Y → L_g`, which exists because `Y` is a unit in `L_g` for `g ∈ J'`. -/
def ayToLocalModule {g : PBase} (hg : g ∈ Ideal.span {omegaP}) : AYBase →+* LocalModule g :=
  IsLocalization.lift (M := Submonoid.powers ayElt)
    (g := (algebraMap ABase (LocalModule g) : ABase →+* LocalModule g)) (by
      intro y
      obtain ⟨k, hk⟩ := y.2
      rw [← hk, map_pow]
      exact IsUnit.pow _ (isUnit_ayElt_localModule hg))

/-- `ayToLocalModule` sends the image of `a ∈ A'` to the image of `a` in `L_g`. -/
theorem ayToLocalModule_algebraMap {g : PBase} (hg : g ∈ Ideal.span {omegaP}) (a : ABase) :
    ayToLocalModule hg (algebraMap ABase AYBase a) = algebraMap ABase (LocalModule g) a :=
  IsLocalization.lift_eq _ a

/-- The image of `Y⁻¹` inverts `Y`. -/
theorem ayToLocalModule_ayInv {g : PBase} (hg : g ∈ Ideal.span {omegaP}) :
    algebraMap ABase (LocalModule g) ayElt * ayToLocalModule hg ayInv = 1 := by
  have h := congrArg (ayToLocalModule hg) ay_mul_ayInv
  rw [map_mul, map_one, ayToLocalModule_algebraMap] at h
  exact h

/-- **The square commutes**: `P' → (A')_Y → L_g` is `P' → (P')_g → L_g`. Checked on the two
generators of `P' = A'[x]/(x² − t·x − t²·Y)`: on `A'` both sides are the structure map, and on `x`
the left side is `t·β = t·Z·Y⁻¹` while the right side is `x`, which `u = 0` identifies. -/
theorem ayToLocalModule_pBaseToAY {g : PBase} (hg : g ∈ Ideal.span {omegaP}) (p : PBase) :
    ayToLocalModule hg (pBaseToAY p) = algebraMap PBase (LocalModule g) p := by
  have hring : (ayToLocalModule hg).comp pBaseToAY =
      (algebraMap PBase (LocalModule g) : PBase →+* LocalModule g) := by
    refine AdjoinRoot.ringHom_ext ?_ ?_
    · refine RingHom.ext fun a => ?_
      show ayToLocalModule hg (pBaseToAY (AdjoinRoot.of pPoly a)) = _
      rw [show AdjoinRoot.of pPoly a = algebraMap ABase PBase a from rfl,
        pBaseToAY_algebraMap, ayToLocalModule_algebraMap]
      exact algebraMap_ABase_LocalModule g a
    · show ayToLocalModule hg (pBaseToAY (AdjoinRoot.root pPoly)) = _
      rw [pBaseToAY_root, map_mul, ayToLocalModule_algebraMap, betaAY, map_mul,
        ayToLocalModule_algebraMap]
      have hrel := omegaP_mul_root_eq g
      have hinv := ayToLocalModule_ayInv hg
      linear_combination (-(ayToLocalModule hg ayInv)) * hrel +
        (algebraMap PBase (LocalModule g) (AdjoinRoot.root pPoly)) * hinv
  exact RingHom.congr_fun hring p

/-- `((A')_Y)_{π g} → L_g`, the extension of `ayToLocalModule` across the second localization:
`π g` goes to the image of `g`, which is a unit. -/
def ayAwayToLocalModule {g : PBase} (hg : g ∈ Ideal.span {omegaP}) :
    AYAway g →+* LocalModule g :=
  IsLocalization.lift (M := Submonoid.powers (pBaseToAY g)) (g := ayToLocalModule hg) (by
    intro y
    obtain ⟨k, hk⟩ := y.2
    rw [← hk, map_pow]
    refine IsUnit.pow _ ?_
    rw [ayToLocalModule_pBaseToAY hg g]
    exact isUnit_g_localModule g)

/-- `ayAwayToLocalModule` restricted to `(A')_Y` is `ayToLocalModule`. -/
theorem ayAwayToLocalModule_algebraMap {g : PBase} (hg : g ∈ Ideal.span {omegaP}) (b : AYBase) :
    ayAwayToLocalModule hg (algebraMap AYBase (AYAway g) b) = ayToLocalModule hg b :=
  IsLocalization.lift_eq _ b

/-! ### The identification -/

/-- `ayAwayToLocalModule` is a left inverse of `localModuleToAYAway`, checked on the images of
`P'` in `L_g`. -/
theorem ayAwayToLocalModule_localModuleToAYAway {g : PBase} (hg : g ∈ Ideal.span {omegaP})
    (y : LocalModule g) :
    ayAwayToLocalModule hg (localModuleToAYAway g y) = y := by
  have hring : ((ayAwayToLocalModule hg).comp (localModuleToAYAway g)).comp
        (Ideal.Quotient.mk (localIdeal g)) =
      (Ideal.Quotient.mk (localIdeal g) : PAway g →+* LocalModule g) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers g) (RingHom.ext fun p => ?_)
    show ayAwayToLocalModule hg (localModuleToAYAway g
      (Ideal.Quotient.mk (localIdeal g) (algebraMap PBase (PAway g) p))) = _
    rw [algebraMap_PAway_LocalModule, localModuleToAYAway_mk,
      ayAwayToLocalModule_algebraMap, ayToLocalModule_pBaseToAY hg p]
    exact (algebraMap_PAway_LocalModule g p).symm
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact RingHom.congr_fun hring z

/-- `ayAwayToLocalModule` is a right inverse of `localModuleToAYAway`, checked on the image of
`A'` in `((A')_Y)_{π g}`. -/
theorem localModuleToAYAway_ayAwayToLocalModule {g : PBase} (hg : g ∈ Ideal.span {omegaP})
    (b : AYAway g) :
    localModuleToAYAway g (ayAwayToLocalModule hg b) = b := by
  have hring : (localModuleToAYAway g).comp (ayAwayToLocalModule hg) =
      RingHom.id (AYAway g) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (pBaseToAY g)) ?_
    refine IsLocalization.ringHom_ext (Submonoid.powers ayElt) (RingHom.ext fun a => ?_)
    show localModuleToAYAway g (ayAwayToLocalModule hg
      (algebraMap AYBase (AYAway g) (algebraMap ABase AYBase a))) = _
    rw [ayAwayToLocalModule_algebraMap, ayToLocalModule_algebraMap,
      algebraMap_ABase_LocalModule, localModuleToAYAway_mk, pBaseToAY_algebraMap]
    rfl
  exact RingHom.congr_fun hring b

/-- **`L_g ≅ ((A')_Y)_{π g}` as `A'`-algebras.** -/
def localModuleAlgEquivAYAway {g : PBase} (hg : g ∈ Ideal.span {omegaP}) :
    LocalModule g ≃ₐ[ABase] AYAway g :=
  AlgEquiv.ofRingEquiv
    (f := { toFun := localModuleToAYAway g
            invFun := ayAwayToLocalModule hg
            left_inv := ayAwayToLocalModule_localModuleToAYAway hg
            right_inv := localModuleToAYAway_ayAwayToLocalModule hg
            map_mul' := (localModuleToAYAway g).map_mul
            map_add' := (localModuleToAYAway g).map_add })
    (fun a => by
      change localModuleToAYAway g (algebraMap ABase (LocalModule g) a) = _
      rw [show algebraMap ABase (LocalModule g) a =
          algebraMap PBase (LocalModule g) (algebraMap ABase PBase a) from
        IsScalarTower.algebraMap_apply ABase PBase (LocalModule g) a,
        localModuleToAYAway_mk, pBaseToAY_algebraMap]
      rw [IsScalarTower.algebraMap_apply ABase AYBase (AYAway g) a])

/-- **`Module.Flat A' L_g`**: `L_g` is `((A')_Y)_{π g}`, a localization of a localization of
`A'`. -/
theorem flat_LocalModule {g : PBase} (hg : g ∈ Ideal.span {omegaP}) :
    Module.Flat ABase (LocalModule g) := by
  have := flat_AYAway g
  exact Module.Flat.of_linearEquiv (localModuleAlgEquivAYAway hg).toLinearEquiv

end Deformation.Examples.ArtinSchreier

end
