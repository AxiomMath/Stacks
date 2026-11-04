module

public import Mathlib.RingTheory.Flat.Localization
public import StacksFrontier.Deformation.Examples.Linear.NodalCubicThickening

/-!
# An Artin–Schreier cover of `P'` and a flat module over it

Over the ring `P' = A'[x]/(x² − t·x − t²·Y)` (`PBase`), this file constructs

`Q₁ = P'[z]/(z² + z − Y)`,  `Q' = (Q₁)_{z+1}`,

together with the module `N' = (A'[z]/(z² + z − Y))_{α+1}` and a ring map `Q' → N'` sending
`x ↦ t·α` and `z ↦ α`. Substituting `x = t·z` into the relation `x² = t·x + t²·Y` of `P'` gives
`t²·(z² − z − Y)`, which vanishes because `z² + z = Y` and `2 = 0`; so `N'` is the quotient
`Q'/(x − t·z)` presented without `x`. As `A'[z]/(z² + z − Y)` is free of rank two over `A'`,
`N'` is flat over `A'`.

## Main definitions

* `Deformation.Examples.ArtinSchreier.QOne`, `QBase`: the rings `Q₁` and `Q'`.
* `Deformation.Examples.ArtinSchreier.NOne`, `NMod`: `A'[z]/(z² + z − Y)` and its localization at
  `α + 1`.
* `Deformation.Examples.ArtinSchreier.qBaseToNMod`: the ring map `Q' → N'`.

## Main results

* `Deformation.Examples.ArtinSchreier.flat_QOne`, `flat_QBase_PBase`: `Q₁` and `Q'` are flat over
  `P'`.
* `Deformation.Examples.ArtinSchreier.qRelation`, `qRelationMul`: `z² + z = Y` and
  `Y = z·(z + 1)` in `Q₁`.
* `Deformation.Examples.ArtinSchreier.flat_NMod`: `N'` is flat over `A'`.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
-/

@[expose] public noncomputable section

open Polynomial
open Deformation.Examples.MaurerCartanWindow

universe u

namespace Deformation.Examples.ArtinSchreier

/-! ### Nontriviality upstairs -/

/-- `A' = NC[t]/t³` is not the zero ring: it surjects onto `NC`. -/
instance : Nontrivial ABase :=
  ⟨⟨1, 0, fun h => by
    have hmap := congrArg redA h
    simp at hmap⟩⟩

/-- The ring map `P' → NC` sending `x ↦ 0` and `t ↦ 0`. -/
def pBaseToNC : PBase →+* NC :=
  AdjoinRoot.lift redA 0 (by
    change Polynomial.eval₂ redA 0 pPoly = 0
    rw [show pPoly = X ^ 2 + -(C (tau NC) * X + C (tau NC * tau NC * cst NC ncY)) from rfl]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_neg, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, map_mul, redA_tau]
    ring)

/-- `P'` is not the zero ring: it surjects onto `NC` via `pBaseToNC`. -/
instance : Nontrivial PBase :=
  ⟨⟨1, 0, fun h => by
    have hmap := congrArg pBaseToNC h
    simp at hmap⟩⟩

/-! ### Characteristic two upstairs -/

/-- `2 = 0` in `A' = NC[t]/t³`. -/
theorem two_eq_zero_ABase : (2 : ABase) = 0 := by
  rw [← map_ofNat (cst NC) 2, two_eq_zero_nc, map_zero]

/-! ### `N'` without the thickening coordinate -/

/-- The Artin–Schreier polynomial `z² + z − c` is monic. -/
private theorem monic_X_sq_add_X_sub_C {R : Type*} [CommRing R] [Nontrivial R] (c : R) :
    (X ^ 2 + (X - C c) : Polynomial R).Monic := by
  refine (Polynomial.monic_X_pow (R := R) 2).add_of_left ?_
  rw [Polynomial.degree_X_pow]
  have hle : (X - C c : Polynomial R).degree ≤ 1 := by
    refine le_trans (Polynomial.degree_sub_le _ _) (max_le Polynomial.degree_X_le ?_)
    exact le_trans Polynomial.degree_C_le (by norm_num)
  exact lt_of_le_of_lt hle (by norm_num)

/-- The root of `z² + z − c` in `R[z]/(z² + z − c)` satisfies `α² + α = c`. -/
private theorem root_mul_self_add_root {R : Type*} [CommRing R] (c : R) (p : Polynomial R)
    (hp : p = X ^ 2 + (X - C c)) :
    AdjoinRoot.root p * AdjoinRoot.root p + AdjoinRoot.root p = algebraMap R (AdjoinRoot p) c := by
  have h0 : AdjoinRoot.mk p (X ^ 2 + (X - C c)) = 0 := by
    rw [← hp]
    exact AdjoinRoot.mk_self
  rw [map_add, map_sub, map_pow] at h0
  have hX : AdjoinRoot.mk p (X : Polynomial R) = AdjoinRoot.root p := rfl
  have hC : AdjoinRoot.mk p (C c) = algebraMap R (AdjoinRoot p) c := rfl
  rw [hX, hC] at h0
  linear_combination h0

/-- The Artin–Schreier polynomial `z² + z − Y` over `A' = NC[t]/t³`. -/
def asPolyA : Polynomial ABase := X ^ 2 + (X - C (cst NC ncY))

/-- The polynomial `z² + z − Y` over `A'` is monic. -/
theorem asPolyA_monic : asPolyA.Monic :=
  monic_X_sq_add_X_sub_C _

/-- `N'₁ = A'[z]/(z² + z − Y)`, the quotient `Q₁/(x − t·z)` with `x` eliminated. -/
abbrev NOne : Type := AdjoinRoot asPolyA

/-- The Artin–Schreier root `α` over `A'`. -/
def alphaRoot : NOne := AdjoinRoot.root asPolyA

/-- `α² + α = Y` in `N'₁`. -/
theorem asRelation :
    alphaRoot * alphaRoot + alphaRoot = algebraMap ABase NOne (cst NC ncY) :=
  root_mul_self_add_root _ asPolyA rfl

/-- `N'₁` is free of rank two over `A'`. -/
theorem free_NOne : Module.Free ABase NOne :=
  Module.Free.of_basis (AdjoinRoot.powerBasis' asPolyA_monic).basis

/-- `N' = (N'₁)_{α+1}`, the localization of `N'₁` at `α + 1`. -/
abbrev NMod : Type := Localization.Away (alphaRoot + 1)

/-- `N'` is flat over `A'`. -/
theorem flat_NMod : Module.Flat ABase NMod := by
  have := free_NOne
  have : Module.Flat ABase NOne := Module.Flat.of_free
  have : Module.Flat NOne NMod :=
    IsLocalization.flat (Localization.Away (alphaRoot + 1)) (Submonoid.powers (alphaRoot + 1))
  exact Module.Flat.trans ABase NOne NMod

/-! ### The right column over `P'` -/

/-- The image of `Y` in `P'`. -/
def omegaP : PBase := algebraMap ABase PBase (cst NC ncY)

/-- The Artin–Schreier polynomial `z² + z − Y` over `P'`. -/
def qPoly : Polynomial PBase := X ^ 2 + (X - C omegaP)

/-- The polynomial `z² + z − Y` over `P'` is monic. -/
theorem qPoly_monic : qPoly.Monic :=
  monic_X_sq_add_X_sub_C _

/-- `Q₁ = P'[z]/(z² + z − Y)`, the étale `ℤ/2`-cover of `P'` on which the Artin–Schreier class of
`Y` becomes trivial. -/
abbrev QOne : Type := AdjoinRoot qPoly

/-- The Artin–Schreier root `z` over `P'`. -/
def zRoot : QOne := AdjoinRoot.root qPoly

/-- `z² + z = Y` in `Q₁`. -/
theorem qRelation : zRoot * zRoot + zRoot = algebraMap PBase QOne omegaP :=
  root_mul_self_add_root _ qPoly rfl

/-- `Y = z·(z + 1)` in `Q₁`. -/
theorem qRelationMul :
    algebraMap PBase QOne omegaP = zRoot * (zRoot + 1) := by
  have h := qRelation
  linear_combination -h

/-- `Q₁` is free of rank two over `P'`. -/
theorem free_QOne : Module.Free PBase QOne :=
  Module.Free.of_basis (AdjoinRoot.powerBasis' qPoly_monic).basis

/-- `Q₁` is flat over `P'`. -/
theorem flat_QOne : Module.Flat PBase QOne :=
  have := free_QOne
  Module.Flat.of_free

/-- `Q' = (Q₁)_{z+1}`, the localization of `Q₁` at `z + 1`. -/
abbrev QBase : Type := Localization.Away (zRoot + 1)

/-- `Q'` is flat over `P'`. -/
theorem flat_QBase_PBase : Module.Flat PBase QBase := by
  have := flat_QOne
  have : Module.Flat QOne QBase :=
    IsLocalization.flat (Localization.Away (zRoot + 1)) (Submonoid.powers (zRoot + 1))
  exact Module.Flat.trans PBase QOne QBase

/-! ### The surjection `Q' ↠ N'` -/

/-- The `A'`-algebra map `P' → N'₁` sending `x ↦ t·α`. -/
def pBaseToNOne : PBase →+* NOne :=
  AdjoinRoot.lift (algebraMap ABase NOne)
    (algebraMap ABase NOne (tau NC) * alphaRoot) (by
      have h2 : (2 : NOne) = 0 := by
        rw [← map_ofNat (algebraMap ABase NOne) 2, two_eq_zero_ABase, map_zero]
      have hrel := asRelation
      change Polynomial.eval₂ (algebraMap ABase NOne)
        (algebraMap ABase NOne (tau NC) * alphaRoot) pPoly = 0
      rw [show pPoly = X ^ 2 + -(C (tau NC) * X + C (tau NC * tau NC * cst NC ncY)) from rfl]
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_neg, Polynomial.eval₂_mul,
        Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, map_mul]
      linear_combination (algebraMap ABase NOne (tau NC) * algebraMap ABase NOne (tau NC)) * hrel
        - (algebraMap ABase NOne (tau NC) * algebraMap ABase NOne (tau NC) * alphaRoot) * h2)

/-- The ring map `Q₁ → N'₁` extending `pBaseToNOne` and sending `z ↦ α`. -/
def qOneToNOne : QOne →+* NOne :=
  AdjoinRoot.lift pBaseToNOne alphaRoot (by
    have hrel := asRelation
    have hP : pBaseToNOne omegaP = algebraMap ABase NOne (cst NC ncY) := by
      change AdjoinRoot.lift (algebraMap ABase NOne)
        (algebraMap ABase NOne (tau NC) * alphaRoot) _ (algebraMap ABase PBase (cst NC ncY)) = _
      exact AdjoinRoot.lift_of _
    change Polynomial.eval₂ pBaseToNOne alphaRoot qPoly = 0
    rw [show qPoly = X ^ 2 + (X - C omegaP) from rfl]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    rw [hP]
    linear_combination hrel)

/-- The ring map `Q' → N'` induced by `qOneToNOne` on localizations, using `z + 1 ↦ α + 1`. -/
def qBaseToNMod : QBase →+* NMod :=
  IsLocalization.lift (M := Submonoid.powers (zRoot + 1))
    (g := (algebraMap NOne NMod).comp qOneToNOne) (by
      intro y
      obtain ⟨k, hk⟩ := y.2
      have hz : qOneToNOne (zRoot + 1) = alphaRoot + 1 := by
        rw [map_add, map_one]
        change AdjoinRoot.lift pBaseToNOne alphaRoot _ (AdjoinRoot.root qPoly) + 1 = _
        rw [AdjoinRoot.lift_root]
      have hval : ((algebraMap NOne NMod).comp qOneToNOne) (y : QOne) =
          (algebraMap NOne NMod (alphaRoot + 1)) ^ k := by
        rw [← hk, RingHom.comp_apply, map_pow, map_pow, hz]
      rw [hval]
      refine IsUnit.pow _ ?_
      exact IsLocalization.map_units (Localization.Away (alphaRoot + 1))
        (⟨alphaRoot + 1, Submonoid.mem_powers _⟩ : Submonoid.powers (alphaRoot + 1)))

/-! ### The structural map `A' → Q'` -/

/-- The composite ring map `A' → P' → Q₁ → Q'`. -/
def aBaseToQBase : ABase →+* QBase :=
  (algebraMap QOne QBase).comp ((algebraMap PBase QOne).comp (algebraMap ABase PBase))

/-- The image of `t` in `Q'`. -/
def tauQ : QBase := aBaseToQBase (tau NC)

end Deformation.Examples.ArtinSchreier

end
