module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Discriminant.BaseLocalization
public import StacksFrontier.AlgebraicGeometry.Discriminant.TargetLocalization

/-!
# Localizing base and target of a relative dualizing module at once

Let `A → B` be a quasi-finite map of Noetherian rings and `f` an element of `A`. Localizing `A`
away from `f` and `B` away from the image of `f` turns the relative dualizing module into its
own localization away from that image. This file constructs that identification and shows it is
the composite of the two one-sided identifications.

## Main definitions

* `Stacks.Discriminant.localizedModule_dualizingModule_equiv_of_baseLocalization` identifies a
  localization of the relative dualizing module away from the image of `f` with the relative
  dualizing module of `B_f` over `A_f`.

## Main results

* `Stacks.Discriminant.localizedModule_dualizingModule_equiv_of_baseLocalization_eq_comp`
  exhibits it as localizing in the target and then replacing the base by its localization.

## Implementation notes

The composite is formed through the finite-open factorization of `B_f` over `A` obtained from
the chosen one of `B` by `Stacks.Discriminant.locFact`; the naturality of each of the two
one-sided identifications is what lets that intermediate choice be exchanged for an arbitrary
one.

## References

* [Stacks Project, Tag 0BT2](https://stacks.math.columbia.edu/tag/0BT2)
-/

@[expose] public section

namespace Stacks.Discriminant

universe u v w x y z t q

open Topology
open scoped TensorProduct

attribute [local instance] algebraDualModule

/-- **Stacks Project, Tag 0BT2, part (3).** After localizing the base away from `f` and the
target away from its image, the relative dualizing module is the corresponding localization of
the original relative dualizing module. -/
@[stacks 0BT2 "part (3)"]
public noncomputable def localizedModule_dualizingModule_equiv_of_baseLocalization
    {A : Type u} {B : Type v} {Af : Type w} {Bf : Type x} {M : Type y}
    [CommRing A] [CommRing B] [CommRing Af] [CommRing Bf]
    [Algebra A B] [Algebra A Af] [Algebra B Bf] [Algebra A Bf] [Algebra Af Bf]
    [IsScalarTower A B Bf] [IsScalarTower A Af Bf]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B]
    (f : A) [IsLocalization.Away f Af]
    [IsLocalization.Away (algebraMap A B f) Bf]
    (F : FiniteOpenFactorization.{u, v, z} A B)
    (G : FiniteOpenFactorization.{w, x, q} Af Bf)
    [AddCommGroup M] [Module B M] [Module Bf M] [IsScalarTower B Bf M]
    (localizationMap : dualizingModule F →ₗ[B] M)
    (hM : IsLocalizedModule (Submonoid.powers (algebraMap A B f)) localizationMap) :
    M ≃ₗ[Bf] dualizingModule G := by
  let g := algebraMap A B f
  let H : FiniteOpenFactorization A Bf := locFact (Bg := Bf) g F
  letI : Algebra.QuasiFinite A Bf :=
    Algebra.QuasiFinite.of_isLocalization (Submonoid.powers (algebraMap A B f))
  letI : IsNoetherianRing Bf :=
    IsLocalization.isNoetherianRing (Submonoid.powers (algebraMap A B f)) Bf inferInstance
  exact (localizedModule_dualizingModule_equiv (algebraMap A B f) F H
    localizationMap hM).trans (dualizingModule_equiv_of_isLocalization_away f H G)

/-- Simultaneous localization is the composite of localization in the target and replacement
of the base by its localization.  This fixes the canonical identification, rather than merely
asserting the existence of a linear equivalence. -/
@[stacks 0BT2 "part (3), compatibility with parts (1) and (2)"]
public theorem localizedModule_dualizingModule_equiv_of_baseLocalization_eq_comp
    {A : Type u} {B : Type v} {Af : Type w} {Bf : Type x} {M : Type y}
    [CommRing A] [CommRing B] [CommRing Af] [CommRing Bf]
    [Algebra A B] [Algebra A Af] [Algebra B Bf] [Algebra A Bf] [Algebra Af Bf]
    [IsScalarTower A B Bf] [IsScalarTower A Af Bf]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing Bf]
    [Algebra.QuasiFinite A B] [Algebra.QuasiFinite A Bf]
    (f : A) [IsLocalization.Away f Af]
    [IsLocalization.Away (algebraMap A B f) Bf]
    (F : FiniteOpenFactorization.{u, v, z} A B)
    (H : FiniteOpenFactorization.{u, x, t} A Bf)
    (G : FiniteOpenFactorization.{w, x, q} Af Bf)
    [AddCommGroup M] [Module B M] [Module Bf M] [IsScalarTower B Bf M]
    (localizationMap : dualizingModule F →ₗ[B] M)
    (hM : IsLocalizedModule (Submonoid.powers (algebraMap A B f)) localizationMap) :
    localizedModule_dualizingModule_equiv_of_baseLocalization
        f F G localizationMap hM =
      (localizedModule_dualizingModule_equiv
        (algebraMap A B f) F H localizationMap hM).trans
        (dualizingModule_equiv_of_isLocalization_away f H G) :=
  by
    let H₀ := locFact (A := A) (B := B) (Bg := Bf) (algebraMap A B f) F
    let : IsNoetherianRing Af :=
      IsLocalization.isNoetherianRing (Submonoid.powers f) Af inferInstance
    apply LinearEquiv.ext
    intro m
    have hTarget := localizedModule_dualizingModule_equiv_natural_in_source
      (g := algebraMap A B f) (F := F) (F' := F) (G := H₀) (G' := H)
      (localizationMap := localizationMap) (hM := hM)
      (localizationMap' := localizationMap) (hM' := hM)
      (comparison := LinearMap.id)
      (hcomparison := by
        intro x
        simp [dualizingModuleEquiv_refl]) m
    have hTarget' :
        dualizingModuleEquiv H₀ H
            (localizedModule_dualizingModule_equiv (algebraMap A B f)
              F H₀ localizationMap hM m) =
          localizedModule_dualizingModule_equiv (algebraMap A B f)
            F H localizationMap hM m := by
      simpa using hTarget
    have hBase := dualizingModule_equiv_of_isLocalization_away_natural
      f H₀ H G G
      (localizedModule_dualizingModule_equiv (algebraMap A B f)
        F H₀ localizationMap hM m)
    have hBase' :
        dualizingModule_equiv_of_isLocalization_away f H₀ G
            (localizedModule_dualizingModule_equiv (algebraMap A B f)
              F H₀ localizationMap hM m) =
          dualizingModule_equiv_of_isLocalization_away f H G
            (dualizingModuleEquiv H₀ H
              (localizedModule_dualizingModule_equiv (algebraMap A B f)
                F H₀ localizationMap hM m)) := by
      simpa [dualizingModuleEquiv_refl] using hBase
    show dualizingModule_equiv_of_isLocalization_away f H₀ G
          (localizedModule_dualizingModule_equiv (algebraMap A B f)
            F H₀ localizationMap hM m) =
        dualizingModule_equiv_of_isLocalization_away f H G
          (localizedModule_dualizingModule_equiv (algebraMap A B f)
            F H localizationMap hM m)
    rw [hBase', hTarget']

end Stacks.Discriminant
