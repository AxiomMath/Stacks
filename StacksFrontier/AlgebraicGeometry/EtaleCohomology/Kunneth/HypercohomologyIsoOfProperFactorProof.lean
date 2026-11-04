module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.OpenImmersionProductSquareInduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.ProperFactorKunnethStep
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.BaseChangeMapBoundedBelowFunctor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLerayGlobalSectionsAb
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.CanonicalMapOfASquare

/-!
# The Künneth input of [Stacks, Tag 0F1H]

This file proves
`Stacks.EtaleCohomology.OpenImmersionProductSquare.HypercohomologyIsoOfProperFactor`
(`hypercohomologyIsoOfProperFactor`): for `K` separably closed, `j : U ⟶ X` an open immersion of
schemes of finite type over `K`, `Y` proper over `K` and an abelian sheaf `𝓕` on `U_étale`
annihilated by an integer `n` invertible in `K`, the base change map `q⁻¹Rj_*𝓕 ⟶ Rh_*p⁻¹𝓕`
induces isomorphisms on all hypercohomology groups `H^i(Y ×_K X, -)`. This is the last paragraph
of the proof of [Stacks, Tag 0F1H]: by the Künneth formula [Stacks, Tag 0F14] both sides are
`RΓ(U, 𝓕) ⊗^L_{ℤ/n} RΓ(Y, ℤ/n)`.

## The proof

The Künneth computation is
`Stacks.EtaleCohomology.EtaleCoefficients.isIso_pushforward_map_baseChangeMap_of_isProper`, on the
derived categories `D(-_étale, ℤ/m)` of the Künneth section, `m = |n|`. It is read on abelian
sheaves as follows.

* `𝓕` is the underlying abelian sheaf of a sheaf of `ℤ/m`-modules `𝓕'`
  (`Stacks.EtaleCohomology.EtaleCoefficients.mem_essImage_etaleToSheaf_iff`).
* On `D(-_étale, ℤ/m)` the unbounded base change map and its descent to `D⁺` have invertible
  direct images to `Spec K` together
  (`EtaleCoefficients.isIso_map_baseChangeMap_app_iff_isIso_map_ι_map_derivedBaseChangePlus_app`).
* The underlying abelian sheaf carries the direct image of the descent to `R⁺c_*` of the abelian
  base change map (`pushforwardForgetPlusIso`,
  `Stacks.Cohomology.BaseChange.derived_exactTransport_app`).
* `RΓ(Y ×_K X, -) = RΓ(Spec K, -) ∘ Rc_*` and `Rc_*` restricts to `R⁺c_*` on `D⁺`
  (`Stacks.EtaleCohomology.smallEtaleDerivedGlobalSectionsPushforwardIsoAb`,
  `CategoryTheory.Functor.boundedDerivedIso`).

## Main results

* `Stacks.EtaleCohomology.OpenImmersionProductSquare.hypercohomologyIsoOfProperFactor`.

## References

* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
* [Stacks Project, Tag 0F14](https://stacks.math.columbia.edu/tag/0F14)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

-- `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb` and
-- `Stacks.EtaleCohomology.smallEtaleDerivedGlobalSections` are formed for the standard model of
-- the derived categories.
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **Hypercohomology from the bounded below direct image.** For a morphism `c : T ⟶ Z` and a
morphism `φ` of `D⁺(T_étale)`, if `R⁺c_*φ` is invertible then so is `RΓ(T, φ)`, hence every
`H^i(T, φ)`: `RΓ(T, -) = RΓ(Z, -) ∘ Rc_*` and `Rc_*` restricts to `R⁺c_*` on `D⁺`. -/
theorem isIso_homology_map_smallEtaleDerivedGlobalSections_map_of_isIso {T Z : Scheme.{u}}
    (c : T ⟶ Z) {A B : DerivedCategory.Plus (Sheaf (smallEtaleTopology T) Ab.{u + 1})}
    (φ : A ⟶ B) (hφ : IsIso ((smallEtalePushforwardAb c).rightDerivedFunctorPlus.map φ)) (i : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor Ab.{u + 1} i).map
      ((smallEtaleDerivedGlobalSections T).map (DerivedCategory.Plus.ι.map φ))) := by
  have e := Functor.boundedDerivedIso (smallEtalePushforwardAb c) (smallEtaleDerivedPushforwardAb c)
    (smallEtaleDerivedPushforwardAbUnit c)
    (Stacks.Cohomology.MayerVietoris.exists_quasiIso_isKInjective _)
  have h₁ : IsIso ((smallEtaleDerivedPushforwardAb c).map (DerivedCategory.Plus.ι.map φ)) :=
    (NatIso.isIso_map_iff e φ).1 (by
      show IsIso (DerivedCategory.Plus.ι.map
        ((smallEtalePushforwardAb c).rightDerivedFunctorPlus.map φ))
      infer_instance)
  have h₂ : IsIso ((smallEtaleDerivedGlobalSections T).map (DerivedCategory.Plus.ι.map φ)) :=
    (NatIso.isIso_map_iff (smallEtaleDerivedGlobalSectionsPushforwardIsoAb c) _).1
      (by
        show IsIso ((smallEtaleDerivedGlobalSections Z).map _)
        infer_instance)
  infer_instance

namespace EtaleCoefficients

/-- `isIso_pushforward_map_baseChangeMap_of_isProper` with the two projections and the
commutativity of the square as arguments, equal to the ones of the statement. -/
theorem isIso_pushforward_map_baseChangeMap_of_isProper_of_eq {K : Type u} [Field K]
    [IsSepClosed K] {X U Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
    (j : U ⟶ X) [IsOpenImmersion j] [LocallyOfFiniteType sX] [QuasiCompact sX]
    [QuasiCompact (j ≫ sX)] [IsProper sY] (m : ℕ) [NeZero m]
    (hh : Limits.pullback sY (j ≫ sX) ⟶ Limits.pullback sY sX)
    (hhr : hh ≫ pullback.fst sY sX = pullback.fst sY (j ≫ sX))
    (sq : IsPullback (pullback.snd sY (j ≫ sX)) hh j (pullback.snd sY sX))
    (q₀ : Limits.pullback sY sX ⟶ X) (hq : q₀ = pullback.snd sY sX)
    (p₀ : Limits.pullback sY (j ≫ sX) ⟶ U) (hp : p₀ = pullback.snd sY (j ≫ sX))
    (w : hh ≫ q₀ = p₀ ≫ j) (G : DerivedModules (ULift.{u + 1} (ZMod m)) U) :
    IsIso ((pushforward (ULift.{u + 1} (ZMod m)) (pullback.snd sY sX ≫ sX)).map
      ((baseChangeMap (ULift.{u + 1} (ZMod m)) q₀ j hh p₀ w).app G)) := by
  subst hq hp
  exact isIso_map_baseChangeMap_app_congr _ _ _ _ _ sq.w.symm _ _ _
    (isIso_pushforward_map_baseChangeMap_of_isProper sX sY j m hh hhr sq G)

end EtaleCoefficients

namespace OpenImmersionProductSquare

/-- **The Künneth input of [Stacks, Tag 0F1H] holds.** For `K` separably closed, `j : U ⟶ X` an
open immersion of schemes of finite type over `K`, `Y` proper over `K` and `𝓕` an abelian sheaf
on `U_étale` annihilated by an integer `n` invertible in `K`, the base change map
`q⁻¹Rj_*𝓕 ⟶ Rh_*p⁻¹𝓕` induces isomorphisms `H^i(Y ×_K X, q⁻¹Rj_*𝓕) ⟶ H^i(Y ×_K X, Rh_*p⁻¹𝓕)`
for all `i`. -/
theorem hypercohomologyIsoOfProperFactor : HypercohomologyIsoOfProperFactor.{u} := by
  intro K _ _ X U Y sX sU sY j _ hj _ _ _ _ _ n hn 𝓕 h𝓕 i
  subst hj
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  let m := n.natAbs
  have : NeZero m := ⟨Int.natAbs_ne_zero.2 hn0⟩
  -- `𝓕` is the underlying abelian sheaf of a sheaf of `ℤ/m`-modules
  have hm : m • 𝟙 𝓕 = 0 := by
    refine (EtaleCoefficients.nsmul_id_eq_zero_iff m 𝓕).2 fun V x => ?_
    have h₀ := h𝓕 V.unop x
    rcases Int.natAbs_eq n with hnm | hnm
    · rwa [hnm, natCast_zsmul] at h₀
    · rwa [hnm, neg_smul, neg_eq_zero, natCast_zsmul] at h₀
  obtain ⟨𝓕', ⟨e𝓕⟩⟩ := (EtaleCoefficients.mem_essImage_etaleToSheaf_iff m U 𝓕).2 hm
  have iK := EtaleCoefficients.forgetDerivedPlusSingleIso m U 𝓕' ≪≫
    (DerivedCategory.Plus.singleFunctor _ 0).mapIso e𝓕
  refine isIso_homology_map_smallEtaleDerivedGlobalSections_map_of_isIso
    (pullback.snd sY sX ≫ sX) _ ?_ i
  refine (NatTrans.isIso_app_iff_of_iso (Functor.whiskerRight
    (smallEtaleDerivedBaseChangeAb (q sX sY) j (h sX (j ≫ sX) sY j rfl) (p (j ≫ sX) sY)
      (h_comp_q sX (j ≫ sX) sY j rfl))
    (smallEtalePushforwardAb (pullback.snd sY sX ≫ sX)).rightDerivedFunctorPlus) iK).1 ?_
  show IsIso ((smallEtalePushforwardAb (pullback.snd sY sX ≫ sX)).rightDerivedFunctorPlus.map
    ((smallEtaleDerivedBaseChangeAb (q sX sY) j (h sX (j ≫ sX) sY j rfl) (p (j ≫ sX) sY)
      (h_comp_q sX (j ≫ sX) sY j rfl)).app _))
  rw [EtaleCoefficients.isIso_rightDerivedFunctorPlus_map_smallEtaleDerivedBaseChangeAb_app_iff]
  refine EtaleCoefficients.isIso_rightDerivedFunctorPlus_map_forgetDerivedPlus_map_of_isIso _ _ _ ?_
  rw [← EtaleCoefficients.isIso_map_baseChangeMap_app_iff_isIso_map_ι_map_derivedBaseChangePlus_app]
  exact EtaleCoefficients.isIso_pushforward_map_baseChangeMap_of_isProper_of_eq sX sY j m
    (h sX (j ≫ sX) sY j rfl) (h_comp_fst sX (j ≫ sX) sY j rfl)
    (isPullback sX (j ≫ sX) sY j rfl).flip (q sX sY) rfl (p (j ≫ sX) sY) rfl
    (h_comp_q sX (j ≫ sX) sY j rfl) _

end OpenImmersionProductSquare

end Stacks.EtaleCohomology

end
