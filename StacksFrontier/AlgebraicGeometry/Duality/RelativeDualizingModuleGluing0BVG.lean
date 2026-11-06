module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ChartComparison
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModuleData0BVG
public import StacksFrontier.AlgebraicGeometry.Modules.ChartSheafFiniteType
public import StacksFrontier.AlgebraicGeometry.Modules.GluedCoherentOfBasis
public import StacksFrontier.RingTheory.Dualizing.NoetherianPairings.Ports.DualizingModuleLocalization
public import Mathlib.Algebra.Module.LocalizedModule.Away
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Glueing the relative dualizing module of a locally quasi-finite morphism

Let `f : Y ⟶ X` be locally of finite type and locally quasi-finite between locally Noetherian
schemes.  Each *adapted open* of `f` — an affine open of the source over an affine open of the
base (`Stacks.Discriminant.AdaptedOpen`) — carries the algebraic relative dualizing module
`ω_{Γ(Y,V)/Γ(X,U)}` of Tag 0BSZ, hence a sheaf of `𝒪_Y`-modules whose sections over a principal
open of its source open are the corresponding localization.  This file assembles the glueing
datum of those sheaves: the cover, the local quasi-coherence and finite type of each member, the
comparison of two members over an adapted open good for both, and the cocycle identity.

The comparison is built from Tag 0BT2: part (2) localizes the target from the chart's source
open to the adapted open's source open, and part (1) then replaces the chart's base ring by the
adapted open's.  Its target, the dualizing module of `Stacks.Discriminant.adaptedFactorization`,
depends on the adapted open alone, which is what makes the cocycle identity free.

## Main definitions

* `Stacks.Modules.chartSectionOfLE`: the canonical map from a module over an affine chart to the
  sections of its chart sheaf over an open inside the chart, as a linear map.
* `Stacks.Discriminant.adaptedChartSheaf`: the sheaf of `𝒪_Y`-modules of an adapted open.
* `Stacks.Discriminant.chartHub` and `Stacks.Discriminant.adaptedHub`: the two-step comparison of
  Tag 0BT2 identifying the sections of a chart sheaf over an adapted open with the algebraic
  relative dualizing module of that adapted open.
* `Stacks.Discriminant.adaptedSheafComparison`: the comparison of two chart sheaves over an
  adapted open good for both.
* `Stacks.Discriminant.HubRestrict`: the statement that the hub comparisons of two nested adapted
  opens are intertwined by restriction of sections, through a map of the two algebraic relative
  dualizing modules that does not depend on the chart.

## Main results

* `Stacks.Modules.isLocalizedModule_chartSectionOfLE`: the sections of a chart sheaf over a
  principal open are a localization of the module.
* `Stacks.Discriminant.isLocalizedModule_away_of_comp`: a map between two localizations of one
  module, at two elements of the base ring, is itself a localization map.
* `Stacks.Discriminant.iSup_adaptedOpen_source_eq_top`,
  `Stacks.Discriminant.isQuasicoherent_restrict_adaptedChartSheaf` and
  `Stacks.Discriminant.isFiniteType_restrict_adaptedChartSheaf`: the three local inputs of the
  glueing.
* `Stacks.Discriminant.adaptedSheafComparison_trans`: the cocycle identity.
* `Stacks.Discriminant.adaptedSheafComparison_restrict`: the restriction compatibility a glueing
  datum demands, reduced to `HubRestrict`.  The reduction uses
  `Stacks.Discriminant.AdaptedOpen.restrict_comparison_of_source_le` to shrink the base opens as
  well, and then only the algebra of composing an isomorphism with its inverse.
* `Stacks.Discriminant.exists_relativeDualizingModule_of_hubRestrict`: **assuming
  `HubRestrict f`**, there is a coherent quasi-coherent `𝒪_Y`-module whose sections over every
  affine chart are the algebraic relative dualizing module of that chart, compatibly with
  restriction inside a chart and with the chart comparison over the adapted opens.

## Implementation notes

`Stacks.Discriminant.chartHub` repeats `Stacks.Discriminant.chartDualizingEquivBasicOpen` with
the two opens of the adapted open left as variables rather than presented as `Y.basicOpen g` and
`X.basicOpen a`.  The reason is that the presented form can only be read at an adapted open by
destructuring it and substituting the presentations, as
`Stacks.Discriminant.chartDualizingEquivOfPresentation` does, and a statement about *two*
adapted opens and a chart cannot substitute the presentations of both.  Here the localization
instances come from `AlgebraicGeometry.IsAffineOpen.isLocalization_of_eq_basicOpen` and
`Stacks.Modules.isLocalizedModule_chartSectionOfLE`, which take the equality of opens as a
hypothesis, so nothing is substituted.

**`HubRestrict f` is now discharged, by `Stacks.Discriminant.hubRestrict` in
`RelativeDualizingModuleExistence0BVG`, where `Stacks.Discriminant.exists_relativeDualizingModule`
carries `@[stacks 0BVG "existence"]`.  No declaration in this file carries a `@[stacks 0BVG]`
attribute.** Tag 0BVG asserts that the
relative dualizing module *exists*, and the module produced here exists only under the
hypothesis `HubRestrict f`, which is the one remaining input of the glueing: that the two-step
comparison of a chart with the hub of an adapted open commutes with restriction to a smaller
adapted open, through a map of hubs independent of the chart.  The three compatibilities of
Tag 0BT2 it is to be assembled from are all available —
`Stacks.Discriminant.localizedModule_dualizingModule_equiv_trans` for the target localization,
`Stacks.Discriminant.dualizingModule_equiv_of_isLocalization_away_trans` for the base
replacement, and `Stacks.Discriminant.localizedModule_dualizingModule_equiv_comm_base` for their
commutation — together with the uniqueness of the normalised localization map
(`Stacks.Discriminant.localizedDualizingModuleMap_eq_of_eq_id`) that makes the resulting map of
hubs independent of the chart.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 0BSZ](https://stacks.math.columbia.edu/tag/0BSZ)
* [Stacks Project, Tag 0BT1](https://stacks.math.columbia.edu/tag/0BT1)
* [Stacks Project, Tag 0BT2](https://stacks.math.columbia.edu/tag/0BT2)
* [Stacks Project, Tag 0BVG](https://stacks.math.columbia.edu/tag/0BVG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.Modules

variable {Y : Scheme.{u}}

/-- The canonical map from a module over an affine chart to the sections of its chart sheaf over
an open contained in the chart, as a `Γ(Y, V)`-linear map. -/
public def chartSectionOfLE (V : Y.affineOpens) (M : ModuleCat.{u} Γ(Y, V.1)) {W : Y.Opens}
    (hWV : W ≤ V.1) :
    letI := moduleOfLE (chartSheaf V M) hWV
    M →ₗ[Γ(Y, V.1)] Γ(chartSheaf V M, W) :=
  letI := moduleOfLE (chartSheaf V M) hWV
  (restrictₗ (chartSheaf V M) hWV).comp (chartTopEquiv V M).toLinearMap

/-- **The sections of a chart sheaf over a principal open are a localization.** If the open `W`
is the principal open cut out by `g` then the sections of `chartSheaf V M` over `W` are the
localization of `M` away from `g`. -/
@[ega "I 1.3.7" "more general"]
public theorem isLocalizedModule_chartSectionOfLE (V : Y.affineOpens)
    (M : ModuleCat.{u} Γ(Y, V.1)) (g : Γ(Y, V.1)) {W : Y.Opens} (hWV : W ≤ V.1)
    (hW : W = Y.basicOpen g) :
    letI := moduleOfLE (chartSheaf V M) hWV
    IsLocalizedModule (Submonoid.powers g) (chartSectionOfLE V M hWV) := by
  subst hW
  have h := isLocalizedModule_chartSectionBasicOpen V M g
  rw [chartSectionBasicOpen_eq_comp] at h
  exact h

end Stacks.Modules

namespace Stacks.Discriminant

/-- **One localization of a module through another.** Let `S` be the localization of `R` away
from `a`, let `T` be the localization of `S` away from the image of `b : R`, let `lm₁` present
`M₁` as the localization of `N` away from `a` and `lm₂` present `M₂` as its localization away
from `b`, and let `φ : M₁ → M₂` be an `S`-linear map compatible with the two.  Then `φ` presents
`M₂` as the localization of `M₁` away from the image of `b`. -/
public theorem isLocalizedModule_away_of_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    {N M₁ M₂ : Type*} [AddCommGroup N] [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R N] [Module R M₁] [Module S M₁] [IsScalarTower R S M₁]
    [Module R M₂] [Module S M₂] [Module T M₂] [IsScalarTower R S M₂] [IsScalarTower S T M₂]
    (a b : R) [IsLocalization.Away a S] [IsLocalization.Away (algebraMap R S b) T]
    (lm₁ : N →ₗ[R] M₁) (lm₂ : N →ₗ[R] M₂) (φ : M₁ →ₗ[S] M₂)
    (hlm₁ : IsLocalizedModule (Submonoid.powers a) lm₁)
    (hlm₂ : IsLocalizedModule (Submonoid.powers b) lm₂)
    (hφ : ∀ n, φ (lm₁ n) = lm₂ n) :
    IsLocalizedModule (Submonoid.powers (algebraMap R S b)) φ := by
  have : IsLocalizedModule.Away a lm₁ := hlm₁
  have : IsLocalizedModule.Away b lm₂ := hlm₂
  refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ ?_ ?_
  · have hu : IsUnit (algebraMap S T (algebraMap R S b)) :=
      IsLocalization.Away.algebraMap_isUnit (algebraMap R S b)
    have hend := hu.map (algebraMap T (Module.End T M₂))
    rw [Module.End.isUnit_iff] at hend ⊢
    have hfun : ((algebraMap S (Module.End S M₂) (algebraMap R S b)) : M₂ → M₂) =
        ((algebraMap T (Module.End T M₂) (algebraMap S T (algebraMap R S b))) : M₂ → M₂) := by
      funext x
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply,
        IsScalarTower.algebraMap_smul T (algebraMap R S b) x]
    rw [hfun]
    exact hend
  · intro x
    obtain ⟨n, y, hy⟩ := IsLocalizedModule.Away.surj lm₂ b x
    refine ⟨n, lm₁ y, ?_⟩
    rw [hφ y, ← hy, ← map_pow, IsScalarTower.algebraMap_smul S]
  · intro x hx
    obtain ⟨p, z, hz⟩ := IsLocalizedModule.Away.surj lm₁ a x
    have hz₀ : lm₂ z = 0 := by
      rw [← hφ z, ← hz, ← IsScalarTower.algebraMap_smul S (a ^ p) x, map_smul, hx, smul_zero]
    obtain ⟨q, hq⟩ := IsLocalizedModule.Away.exists_of_eq b
      (hz₀.trans (map_zero lm₂).symm)
    rw [smul_zero] at hq
    have hinj : Function.Injective
        ((algebraMap R (Module.End R M₁) (a ^ p) : Module.End R M₁) : M₁ → M₁) :=
      ((Module.End.isUnit_iff _).mp
        (IsLocalizedModule.map_units (S := Submonoid.powers a) lm₁
          ⟨a ^ p, ⟨p, rfl⟩⟩)).1
    refine ⟨q, ?_⟩
    rw [← map_pow, IsScalarTower.algebraMap_smul S]
    apply hinj
    rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, smul_zero, smul_comm, hz,
      ← map_smul, hq, map_zero]

variable {X Y : Scheme.{u}} (f : Y ⟶ X)
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  [LocallyOfFiniteType f] [LocallyQuasiFinite f]

/-- The sheaf of `𝒪_Y`-modules determined by the algebraic relative dualizing module of an
adapted open, read on its source open. -/
public def adaptedChartSheaf (k : AdaptedOpen f) : Y.Modules :=
  letI : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
    (f.appLE k.base k.source k.source_le).hom.toAlgebra
  Stacks.Modules.chartSheaf k.source
    (ModuleCat.of _ (dualizingModule (adaptedFactorization f k)))

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyOfFiniteType f]
  [LocallyQuasiFinite f] in
/-- The source opens of the adapted opens of a morphism cover the source. -/
public theorem iSup_adaptedOpen_source_eq_top :
    (⨆ k : AdaptedOpen f, k.source.1) = ⊤ := by
  refine top_le_iff.mp fun y _ ↦ ?_
  obtain ⟨U, V, hyV, hVU⟩ := exists_affineChartPair f y
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, U, hVU⟩, hyV⟩

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] in
/-- The chart sheaf of an adapted open is quasi-coherent on its source open. -/
public theorem isQuasicoherent_restrict_adaptedChartSheaf (k : AdaptedOpen f) :
    ((adaptedChartSheaf f k).restrict k.source.1.ι).IsQuasicoherent :=
  Stacks.Modules.isQuasicoherent_restrict_chartSheaf _ _

omit [IsLocallyNoetherian Y] in
/-- The chart sheaf of an adapted open is of finite type on its source open. -/
public theorem isFiniteType_restrict_adaptedChartSheaf (k : AdaptedOpen f) :
    ((adaptedChartSheaf f k).restrict k.source.1.ι).IsFiniteType := by
  let : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
    (f.appLE k.base k.source k.source_le).hom.toAlgebra
  let : IsNoetherianRing Γ(X, k.base.1) :=
    IsLocallyNoetherian.component_noetherian k.base
  exact Stacks.Modules.isFiniteType_restrict_chartSheaf _ _
    (finite_dualizingModule (adaptedFactorization f k))

section Hub

variable (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
  (k : AdaptedOpen f) (hk : k.Good V U)

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyOfFiniteType f]
  [LocallyQuasiFinite f] in
/-- The base open of an adapted open good for a chart lies inside the chart's base open. -/
public theorem AdaptedOpen.Good.baseLE {k : AdaptedOpen f} {V : Y.affineOpens}
    {U : X.affineOpens} (hk : k.Good V U) : k.base.1 ≤ U.1 := by
  obtain ⟨-, ⟨a, ha⟩⟩ := hk
  exact ha ▸ X.basicOpen_le a

/-- A factorization of the coordinate-ring map of the chart's base and the adapted open's
source open. -/
public def hubMiddleFactorization :
    letI : Algebra Γ(X, U.1) Γ(Y, k.source.1) :=
      (f.appLE U.1 k.source.1 (hk.le.trans hVU)).hom.toAlgebra
    FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, k.source.1) :=
  (nonempty_relativeDualizingChartFactorization f U k.source (hk.le.trans hVU)).some

/-- **The comparison of a chart with the dualizing module of an adapted open good for it.**
Tag 0BT2 part (2) localizes the target from `Γ(Y, V)` to the adapted open's source open,
keeping the base `Γ(X, U)`; part (1) then replaces that base by the adapted open's base. -/
public def chartHub :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    letI : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
      (f.appLE k.base k.source k.source_le).hom.toAlgebra
    ∀ F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1),
      Γ(Stacks.Modules.chartSheaf V (ModuleCat.of _ (dualizingModule F)), k.source.1)
        ≃ₗ[Γ(Y, k.source.1)] dualizingModule (adaptedFactorization f k) := by
  letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  letI : Algebra Γ(Y, V.1) Γ(Y, k.source.1) := algebraOfLE Y hk.le
  letI : Algebra Γ(X, U.1) Γ(Y, k.source.1) :=
    (f.appLE U.1 k.source.1 (hk.le.trans hVU)).hom.toAlgebra
  letI : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
    (f.appLE k.base k.source k.source_le).hom.toAlgebra
  letI : Algebra Γ(X, U.1) Γ(X, k.base.1) := algebraOfLE X hk.baseLE
  letI : IsScalarTower Γ(X, U.1) Γ(Y, V.1) Γ(Y, k.source.1) :=
    IsScalarTower.of_algebraMap_eq' (by
      change (f.appLE U.1 k.source.1 (hk.le.trans hVU)).hom =
        ((Y.presheaf.map (homOfLE hk.le).op).hom).comp (f.appLE U V hVU).hom
      rw [← CommRingCat.hom_comp, ← f.appLE_map hVU (homOfLE hk.le).op])
  letI : IsScalarTower Γ(X, U.1) Γ(X, k.base.1) Γ(Y, k.source.1) :=
    IsScalarTower.of_algebraMap_eq' (by
      change (f.appLE U.1 k.source.1 (hk.le.trans hVU)).hom =
        ((f.appLE k.base.1 k.source.1 k.source_le).hom).comp
          (X.presheaf.map (homOfLE hk.baseLE).op).hom
      rw [← CommRingCat.hom_comp, f.map_appLE k.source_le (homOfLE hk.baseLE).op])
  letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  letI : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  letI : IsNoetherianRing Γ(Y, k.source.1) :=
    IsLocallyNoetherian.component_noetherian k.source
  letI : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
  letI : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, k.source.1) :=
    RingHom.quasiFinite_algebraMap.mp
      (LocallyQuasiFinite.quasiFinite_appLE U.2 k.source.2 (hk.le.trans hVU))
  letI : IsLocalization.Away hk.1.choose Γ(Y, k.source.1) :=
    V.2.isLocalization_of_eq_basicOpen _ (homOfLE hk.le) hk.1.choose_spec.symm
  letI : IsLocalization.Away hk.2.choose Γ(X, k.base.1) :=
    U.2.isLocalization_of_eq_basicOpen _ (homOfLE hk.baseLE) hk.2.choose_spec.symm
  intro F
  letI := moduleOfLE (Stacks.Modules.chartSheaf V (ModuleCat.of _ (dualizingModule F))) hk.le
  letI := isScalarTowerOfLE
    (Stacks.Modules.chartSheaf V (ModuleCat.of _ (dualizingModule F))) hk.le
  exact (localizedModule_dualizingModule_equiv hk.1.choose F
        (hubMiddleFactorization f U V hVU k hk)
        (Stacks.Modules.chartSectionOfLE V (ModuleCat.of _ (dualizingModule F)) hk.le)
        (Stacks.Modules.isLocalizedModule_chartSectionOfLE V _ _ hk.le
          hk.1.choose_spec.symm)).trans
    (dualizingModule_equiv_of_isLocalization_away hk.2.choose
      (hubMiddleFactorization f U V hVU k hk) (adaptedFactorization f k))

end Hub

/-- The comparison of the sections of the chart sheaf of an adapted open `i` over an adapted
open `k` good for it with the algebraic relative dualizing module of `k`. -/
public def adaptedHub (k i : AdaptedOpen f) (hki : k.Good i.source i.base) :
    letI : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
      (f.appLE k.base k.source k.source_le).hom.toAlgebra
    Γ(adaptedChartSheaf f i, k.source.1)
      ≃ₗ[Γ(Y, k.source.1)] dualizingModule (adaptedFactorization f k) :=
  letI : Algebra Γ(X, i.base.1) Γ(Y, i.source.1) :=
    (f.appLE i.base i.source i.source_le).hom.toAlgebra
  chartHub f i.base i.source i.source_le k hki (adaptedFactorization f i)

/-- The comparison of the chart sheaves of two adapted opens over an adapted open good for
both, obtained by composing the comparison of the first with the adapted open's dualizing
module and the inverse of the comparison of the second. -/
public def adaptedSheafComparison (k i j : AdaptedOpen f)
    (hki : k.Good i.source i.base) (hkj : k.Good j.source j.base) :
    Γ(adaptedChartSheaf f i, k.source.1) ≃ₗ[Γ(Y, k.source.1)]
      Γ(adaptedChartSheaf f j, k.source.1) :=
  (adaptedHub f k i hki).trans (adaptedHub f k j hkj).symm

/-- **The cocycle identity is free.** All three comparisons between three charts over one
adapted open factor through the dualizing module of that adapted open. -/
public theorem adaptedSheafComparison_trans (k i j m : AdaptedOpen f)
    (hi : k.Good i.source i.base) (hj : k.Good j.source j.base)
    (hm : k.Good m.source m.base) (s : Γ(adaptedChartSheaf f i, k.source.1)) :
    adaptedSheafComparison f k j m hj hm (adaptedSheafComparison f k i j hi hj s) =
      adaptedSheafComparison f k i m hi hm s := by
  simp only [adaptedSheafComparison, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

/-- The per-chart comparison of the hubs of two nested adapted opens: a map between the
algebraic relative dualizing modules of the two adapted opens, independent of the chart, which
intertwines the hub comparisons with restriction of sections. -/
public def HubRestrict : Prop :=
  ∀ (k l : AdaptedOpen f) (_ : l.base.1 ≤ k.base.1) (hW : l.source.1 ≤ k.source.1),
    letI : Algebra Γ(X, k.base.1) Γ(Y, k.source.1) :=
      (f.appLE k.base k.source k.source_le).hom.toAlgebra
    letI : Algebra Γ(X, l.base.1) Γ(Y, l.source.1) :=
      (f.appLE l.base l.source l.source_le).hom.toAlgebra
    ∃ Θ : dualizingModule (adaptedFactorization f k) →
        dualizingModule (adaptedFactorization f l),
      ∀ (i : AdaptedOpen f) (hki : k.Good i.source i.base)
        (hli : l.Good i.source i.base) (s : Γ(adaptedChartSheaf f i, k.source.1)),
        adaptedHub f l i hli
            ((adaptedChartSheaf f i).presheaf.map (homOfLE hW).op s) =
          Θ (adaptedHub f k i hki s)

/-- **The restriction compatibility of the chart comparison**, in the shape a glueing datum
asks for, from the per-chart comparison of the hubs of two nested adapted opens. -/
public theorem adaptedSheafComparison_restrict (hsq : HubRestrict f)
    (k l i j : AdaptedOpen f) (hki : k.Good i.source i.base)
    (hkj : k.Good j.source j.base) (hli : l.Good i.source i.base)
    (hlj : l.Good j.source j.base) (hW : l.source.1 ≤ k.source.1)
    (s : Γ(adaptedChartSheaf f i, k.source.1)) :
    adaptedSheafComparison f l i j hli hlj
        ((adaptedChartSheaf f i).presheaf.map (homOfLE hW).op s) =
      (adaptedChartSheaf f j).presheaf.map (homOfLE hW).op
        (adaptedSheafComparison f k i j hki hkj s) := by
  refine AdaptedOpen.restrict_comparison_of_source_le (f := f) (fun m ↦ m.source)
    (fun m ↦ m.base) (adaptedChartSheaf f)
    (fun m a b ha hb ↦ adaptedSheafComparison f m a b ha hb)
    (fun k' l' i' j' hki' hkj' hli' hlj' hW' hB' s' ↦ ?_) k l i j hki hkj hli hlj hW s
  obtain ⟨Θ, hΘ⟩ := hsq k' l' hB' hW'
  have hji : adaptedHub f k' j' hkj'
      ((adaptedHub f k' j' hkj').symm (adaptedHub f k' i' hki' s')) =
      adaptedHub f k' i' hki' s' := LinearEquiv.apply_symm_apply _ _
  have h1 := hΘ i' hki' hli' s'
  have h2 := hΘ j' hkj' hlj'
    ((adaptedHub f k' j' hkj').symm (adaptedHub f k' i' hki' s'))
  rw [hji] at h2
  simp only [adaptedSheafComparison, LinearEquiv.trans_apply]
  rw [h1, ← h2, LinearEquiv.symm_apply_apply]

/-- **The relative dualizing module of a locally quasi-finite morphism, modulo the restriction
compatibility of the chart comparison.** There is a coherent quasi-coherent `𝒪_Y`-module whose
sections over every affine chart of `f` are the algebraic relative dualizing module of that
chart, compatibly with restriction inside a chart and with the chart comparison over the
adapted opens. -/
public theorem exists_relativeDualizingModule_of_hubRestrict (hsq : HubRestrict f) :
    ∃ (M : Y.Modules)
      (c : ∀ (i : AdaptedOpen f) (W : Y.Opens), W ≤ i.source.1 →
        Γ(M, W) ≃ₗ[Γ(Y, W)] Γ(adaptedChartSheaf f i, W)),
      M.IsQuasicoherent ∧ _root_.SheafOfModules.IsCoherent M ∧
        (∀ (i : AdaptedOpen f) (W W' : Y.Opens) (hW : W ≤ i.source.1) (h : W' ≤ W)
          (s : Γ(M, W)),
          c i W' (h.trans hW) (M.presheaf.map (homOfLE h).op s) =
            (adaptedChartSheaf f i).presheaf.map (homOfLE h).op (c i W hW s)) ∧
        (∀ (k i j : AdaptedOpen f) (hki : k.Good i.source i.base)
          (hkj : k.Good j.source j.base) (s : Γ(M, k.source.1)),
          c j k.source.1 hkj.le s =
            adaptedSheafComparison f k i j hki hkj (c i k.source.1 hki.le s)) :=
  Stacks.Modules.exists_coherent_glued_of_basisComparison
    (fun i : AdaptedOpen f ↦ i.source.1) (iSup_adaptedOpen_source_eq_top f)
    (adaptedChartSheaf f) (isQuasicoherent_restrict_adaptedChartSheaf f)
    (isFiniteType_restrict_adaptedChartSheaf f)
    (fun k : AdaptedOpen f ↦ k.source.1) (fun k i ↦ k.Good i.source i.base)
    (fun _ _ h ↦ h.le)
    (AdaptedOpen.exists_good_pair (f := f) (fun m : AdaptedOpen f ↦ m.source)
      (fun m : AdaptedOpen f ↦ m.base) fun m ↦ m.source_le)
    (AdaptedOpen.exists_good_triple (f := f) (fun m : AdaptedOpen f ↦ m.source)
      (fun m : AdaptedOpen f ↦ m.base) fun m ↦ m.source_le)
    (fun m a b ha hb ↦ adaptedSheafComparison f m a b ha hb)
    (adaptedSheafComparison_restrict f hsq)
    (adaptedSheafComparison_trans f)

end Stacks.Discriminant

end
