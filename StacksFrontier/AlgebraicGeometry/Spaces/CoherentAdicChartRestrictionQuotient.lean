module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeNonAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicAffineQuotientSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AffineComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AffineSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalPullback
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionFunctor
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Sections
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerChartComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientMap

/-!
# The chart restriction of an adic quotient

Let `X` be an algebraic space over a scheme `S`, let `A` be an étale scheme chart of `X` and let
`M` be a quasi-coherent `𝒪_X`-module.  The chart restriction
`AlgebraicGeometry.Space.chartRestrictionSheaf` carries `M` to a quasi-coherent module `ρ M` on
the Zariski site of the chart's scheme whose sections over an open `O` are, on the nose, the
sections of `M` over the étale chart `O` cuts out.

This file adds two things.  First the action of the chart restriction on morphisms,
`AlgebraicGeometry.Space.chartRestrictionSheafMap`, with its sections on the nose.  Second the
comparison of adic quotients: if `𝓘 ⊆ 𝒪_X` is a sheaf of ideals cartesian on affine charts and
`Ī` is a Zariski sheaf of ideals of the chart's scheme which, over every affine open, generates
`𝓘` on the chart the open cuts out, then

`ρ M / Ī ^ k ρ M ≅ ρ (M / 𝓘 ^ k M)`,

compatibly with the two projections from `ρ M`.

## Main definitions

* `AlgebraicGeometry.Space.chartRestrictionSheafMap` — the chart restriction of a morphism.
* `AlgebraicGeometry.Space.chartRestrictionQuotientHom` — the comparison of the quotients.

## Main results

* `AlgebraicGeometry.Space.isIso_chartRestrictionQuotientHom` — **the comparison is an
  isomorphism**: over an affine open both sides are `M(Z) / 𝓘(Z) ^ k M(Z)`.

## References

* [Stacks Project, Tag 08BD](https://stacks.math.columbia.edu/tag/08BD)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The additive presheaf map underlying `chartRestrictionSheafMap`. -/
def chartRestrictionPresheafHom {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N)
    (A : SmallEtale B S hS X.1) :
    (chartRestrictionSheaf B S hS X M A).val.presheaf ⟶
      (chartRestrictionSheaf B S hS X N A).val.presheaf where
  app O := AddCommGrpCat.ofHom
    { toFun x := ULift.up (φ.val.app (op ((chartOpens B S hS A).obj O.unop)) x.down)
      map_zero' := congrArg ULift.up (map_zero _)
      map_add' x y := congrArg ULift.up (map_add _ x.down y.down) }
  naturality {O O'} k := by
    refine AddCommGrpCat.ext fun x => ?_
    exact congrArg ULift.up (congrArg (fun ψ => ψ x.down) (congrArg (fun χ => χ.hom)
      (φ.val.naturality ((chartOpens B S hS A).map k.unop).op)))

/-- The map of chart restrictions induced by a morphism of `𝒪_X`-modules. -/
def chartRestrictionSheafMap {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N)
    (A : SmallEtale B S hS X.1) :
    chartRestrictionSheaf B S hS X M A ⟶ chartRestrictionSheaf B S hS X N A where
  val := PresheafOfModules.homMk (chartRestrictionPresheafHom B S hS X φ A) fun O r x =>
    congrArg ULift.up ((φ.val.app (op ((chartOpens B S hS A).obj O.unop))).hom.map_smul
      ((chartRestrictionRingHom B S hS X.2 A).app O r) x.down)

/-- Over a Zariski open `O`, `chartRestrictionSheafMap φ A` acts on sections as `φ` over the étale
chart `O` cuts out. -/
theorem chartRestrictionSheafMap_val_app {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N)
    (A : SmallEtale B S hS X.1) (O : (chartScheme A).Opens)
    (x : (chartRestrictionSheaf B S hS X M A).val.obj (op O)) :
    (chartRestrictionSheafMap B S hS X φ A).val.app (op O) x =
      ULift.up (φ.val.app (op ((chartOpens B S hS A).obj O)) x.down) := rfl

/-- Over a Zariski open `O` of the chart's scheme, the ring map `O.topIso.inv` is bijective. -/
theorem bijective_chartRestrictionRingAt (A : SmallEtale B S hS X.1) (O : (chartScheme A).Opens) :
    Function.Bijective O.topIso.inv.hom :=
  (ConcreteCategory.isIso_iff_bijective _).1 inferInstance

section Quotient

variable (𝓘 : (SheafOfModules.unit.{u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).Submodule)
    (M : Modules.{u, u} B S hS X.1 X.2)
    (A : SmallEtale B S hS X.1) (Ibar : (chartScheme A).IdealSheafData)
    (hIbar : ∀ O : (chartScheme A).affineOpens,
      Ideal.map O.1.topIso.inv.hom (Ibar.ideal O) =
        chartSectionIdeal B S hS X.1 X.2 𝓘 ((chartOpens B S hS A).obj O.1))
    (k : ℕ)

include hIbar in
/-- **The chart restriction of `M / 𝓘 ^ k M` is annihilated by the `k`-th power of the Zariski
ideal over every affine open**, the Zariski ideal generating `𝓘` on the charts the affine opens
cut out. -/
theorem pow_smul_top_chartRestrictionSheaf_idealPowerQuotient_eq_bot
    (O : (chartScheme A).affineOpens) :
    Ibar.ideal O ^ k • (⊤ : Submodule Γ(chartScheme A, O.1)
      Γ(chartRestrictionSheaf B S hS X (idealPowerQuotient B S hS X.1 X.2 𝓘 k M) A, O.1)) = ⊥ := by
  refine eq_bot_iff.mpr (Submodule.smul_le.mpr fun r hr y _ => ?_)
  have hr' : O.1.topIso.inv.hom r ∈ Ideal.map O.1.topIso.inv.hom (Ibar.ideal O ^ k) :=
    Ideal.mem_map_of_mem _ hr
  rw [Ideal.map_pow, hIbar O] at hr'
  have h := isPowAnnihilated_idealPowerQuotient B S hS X.1 X.2 𝓘 k M
    ((chartOpens B S hS A).obj O.1) _ hr' y.down
  rw [Submodule.mem_bot]
  exact congrArg ULift.up h

/-- The zero morphism out of the sheaf of modules underlying a subsheaf on a scheme. -/
local instance zeroHomOfSchemeSheafOfModules {Y : Scheme.{u}}
    (A : SheafOfModules.{u} Y.ringCatSheaf) (N : Y.Modules) : Zero (A ⟶ N) :=
  HasZeroMorphisms.zero (C := Y.Modules) A N

/-- A sheaf submodule contained in the sectionwise kernel of a morphism is killed by it. -/
theorem ι_comp_eq_zero_of_le_kernelSubmodule {Y : Scheme.{u}}
    {N P : Y.Modules} (f : N ⟶ P) (Q : N.Submodule)
    (h : Q ≤ Stacks.Algebraization.kernelSubmodule f) : Q.ι ≫ f = 0 := by
  ext U x
  have hx : x.1 ∈ (Stacks.Algebraization.kernelSubmodule f).toSubmodule.obj U := h U x.2
  rw [Stacks.Algebraization.kernelSubmodule_toSubmodule_obj, LinearMap.mem_ker] at hx
  exact hx

include hIbar in
/-- `𝓘 ^ k`-power multiples, read on the chart's scheme through the Zariski ideal, die in the
chart restriction of `M / 𝓘 ^ k M`. -/
theorem idealPowerMultiple_ι_comp_chartRestrictionSheafMap_π :
    (Stacks.Algebraization.idealPowerMultiple Ibar k
        (chartRestrictionSheaf B S hS X M A)).ι ≫
      chartRestrictionSheafMap B S hS X
        (cokernel.π (idealPowerMultiple B S hS X.1 X.2 𝓘 k M).ι) A = 0 :=
  ι_comp_eq_zero_of_le_kernelSubmodule _ _
    (Stacks.Coherent.idealPowerMultiple_le_kernelSubmodule Ibar k _ fun O =>
      pow_smul_top_chartRestrictionSheaf_idealPowerQuotient_eq_bot B S hS X 𝓘 M A Ibar hIbar k O)

/-- **The comparison of the two quotients**: `ρ M / Ī ^ k ρ M ⟶ ρ (M / 𝓘 ^ k M)`, where `ρ` is the
chart restriction to `A` and `Ī` is a Zariski ideal of the chart's scheme generating `𝓘`. -/
def chartRestrictionQuotientHom :
    Stacks.Algebraization.idealPowerQuotient Ibar k (chartRestrictionSheaf B S hS X M A) ⟶
      chartRestrictionSheaf B S hS X (idealPowerQuotient B S hS X.1 X.2 𝓘 k M) A :=
  cokernel.desc _ _ (idealPowerMultiple_ι_comp_chartRestrictionSheafMap_π B S hS X 𝓘 M A Ibar
      hIbar k)

/-- The comparison `chartRestrictionQuotientHom` composed with the projection
`ρ M ⟶ ρ M / Ī ^ k ρ M` is the chart restriction of the projection `M ⟶ M / 𝓘 ^ k M`. -/
theorem π_comp_chartRestrictionQuotientHom :
    cokernel.π (Stacks.Algebraization.idealPowerMultiple Ibar k
        (chartRestrictionSheaf B S hS X M A)).ι ≫
      chartRestrictionQuotientHom B S hS X 𝓘 M A Ibar hIbar k =
      chartRestrictionSheafMap B S hS X
        (cokernel.π (idealPowerMultiple B S hS X.1 X.2 𝓘 k M).ι) A :=
  cokernel.π_desc _ _ _

include hIbar in
/-- **The comparison of the two quotients is an isomorphism**: over an affine open `O` of the
chart's scheme both sides are `M(Z) / 𝓘(Z) ^ k M(Z)` for the affine chart `Z` cut out by `O`. -/
theorem isIso_chartRestrictionQuotientHom
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules) (hM : M.IsQuasicoherentOnSite) :
    IsIso (chartRestrictionQuotientHom B S hS X 𝓘 M A Ibar hIbar k) := by
  have hMc := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 M hM
  have : (chartRestrictionSheaf B S hS X M A).IsQuasicoherent :=
    isQuasicoherent_chartRestrictionSheaf B S hS X M hM A
  refine Stacks.Algebraization.isIso_of_affine_sections_bijective _ fun O => ?_
  have key := fun x : (chartRestrictionSheaf B S hS X M A).val.obj (op O.1) =>
    congrArg (fun φ => φ.val.app (op O.1) x)
      (π_comp_chartRestrictionQuotientHom B S hS X 𝓘 M A Ibar hIbar k)
  refine ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
    obtain ⟨x, rfl⟩ := @Stacks.Algebraization.surjective_app_of_epi_of_isAffineOpen _ _ _
      inferInstance (Stacks.Algebraization.isQuasicoherent_idealPowerQuotient Ibar k _)
      (cokernel.π (C := (chartScheme A).Modules) (Stacks.Algebraization.idealPowerMultiple Ibar k
        (chartRestrictionSheaf B S hS X M A)).ι) inferInstance O z
    have h1 := congrArg ULift.down ((key x).symm.trans hz)
    have h2 : (x.down : M.val.obj (op ((chartOpens B S hS A).obj O.1))) ∈
        chartSectionIdeal B S hS X.1 X.2 𝓘 ((chartOpens B S hS A).obj O.1) ^ k •
          (⊤ : Submodule (chartRing B S hS X.1 X.2 ((chartOpens B S hS A).obj O.1))
            (M.val.obj (op ((chartOpens B S hS A).obj O.1)))) := by
      rw [← ker_val_app_idealPowerQuotient_π B S hS X.1 X.2 𝓘 hIcart M hMc k
        (V := (chartOpens B S hS A).obj O.1) O.2]
      exact h1
    have h3 : x ∈ Ibar.ideal O ^ k • (⊤ : Submodule Γ(chartScheme A, O.1)
        Γ(chartRestrictionSheaf B S hS X M A, O.1)) := by
      refine Stacks.Submodule.mem_pow_smul_top_of_mem_map_pow_smul_top
        (R' := chartRing B S hS X.1 X.2 ((chartOpens B S hS A).obj O.1))
        (M := Γ(chartRestrictionSheaf B S hS X M A, O.1))
        (M' := M.val.obj (op ((chartOpens B S hS A).obj O.1))) O.1.topIso.inv.hom
        (bijective_chartRestrictionRingAt B S hS X A O.1).2 AddEquiv.ulift
        (fun r y => rfl) (Ibar.ideal O) k ?_
      exact (hIbar O).symm ▸ h2
    rw [← Stacks.Algebraization.idealPowerMultiple_toSubmodule_obj_affine] at h3
    exact (Stacks.Algebraization.cokernel_π_app_eq_zero_iff _ _ _ _).2 h3
  · intro y
    obtain ⟨x, hx⟩ := surjective_val_app_idealPowerQuotient_π B S hS X.1 X.2 𝓘 hIcart M hMc k
      (V := (chartOpens B S hS A).obj O.1) O.2 y.down
    exact ⟨_, (key (ULift.up x)).trans (congrArg ULift.up hx)⟩

end Quotient

end AlgebraicGeometry.Space

end
