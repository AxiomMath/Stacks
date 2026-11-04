module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdicSectionsOfSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.PushforwardIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardRightExact
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerAffineChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsOnSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardGlobalSections

/-!
# Degree-zero formal functions along a closed immersion

Let `A` be a ring, `I ⊆ A` an ideal, `X` an algebraic space over `Spec A`, `i : Z ⟶ X` a closed
immersion and `G` a quasi-coherent `𝒪_Z`-module.  This file proves that the theorem on formal
functions in degree zero for `G` on `Z`, the bijectivity of

`H⁰(Z, G) ⟶ limₙ H⁰(Z, G / (I 𝒪_Z) ^ (n + 1) G)`,

implies the same statement for `i_* G` on `X`, with the ideal sheaf `I 𝒪_X`: the direct image of
the reduction of `G` modulo `(I 𝒪_Z) ^ k` is the reduction of `i_* G` modulo `(I 𝒪_X) ^ k`, and
global sections of a direct image are global sections.

## Main results

* `AlgebraicGeometry.Space.mem_idealPowerMultiple_smallBaseChangeModulePushforward` — a section
  of `(I 𝒪_Z) ^ k G` over the base change of an étale chart of `X` is a section of
  `(I 𝒪_X) ^ k (i_* G)` over that chart, for an affine representable morphism `Z ⟶ X`.
* `AlgebraicGeometry.Space.isIso_smallBaseChangeAdicQuotientComparison` — the comparison
  `i_* G / (I 𝒪_X) ^ k i_* G ⟶ i_* (G / (I 𝒪_Z) ^ k G)` is an isomorphism.
* `AlgebraicGeometry.Space.bijective_adicSectionsOfSections_modulePushforward_of_isClosedImmersion`
  and `AlgebraicGeometry.Space.bijective_adicSectionsOfSections_closedSubspacePushforward` —
  **the transport of degree-zero formal functions along a closed immersion.**

## Implementation notes

The direct image is computed through `AlgebraicGeometry.Space.smallBaseChangeModulePushforward`,
whose sections over a chart `U` of `X` are, by definition, the sections over the base-changed
chart `U ×_X Z`; the result is transported to `AlgebraicGeometry.Space.modulePushforward` along
`AlgebraicGeometry.Space.modulePushforwardChartIso`.  Of the two containments between
`(I 𝒪_X) ^ k (i_* G)` and `i_* ((I 𝒪_Z) ^ k G)`, the first is formal (the direct image of a module
annihilated by `(I 𝒪_Z) ^ k` is annihilated by `(I 𝒪_X) ^ k`); the second is checked on affine
charts, where both sides are computed: over an affine chart `U` the chart `U ×_X Z` is affine, and
there `(I 𝒪_Z) ^ k G` is `I ^ k G(U ×_X Z)`.  The cokernel then commutes with the direct image
because the direct image along a closed immersion is right exact.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] hasCokernels_modules

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}

/-! ### Global sections of a direct image -/

section Sections

variable {X Y : AlgebraicSpaces B (Spec (.of A)) hA} (f : Y ⟶ X)

/-- The sections of two isomorphic modules correspond. -/
def sectionsEquivOfIso {M M' : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2} (e : M ≅ M') :
    M.sections ≃ M'.sections where
  toFun := SheafOfModules.sectionsMap e.hom
  invFun := SheafOfModules.sectionsMap e.inv
  left_inv s := by rw [← SheafOfModules.sectionsMap_comp, e.hom_inv_id,
      SheafOfModules.sectionsMap_id]
  right_inv s := by rw [← SheafOfModules.sectionsMap_comp, e.inv_hom_id,
      SheafOfModules.sectionsMap_id]

variable (hf : yoneda.relativelyRepresentable f.hom)

/-- `AlgebraicGeometry.Space.smallBaseChangeModulePushforward`, read as a functor between the
categories `AlgebraicGeometry.Space.Modules` of the two algebraic spaces. -/
abbrev chartPushforwardModules :
    Modules.{u, u} B (Spec (.of A)) hA Y.1 Y.2 ⥤ Modules.{u, u} B (Spec (.of A)) hA X.1 X.2 :=
  smallBaseChangeModulePushforward.{u, u} B (Spec (.of A)) hA f hf

/-- Global sections of the base-change direct image are global sections. -/
def smallBaseChangeSectionsEquiv (N : Modules.{u, u} B (Spec (.of A)) hA Y.1 Y.2) :
    ((chartPushforwardModules f hf).obj N).sections ≃
      N.sections :=
  (sectionsEquivOfIso ((modulePushforwardChartIso B (Spec (.of A)) hA f hf).app N)).symm.trans
    (modulePushforwardSectionsEquiv B (Spec (.of A)) hA f N)

/-- The identification `AlgebraicGeometry.Space.smallBaseChangeSectionsEquiv` of global sections
is natural in the module. -/
theorem smallBaseChangeSectionsEquiv_sectionsMap
    {N N' : Modules.{u, u} B (Spec (.of A)) hA Y.1 Y.2} (g : N ⟶ N')
    (s : ((chartPushforwardModules f hf).obj N).sections) :
    smallBaseChangeSectionsEquiv f hf N'
        (SheafOfModules.sectionsMap
          ((chartPushforwardModules f hf).map g) s) =
      SheafOfModules.sectionsMap g (smallBaseChangeSectionsEquiv f hf N s) := by
  show modulePushforwardSectionsEquiv B (Spec (.of A)) hA f N'
      (SheafOfModules.sectionsMap ((modulePushforwardChartIso B (Spec (.of A)) hA f hf).app N').inv
        (SheafOfModules.sectionsMap
          ((chartPushforwardModules f hf).map g) s)) =
    SheafOfModules.sectionsMap g (modulePushforwardSectionsEquiv B (Spec (.of A)) hA f N
      (SheafOfModules.sectionsMap ((modulePushforwardChartIso B (Spec (.of A)) hA f hf).app N).inv
        s))
  have hn : (chartPushforwardModules f hf).map g ≫
      ((modulePushforwardChartIso B (Spec (.of A)) hA f hf).app N').inv =
      ((modulePushforwardChartIso B (Spec (.of A)) hA f hf).app N).inv ≫
        (modulePushforward B (Spec (.of A)) hA f).map g :=
    (modulePushforwardChartIso B (Spec (.of A)) hA f hf).inv.naturality g
  rw [← SheafOfModules.sectionsMap_comp, hn, SheafOfModules.sectionsMap_comp,
    modulePushforwardSectionsEquiv_naturality]

end Sections

/-! ### The ideal-power submodules along an affine representable morphism -/

section IdealPower

variable {X Y : AlgebraicSpaces B (Spec (.of A)) hA} (f : Y ⟶ X)
  (hf : yoneda.relativelyRepresentable f.hom) (I : Ideal A)

/-- Over an *affine* étale chart `U` of `X`, a section of `(I 𝒪_Y) ^ k G` over `U ×_X Y` is a
section of `(I 𝒪_X) ^ k` of the direct image of `G` over `U`, for an affine representable
morphism `Y ⟶ X` and a quasi-coherent `G`. -/
theorem mem_idealPowerMultiple_smallBaseChangeModulePushforward_of_isAffine
    (haff : IsAffineHom B (Spec (.of A)) hA f.hom)
    (G : Modules.{u, u} B (Spec (.of A)) hA Y.1 Y.2) (hG : G.IsQuasicoherentOnSite) (k : ℕ)
    (U : SmallEtale B (Spec (.of A)) hA X.1)
    (hU : IsAffine ((SmallEtale.toOver B (Spec (.of A)) hA X.1 ⋙
      BigFppfOver.toScheme B (Spec (.of A)) hA).obj U))
    (y : G.val.obj (op ((smallBaseChange B (Spec (.of A)) hA f hf).obj U)))
    (hy : y ∈ (idealPowerMultiple B (Spec (.of A)) hA Y.1 Y.2 (baseIdealSheaf A Y I) k G).obj
      (op ((smallBaseChange B (Spec (.of A)) hA f hf).obj U))) :
    (show ((chartPushforwardModules f hf).obj G).val.obj
        (op U) from y) ∈
      (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) k
        ((chartPushforwardModules f hf).obj G)).obj (op U) := by
  have hU' := isAffine_smallBaseChange_obj B (Spec (.of A)) hA f hf haff U hU
  rw [idealPowerMultiple_eq_idealPowSubmodule] at hy
  have h1 := chartSubmodule_idealPowSubmodule_le_pow_chartSectionIdeal_smul_top B (Spec (.of A))
    hA Y.1 Y.2 (baseIdealSheaf A Y I) k G
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B (Spec (.of A)) hA Y.1 Y.2 G hG)
    (isCartesianOnAffineCharts_baseIdealSheaf A Y I) ((smallBaseChange B (Spec (.of A)) hA f
        hf).obj U) hU' hy
  have hI : chartSectionIdeal B (Spec (.of A)) hA Y.1 Y.2 (baseIdealSheaf A Y I) ((smallBaseChange
      B (Spec (.of A)) hA f hf).obj U) =
      Ideal.map (chartBaseRingHom A Y ((smallBaseChange B (Spec (.of A)) hA f hf).obj U)) I :=
    baseIdealSheaf_obj_of_isAffine A Y I ((smallBaseChange B (Spec (.of A)) hA f hf).obj U) hU'
  have hI' : chartSectionIdeal B (Spec (.of A)) hA Y.1 Y.2 (baseIdealSheaf A Y I)
      ((smallBaseChange B (Spec (.of A)) hA f hf).obj U) ^ k =
      Ideal.map (show A →+* chartRing B (Spec (.of A)) hA Y.1 Y.2 ((smallBaseChange B (Spec (.of
          A)) hA f hf).obj U) from chartBaseRingHom A Y ((smallBaseChange B (Spec (.of A)) hA f
          hf).obj U))
        (I ^ k) := by
    rw [hI]
    exact (Ideal.map_pow _ I k).symm
  rw [hI'] at h1
  let PG := (chartPushforwardModules f hf).obj G
  let PX := (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) k PG).obj
    (op U)
  let T : Ideal (chartRing B (Spec (.of A)) hA Y.1 Y.2 ((smallBaseChange B (Spec (.of A)) hA f
      hf).obj U)) :=
    { carrier := {r | ∀ x : G.val.obj (op ((smallBaseChange B (Spec (.of A)) hA f hf).obj U)),
        (show PG.val.obj (op U) from r • x) ∈ PX}
      add_mem' := fun {r r'} hr hr' x => by
        have e : (r + r') • x = r • x + r' • x := add_smul r r' x
        show (show PG.val.obj (op U) from (r + r') • x) ∈ PX
        rw [e]
        exact PX.add_mem (hr x) (hr' x)
      zero_mem' := fun x => by
        show (show PG.val.obj (op U) from (0 : chartRing B (Spec (.of A)) hA Y.1 Y.2
            ((smallBaseChange B (Spec (.of A)) hA f hf).obj U)) • x) ∈ PX
        rw [zero_smul]
        exact PX.zero_mem
      smul_mem' := fun b r hr x => by
        have e : (b • r) • x = r • (b • x) := by
          rw [smul_eq_mul, mul_comm, mul_smul]
        show (show PG.val.obj (op U) from (b • r) • x) ∈ PX
        rw [e]
        exact hr (b • x) }
  have hT : Ideal.map (show A →+* chartRing B (Spec (.of A)) hA Y.1 Y.2 ((smallBaseChange B (Spec
      (.of A)) hA f hf).obj U) from chartBaseRingHom A Y ((smallBaseChange B (Spec (.of A)) hA f
      hf).obj U)) (I ^ k) ≤ T := by
    refine Ideal.map_le_iff_le_comap.2 fun a ha x => ?_
    have hχ : (show chartRing B (Spec (.of A)) hA X.1 X.2 U from chartBaseRingHom A X U a) ∈
        chartIdeal B (Spec (.of A)) hA X (baseIdealSheaf A X I) U ^ k := by
      have h2 : Ideal.map (chartBaseRingHom A X U) (I ^ k) ≤
          chartIdeal B (Spec (.of A)) hA X (baseIdealSheaf A X I) U ^ k := by
        rw [Ideal.map_pow]
        exact Ideal.pow_right_mono (le_baseIdealSheaf A X I U) k
      exact h2 (Ideal.mem_map_of_mem _ ha)
    have hmem := le_idealPowerMultiple_obj B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) k
      PG U (Submodule.smul_mem_smul hχ (Submodule.mem_top (x := (show PG.val.obj (op U) from x))))
    have e : chartIdealPullbackHom B (Spec (.of A)) hA f hf U (chartBaseRingHom A X U a) =
        chartBaseRingHom A Y ((smallBaseChange B (Spec (.of A)) hA f hf).obj U) a :=
            chartIdealPullbackHom_chartBaseRingHom A f hf U a
    show (show PG.val.obj (op U) from
      (show chartRing B (Spec (.of A)) hA Y.1 Y.2 ((smallBaseChange B (Spec (.of A)) hA f hf).obj
          U) from
        chartBaseRingHom A Y ((smallBaseChange B (Spec (.of A)) hA f hf).obj U) a) • x) ∈ PX
    rw [← e]
    exact hmem
  refine Submodule.smul_induction_on (p := fun (z : G.val.obj (op ((smallBaseChange B (Spec (.of
      A)) hA f hf).obj U))) => (show PG.val.obj (op U) from z) ∈ PX) h1
    (fun r hr x _ => hT hr x) (fun z z' hz hz' => PX.add_mem hz hz')

/-- A section of `(I 𝒪_Y) ^ k G` over the base change of any étale chart `U` of `X` is a section
of `(I 𝒪_X) ^ k` of the direct image of `G` over `U`: membership is local, and over the affine
charts it is `mem_idealPowerMultiple_smallBaseChangeModulePushforward_of_isAffine`. -/
theorem mem_idealPowerMultiple_smallBaseChangeModulePushforward
    (haff : IsAffineHom B (Spec (.of A)) hA f.hom)
    (G : Modules.{u, u} B (Spec (.of A)) hA Y.1 Y.2) (hG : G.IsQuasicoherentOnSite) (k : ℕ)
    (U : SmallEtale B (Spec (.of A)) hA X.1)
    (y : G.val.obj (op ((smallBaseChange B (Spec (.of A)) hA f hf).obj U)))
    (hy : y ∈ (idealPowerMultiple B (Spec (.of A)) hA Y.1 Y.2 (baseIdealSheaf A Y I) k G).obj
      (op ((smallBaseChange B (Spec (.of A)) hA f hf).obj U))) :
    (show ((chartPushforwardModules f hf).obj G).val.obj
        (op U) from y) ∈
      (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) k
        ((chartPushforwardModules f hf).obj G)).obj (op U) := by
  obtain ⟨Uc, hUc⟩ := exists_isSurjective_chart B (Spec (.of A)) hA X
  refine (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) k
    ((chartPushforwardModules f hf).obj G)).isSheaf
    (X := op U) _ ?_
  refine sieve_mem_of_forall_isAffine_hom B (Spec (.of A)) hA X Uc hUc U _ fun V hV _ g => ?_
  exact mem_idealPowerMultiple_smallBaseChangeModulePushforward_of_isAffine f hf I haff G hG k V
    hV _ ((idealPowerMultiple B (Spec (.of A)) hA Y.1 Y.2 (baseIdealSheaf A Y I) k G).map
      ((smallBaseChange B (Spec (.of A)) hA f hf).map g).op hy)

end IdealPower

/-! ### The comparison of the ideal-power quotients -/

section Quotient

variable {X Y : AlgebraicSpaces B (Spec (.of A)) hA} (f : Y ⟶ X)
  (hf : yoneda.relativelyRepresentable f.hom) (I : Ideal A)
  (G : Modules.{u, u} B (Spec (.of A)) hA Y.1 Y.2)

/-- The subsheaf `(I 𝒪_X) ^ k f_* G` of `f_* G` is killed by the direct image of the projection
`G ⟶ G / (I 𝒪_Y) ^ k G`. -/
theorem idealPowerSubsheaf_ι_comp_smallBaseChangeModulePushforward_map_eq_zero (k : ℕ) :
    (idealPowerSubsheaf B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) k
        ((chartPushforwardModules f hf).obj G)).ι ≫
      (chartPushforwardModules f hf).map
        (smallEtaleAdicQuotientProjection B (Spec (.of A)) hA Y.1 Y.2 (baseIdealSheaf A Y I) k G) =
      0 :=
  idealPowerMultiple_ι_comp_eq_zero_of_eq_bot B (Spec (.of A)) hA X.1 X.2 _ k _
    ((idealPowerMultiple_eq_bot_iff B (Spec (.of A)) hA X.1 X.2 _ k _).2
      (isPowAnnihilated_smallBaseChangeModulePushforward A f hf I k _
        (isPowAnnihilated_idealPowerQuotient B (Spec (.of A)) hA Y.1 Y.2 _ k G)))

/-- The comparison `f_* G / (I 𝒪_X) ^ k f_* G ⟶ f_* (G / (I 𝒪_Y) ^ k G)`. -/
def smallBaseChangeAdicQuotientComparison (k : ℕ) :
    smallEtaleAdicQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) k
        ((chartPushforwardModules f hf).obj G) ⟶
      (chartPushforwardModules f hf).obj
        (smallEtaleAdicQuotient B (Spec (.of A)) hA Y.1 Y.2 (baseIdealSheaf A Y I) k G) :=
  cokernel.desc _ _ (idealPowerSubsheaf_ι_comp_smallBaseChangeModulePushforward_map_eq_zero f hf I
      G k)

/-- The projection `f_* G ⟶ f_* G / (I 𝒪_X) ^ k f_* G` followed by the comparison
`AlgebraicGeometry.Space.smallBaseChangeAdicQuotientComparison` is the direct image of the
projection `G ⟶ G / (I 𝒪_Y) ^ k G`. -/
@[reassoc (attr := simp)]
theorem smallEtaleAdicQuotientProjection_comp_smallBaseChangeAdicQuotientComparison (k : ℕ) :
    smallEtaleAdicQuotientProjection B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) k
        ((chartPushforwardModules f hf).obj G) ≫
      smallBaseChangeAdicQuotientComparison f hf I G k =
    (chartPushforwardModules f hf).map
      (smallEtaleAdicQuotientProjection B (Spec (.of A)) hA Y.1 Y.2 (baseIdealSheaf A Y I) k G) :=
  cokernel.π_desc _ _ _

/-- The comparisons `AlgebraicGeometry.Space.smallBaseChangeAdicQuotientComparison` commute with
the transition maps of the two systems of ideal-power quotients. -/
theorem smallEtaleAdicQuotientTransition_comp_smallBaseChangeAdicQuotientComparison (k : ℕ) :
    smallEtaleAdicQuotientTransition B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) k
        ((chartPushforwardModules f hf).obj G) ≫
      smallBaseChangeAdicQuotientComparison f hf I G k =
    smallBaseChangeAdicQuotientComparison f hf I G (k + 1) ≫
      (chartPushforwardModules f hf).map
        (smallEtaleAdicQuotientTransition B (Spec (.of A)) hA Y.1 Y.2 (baseIdealSheaf A Y I) k
          G) := by
  refine (cancel_epi (smallEtaleAdicQuotientProjection B (Spec (.of A)) hA X.1 X.2
    (baseIdealSheaf A X I) (k + 1)
    ((chartPushforwardModules f hf).obj G))).mp ?_
  rw [← Category.assoc, smallEtaleAdicQuotientProjection_comp_transition,
    smallEtaleAdicQuotientProjection_comp_smallBaseChangeAdicQuotientComparison,
    smallEtaleAdicQuotientProjection_comp_smallBaseChangeAdicQuotientComparison_assoc,
    ← Functor.map_comp, smallEtaleAdicQuotientProjection_comp_transition]

/-- **The comparison of the ideal-power quotients is an isomorphism**, for an affine
representable morphism whose base-change direct image preserves finite colimits and a
quasi-coherent `G`. -/
theorem isIso_smallBaseChangeAdicQuotientComparison
    (haff : IsAffineHom B (Spec (.of A)) hA f.hom)
    [PreservesFiniteColimits (chartPushforwardModules f hf)]
    (hG : G.IsQuasicoherentOnSite) (k : ℕ) :
    IsIso (smallBaseChangeAdicQuotientComparison f hf I G k) := by
  let P := chartPushforwardModules f hf
  let PZ := idealPowerSubsheaf B (Spec (.of A)) hA Y.1 Y.2 (baseIdealSheaf A Y I) k G
  let PX := idealPowerSubsheaf B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) k (P.obj G)
  have := modulePushforward_additive B (Spec (.of A)) hA f
  have : P.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_iso (modulePushforwardChartIso B (Spec (.of A)) hA f hf)
  let l := isColimitOfHasCokernelOfPreservesColimit P PZ.ι
  have hz := idealPowerSubsheaf_ι_comp_smallBaseChangeModulePushforward_map_eq_zero f hf I G k
  have hkill : ∀ {T : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2} (g : P.obj G ⟶ T),
      PX.ι ≫ g = 0 → P.map PZ.ι ≫ g = 0 := by
    intro T g hg
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
      ModuleCat.hom_ext (LinearMap.ext fun y => ?_))
    have hy := mem_idealPowerMultiple_smallBaseChangeModulePushforward f hf I haff G hG k U.unop
      y.1 y.2
    exact congrArg (fun φ : PX.toSheafOfModules ⟶ T => φ.val.app U ⟨_, hy⟩) hg
  let hcolim : IsColimit (CokernelCofork.ofπ _ hz) :=
    CokernelCofork.IsColimit.ofπ _ _
      (fun g hg => l.desc (CokernelCofork.ofπ g (hkill g hg)))
      (fun g hg => l.fac (CokernelCofork.ofπ g (hkill g hg)) WalkingParallelPair.one)
      (fun g hg m hm => Cofork.IsColimit.hom_ext l (by
        rw [Cofork.IsColimit.π_desc]
        exact hm))
  exact (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel PX.ι) hcolim).isIso_hom

end Quotient

/-! ### Transport of the theorem on formal functions in degree zero -/

section Transport

variable {X Y : AlgebraicSpaces B (Spec (.of A)) hA} (f : Y ⟶ X)
  (hf : yoneda.relativelyRepresentable f.hom) (I : Ideal A)
  (G : Modules.{u, u} B (Spec (.of A)) hA Y.1 Y.2)

/-- **Degree-zero formal functions pass to the base-change direct image** along an affine
representable morphism whose base-change direct image preserves finite colimits. -/
theorem bijective_adicSectionsOfSections_smallBaseChangeModulePushforward
    (haff : IsAffineHom B (Spec (.of A)) hA f.hom)
    [PreservesFiniteColimits (chartPushforwardModules f hf)]
    (hG : G.IsQuasicoherentOnSite)
    (h : Function.Bijective
      (adicSectionsOfSections B (Spec (.of A)) hA Y.1 Y.2 (baseIdealSheaf A Y I) G)) :
    Function.Bijective
      (adicSectionsOfSections B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I)
        ((chartPushforwardModules f hf).obj G)) := by
  let P := chartPushforwardModules f hf
  let c := fun n : ℕ => smallBaseChangeAdicQuotientComparison f hf I G (n + 1)
  have hc : ∀ n, IsIso (c n) := fun n =>
    isIso_smallBaseChangeAdicQuotientComparison f hf I G haff hG (n + 1)
  let E := smallBaseChangeSectionsEquiv f hf
  let Φ : adicSections B (Spec (.of A)) hA X.1 X.2
      (fun n => smallEtaleAdicQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) (n + 1)
        (P.obj G))
      (fun n => smallEtaleAdicQuotientTransition B (Spec (.of A)) hA X.1 X.2
        (baseIdealSheaf A X I) (n + 1) (P.obj G)) →
      adicSections B (Spec (.of A)) hA Y.1 Y.2
        (fun n => smallEtaleAdicQuotient B (Spec (.of A)) hA Y.1 Y.2 (baseIdealSheaf A Y I)
          (n + 1) G)
        (fun n => smallEtaleAdicQuotientTransition B (Spec (.of A)) hA Y.1 Y.2
          (baseIdealSheaf A Y I) (n + 1) G) :=
    fun s => ⟨fun n => E _ (SheafOfModules.sectionsMap (c n) (s.1 n)), fun n => by
      dsimp only
      rw [← smallBaseChangeSectionsEquiv_sectionsMap, ← SheafOfModules.sectionsMap_comp,
        ← smallEtaleAdicQuotientTransition_comp_smallBaseChangeAdicQuotientComparison,
        SheafOfModules.sectionsMap_comp, s.2 n]⟩
  have hΦ : Function.Injective Φ := by
    intro s s' hss
    refine Subtype.ext (funext fun n => ?_)
    have h1 := congrArg (fun t => t.1 n) hss
    have h2 := (E _).injective h1
    exact (sectionsEquivOfIso (asIso (c n))).injective h2
  have hsq : ∀ σ, Φ (adicSectionsOfSections B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I)
      (P.obj G) σ) =
      adicSectionsOfSections B (Spec (.of A)) hA Y.1 Y.2 (baseIdealSheaf A Y I) G (E G σ) := by
    intro σ
    refine Subtype.ext (funext fun n => ?_)
    show E _ (SheafOfModules.sectionsMap (c n) (SheafOfModules.sectionsMap _ σ)) =
      SheafOfModules.sectionsMap _ (E G σ)
    rw [← SheafOfModules.sectionsMap_comp,
      smallEtaleAdicQuotientProjection_comp_smallBaseChangeAdicQuotientComparison,
      smallBaseChangeSectionsEquiv_sectionsMap]
  refine ⟨fun σ σ' hσσ => ?_, fun t => ?_⟩
  · have := congrArg Φ hσσ
    rw [hsq, hsq] at this
    exact (E G).injective (h.1 this)
  · obtain ⟨τ, hτ⟩ := h.2 (Φ t)
    refine ⟨(E G).symm τ, hΦ ?_⟩
    rw [hsq, Equiv.apply_symm_apply, hτ]

/-- **Degree-zero formal functions pass to the direct image along a closed immersion.**  Let
`f : Y ⟶ X` be a closed immersion of algebraic spaces over `Spec A` and `G` a quasi-coherent
`𝒪_Y`-module.  If `H⁰(Y, G) ⟶ limₙ H⁰(Y, G / (I 𝒪_Y) ^ (n + 1) G)` is bijective, then so is
`H⁰(X, f_* G) ⟶ limₙ H⁰(X, f_* G / (I 𝒪_X) ^ (n + 1) f_* G)`. -/
theorem bijective_adicSectionsOfSections_modulePushforward_of_isClosedImmersion
    (hi : IsClosedImmersion B (Spec (.of A)) hA f.hom) (hG : G.IsQuasicoherentOnSite)
    (h : Function.Bijective
      (adicSectionsOfSections B (Spec (.of A)) hA Y.1 Y.2 (baseIdealSheaf A Y I) G)) :
    Function.Bijective
      (adicSectionsOfSections B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I)
        ((modulePushforward B (Spec (.of A)) hA f).obj G)) := by
  have hpres := preservesFiniteColimits_modulePushforward_of_isClosedImmersion B (Spec (.of A))
    hA f hi
  have : PreservesFiniteColimits
      (chartPushforwardModules f hi.rep) :=
    preservesFiniteColimits_of_natIso (modulePushforwardChartIso B (Spec (.of A)) hA f hi.rep)
  exact bijective_adicSectionsOfSections_of_iso B (Spec (.of A)) hA X.1 X.2 _
    ((modulePushforwardChartIso B (Spec (.of A)) hA f hi.rep).app G).symm
    (bijective_adicSectionsOfSections_smallBaseChangeModulePushforward f hi.rep I G
      (isAffineHom_of_isClosedImmersion B (Spec (.of A)) hA f.hom hi) hG h)

/-- **Degree-zero formal functions pass from a closed subspace to the ambient space**, in the
shape of clause (3) of Stacks 0CZI (`AlgebraicGeometry.Space.hasProperSupport_tfae`). -/
theorem bijective_adicSectionsOfSections_closedSubspacePushforward
    (X : AlgebraicSpaces B (Spec (.of A)) hA) (Zc : ClosedSubspaces B (Spec (.of A)) hA X.1)
    (I : Ideal A)
    (G : Modules.{u, u} B (Spec (.of A)) hA (closedSubspaceToSpace B (Spec (.of A)) hA X Zc).1
      (closedSubspaceToSpace B (Spec (.of A)) hA X Zc).2)
    (hG : G.IsQuasicoherentOnSite)
    (h : Function.Bijective
      (adicSectionsOfSections B (Spec (.of A)) hA
        (closedSubspaceToSpace B (Spec (.of A)) hA X Zc).1
        (closedSubspaceToSpace B (Spec (.of A)) hA X Zc).2
        (baseIdealSheaf A (closedSubspaceToSpace B (Spec (.of A)) hA X Zc) I) G)) :
    Function.Bijective
      (adicSectionsOfSections B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I)
        ((modulePushforward B (Spec (.of A)) hA
          (closedSubspaceInclusion B (Spec (.of A)) hA X Zc)).obj G)) :=
  bijective_adicSectionsOfSections_modulePushforward_of_isClosedImmersion
    (closedSubspaceInclusion B (Spec (.of A)) hA X Zc) I G Zc.2.2 hG h

end Transport

end AlgebraicGeometry.Space

end
