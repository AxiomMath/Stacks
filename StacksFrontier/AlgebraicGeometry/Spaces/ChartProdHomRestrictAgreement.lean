module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartHomRestrSliceBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPushTransitionNaturality

/-!
# The two chart-scheme preimages of the kernel-pair relocalizations agree over the complement

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B`, let `ℐ ⊆ 𝒪_X` be a sheaf
of ideals which is cartesian on affine charts, let `U = X ∖ V(ℐ)`, let `𝒢` be coherent and `ℱ`
quasi-coherent, let `θ : 𝒢|_U ⟶ ℱ|_U` and let `A` be an étale scheme chart of `X`.  Write
`α : (ℐᵏ𝒢)|_A ⟶ ℱ|_A` for the chart transport `AlgebraicGeometry.Space.chartAlphaSheaf` of `θ`.

The descent from the chart needs the two relocalizations of `α` to the kernel pair `A ⨯ A` to
agree, and `AlgebraicGeometry.Space.homRestr_openChartInclusion_homRestr_prod_eq` gives that
agreement only over the complement of the support of the chartwise sheaf of ideals.  **This file
turns that into the statement on the chart's scheme** which the injectivity clause of
[Stacks, Tag 01YB] consumes: the two morphisms on the scheme of `A ⨯ A` whose chart transports are
the two relocalizations have the same restriction to the complement of the support.

Nothing here raises the exponent of the ideal; that is the next step, and it is what turns the
agreement after restriction into an agreement over the whole kernel pair.

## Main results

* `Stacks.PresheafOfModules.homRestr_restrFun_map_comp`: **relocalization is functorial in the
  module** — relocalizing a morphism precomposed with the restriction of `u : M ⟶ M'` is
  precomposing the relocalization with the restriction of `u`.  By `rfl`, and stated generically.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.homRestrict_eq_of_forall_app`: two morphisms out of
  `Iⁿ G` on a scheme have the same restriction to the complement of the support of `I` as soon as
  their components over the Zariski opens contained in that complement agree.  This is
  `Stacks.AlgebraicGeometry.IdealPowerColimit.val_homRestrict_app` read backwards, and it is
  scheme-generic: no chart datum occurs.
* `AlgebraicGeometry.Space.surjective_idealPowModuleι_val_app_of_pc_eq`: **the inclusion
  `ℐᵏ𝒢 ⟶ 𝒢` is surjective on the sections over a chart of `X` lying over `U`**, because there the
  unit ideal already generates.
* `AlgebraicGeometry.Space.exists_chartPushFactor_val_app_eq`: consequently every section of `Iᵏ`
  times the chart restriction of `𝒢` over a Zariski open off the support comes from a section of
  the chart restriction of `ℐᵏ𝒢`.
* `AlgebraicGeometry.Space.chartAlphaSheaf_val_app_eq_of_val_eq_homRestr_prod`: **the two
  relocalizations of the chart transport to the kernel pair have the same component at the object
  of the slice which a Zariski open off the support cuts out.**  Both components are the
  transport of `θ` at one and the same chart of `U`, by the component determination at `A`.
* `AlgebraicGeometry.Space.homRestrict_eq_of_chartAlphaSheaf_val_eq_homRestr_prod`: **the
  statement on the chart's scheme.**

## Implementation notes

**The relocalization is never wrapped as a morphism of sheaves.**  A morphism of the slice
restrictions of two sheaves of modules has an underlying morphism of the `restrFun` restrictions
with no transport, so `AlgebraicGeometry.Space.homRestr` of it is again such a morphism and
`CategoryTheory.SheafOfModules.Hom.mk` of that typechecks.  But the resulting definition cannot
have its `val` field *projected*: the `rfl` which says that the projection is the
relocalization again exhausts the heartbeat budget, as does every statement about a component of
the wrapped morphism.  The hypotheses of
`AlgebraicGeometry.Space.homRestrict_eq_of_chartAlphaSheaf_val_eq_homRestr_prod` are therefore
equations between the `val` fields, which is the form a consumer obtains from
`CategoryTheory.SheafOfModules.forget`'s fullness anyway, and no sheaf-level relocalization is
defined here.

**The ambient module is spelled `AlgebraicGeometry.Space.asStructureSheafModule`.**  At the
spelling `AlgebraicGeometry.Space.Modules` instance search does not find the category structure of
the slice at a chart, so the component of a morphism of the slice restrictions cannot be written
down; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartComponentDetermination.lean`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.PresheafOfModules

universe v₁ u₁ t₁

variable {C : Type u₁} [Category.{v₁} C] (O : Cᵒᵖ ⥤ CommRingCat)

/-- **Relocalization is functorial in the module.**  Relocalizing along `f : V ⟶ U` a morphism
which is precomposed with the restriction to the slice at `U` of `u : M ⟶ M'` is precomposing the
relocalization with the restriction to the slice at `V` of `u`.

This holds by `rfl` — the restriction of a presheaf of modules to a slice has, over an object of
that slice, the sections of the module over its source — and it is stated generically: at a chart
the two slices carry the chart data and nothing of the statement does. -/
theorem homRestr_restrFun_map_comp (M M' N : _root_.PresheafOfModules.{t₁} (Oforget O))
    (u : M ⟶ M') {V U : C} (f : V ⟶ U)
    (α : (restrFun O U).obj M' ⟶ (restrFun O U).obj N) :
    homRestr O M N f ((restrFun O U).map u ≫ α) =
      (restrFun O V).map u ≫ homRestr O M' N f α := rfl

/-- **Two relocalizations of one morphism have the same component at an object of the slice as
soon as the morphism itself has the same component at the two images of that object.**

This is `Stacks.PresheafOfModules.homRestr_app_apply` twice.  Stated generically, with the two
modules, the morphism, the two indices, the object of the slice and the section all variables:
the ring over which the component is linear is reached here without unfolding any chart datum,
and a version whose modules are the chart data does not elaborate inside the
heartbeat budget, in any of the evident spellings. -/
theorem homRestr_app_eq_of_app_apply_eq (M N : _root_.PresheafOfModules.{t₁} (Oforget O))
    {V U : C} (p q : V ⟶ U) (α : (restrFun O U).obj M ⟶ (restrFun O U).obj N) (Z : (Over V)ᵒᵖ)
    (x : ((restrFun O V).obj M).obj Z)
    (h : (α.app (op (Over.mk (Z.unop.hom ≫ p)))).hom x =
      (α.app (op (Over.mk (Z.unop.hom ≫ q)))).hom x) :
    ((homRestr O M N p α).app Z).hom x = ((homRestr O M N q α).app Z).hom x :=
  (homRestr_app_apply O M N p α Z x).trans
    (h.trans (homRestr_app_apply O M N q α Z x).symm)

end Stacks.PresheafOfModules

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

universe u₂

variable {Y : _root_.AlgebraicGeometry.Scheme.{u₂}}

/-- **Two morphisms out of `Iⁿ G` restrict equally to the complement of the support of `I` as
soon as their components over the Zariski opens inside that complement agree.**

This is `Stacks.AlgebraicGeometry.IdealPowerColimit.val_homRestrict_app` read backwards: the
component of `homRestrict` over an open of the slice site is the component of the morphism at the
same open, applied to a section of `G` viewed as a section of `Iⁿ G`.  It is scheme-generic — no
chart datum occurs — so its instantiation at a chart is first-order. -/
theorem homRestrict_eq_of_forall_app (I : Y.IdealSheafData) {G F : Y.Modules} {n : ℕ}
    (ψ₁ ψ₂ : idealPowSmul I n G ⟶ F)
    (h : ∀ V : Y.Opens, V ≤ (I.support.compl : Y.Opens) →
      ∀ x : Γ(idealPowSmul I n G, V), ψ₁.app V x = ψ₂.app V x) :
    homRestrict I (disjoint_supportCompl_support I) ψ₁ =
      homRestrict I (disjoint_supportCompl_support I) ψ₂ :=
  Stacks.SheafOfModules.hom_ext_val_app_apply fun Z g =>
    (val_homRestrict_app I (disjoint_supportCompl_support I) ψ₁ Z g).trans
      ((h Z.unop.left (leOfHom Z.unop.hom) _).trans
        (val_homRestrict_app I (disjoint_supportCompl_support I) ψ₂ Z g).symm)

end Stacks.AlgebraicGeometry.IdealPowerColimit

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### The inclusion `ℐᵏ𝒢 ⟶ 𝒢` over a chart of the open complement -/

variable (I : IdealSheaves B S hS X.1 X.2)

/-- **The inclusion `ℐᵏ𝒢 ⟶ 𝒢` is surjective on the sections over an étale chart of `X` lying
over `U = X ∖ V(ℐ)`.**  Off the zero locus of `ℐ` the unit ideal already generates, so there
`ℐᵏ𝒢` is all of `𝒢`: this is `AlgebraicGeometry.Space.mem_idealPowSubmodule_pc`. -/
theorem surjective_idealPowModuleι_val_app_of_pc_eq (G : Modules.{u, u} B S hS X.1 X.2) (k : ℕ)
    {P : SmallEtale B S hS (idealComplement B S hS X I).1} {Q : SmallEtale B S hS X.1}
    (hP : pc B S hS X I P = Q) :
    Function.Surjective ((idealPowModuleι I k G).val.app (op Q)).hom := by
  subst hP
  exact fun z => ⟨⟨z, mem_idealPowSubmodule_pc B S hS X I k G P z⟩, rfl⟩

variable (hIc : IsCartesianOnAffineCharts I.toSheafOfModules)
    (G F : Modules.{u, u} B S hS X.1 X.2)

/-- The chart of `U = X ∖ V(ℐ)` cut out by a Zariski open off the support lies over the open chart
of `X` which the open cuts out. -/
private theorem pc_idealComplementChart_eq_openChartOfComparison (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens)
    (hV : V ≤ ((idealSheafDataOfChart B S hS X I hIc A).support.compl : (chartScheme A).Opens)) :
    pc B S hS X I (idealComplementChart B S hS X I hIc A V hV) =
      openChartOfComparison B S hS X A V :=
  (pc_idealComplementChart B S hS X I hIc A V hV).trans
    (openChart_eq_chartLocalization_opensObj B S hS X A V).symm

/-- **Every section of `Iᵏ` times the chart restriction of `𝒢` over a Zariski open off the
support of the chartwise sheaf of ideals comes from a section of the chart restriction of
`ℐᵏ𝒢`.** -/
theorem exists_chartPushFactor_val_app_eq
    (hIq : I.toSheafOfModules.IsQuasicoherentOnSite) (hGq : G.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) (k : ℕ) (V : (chartScheme A).Opens)
    (hV : V ≤ ((idealSheafDataOfChart B S hS X I hIc A).support.compl : (chartScheme A).Opens))
    (x : Γ(Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A), V)) :
    ∃ y : (chartPush B S hS X (idealPowModule I k G) A).val.obj (op V),
      ((chartPushFactor B S hS X I hIc G hIq hGq A k).val.app (op V)).hom y = x := by
  obtain ⟨w, hw⟩ := surjective_idealPowModuleι_val_app_of_pc_eq B S hS X I G k
    (pc_idealComplementChart_eq_openChartOfComparison B S hS X I hIc A V hV)
    (chartPushEquiv B S hS X G A V x.1)
  obtain ⟨y, hy⟩ := (chartPushEquiv B S hS X (idealPowModule I k G) A V).surjective w
  refine ⟨y, (chartPushFactor_val_app_apply B S hS X I hIc G hIq hGq A k V y).trans
    (Subtype.ext ?_)⟩
  refine (chartPushEquiv B S hS X G A V).injective ?_
  refine (chartPushEquiv_chartPushι_apply B S hS X I G A k V y).trans ?_
  exact (congrArg (fun z : (idealPowModule I k G).val.obj
      (op (openChartOfComparison B S hS X A V)) =>
    ((idealPowModuleι I k G).val.app (op (openChartOfComparison B S hS X A V))).hom z) hy).trans
    hw

/-! ### The two relocalizations to the kernel pair, at a Zariski open off the support -/

variable (θ : (restrictToIdealComplement B S hS X I).obj G ⟶
    (restrictToIdealComplement B S hS X I).obj F)
    (hZt : B.Contains (⊤_ Scheme.{u})) (hNo : IsNoetherian B S hS hZt X.1)
    (hIq : I.toSheafOfModules.IsQuasicoherentOnSite) (hFq : F.IsQuasicoherentOnSite)
    (hG : IsCoherent B S hS X.1 X.2 G) (A : SmallEtale B S hS X.1) (k : ℕ)

/-- **The chart transport of `θ` has the same component at the two images in the slice at `A` of
the object which a Zariski open of the scheme of the kernel pair cuts out**, provided the open
misses the support of the chartwise sheaf of ideals.

The chart which such an open cuts out lies over `U = X ∖ V(ℐ)`
(`AlgebraicGeometry.Space.pc_idealComplementChart`), so the component determination
`AlgebraicGeometry.Space.chartAlphaSheaf_val_app_eq_homOnChart_of_homRestrict` evaluates the
component at either image to the transport of `θ` at that one chart of `U`.  Nothing about the
two projections is used.

This is stated at the two images themselves rather than at the relocalizations, so that no
component of a relocalization at the chart data has to be written down; see the implementation
notes. -/
theorem chartAlphaSheaf_val_app_over_mk_prod_eq
    (φ : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A) ⟶
      chartPush B S hS X F A)
    (hφ : Stacks.AlgebraicGeometry.IdealPowerColimit.homRestrict
        (idealSheafDataOfChart B S hS X I hIc A)
        (Stacks.AlgebraicGeometry.IdealPowerColimit.disjoint_supportCompl_support
          (idealSheafDataOfChart B S hS X I hIc A)) φ =
      chartThetaOver B S hS X I hIc G F θ A)
    (V : (chartScheme (A ⨯ A : SmallEtale B S hS X.1)).Opens)
    (hV : V ≤ ((idealSheafDataOfChart B S hS X I hIc (A ⨯ A)).support.compl :
      (chartScheme (A ⨯ A : SmallEtale B S hS X.1)).Opens))
    (x : (idealPowModule I k G).val.obj
      (op (openChartOfComparisonOver B S hS X (A ⨯ A) V).left)) :
    ((chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A k φ).val.app
          (op (Over.mk ((openChartOfComparisonOver B S hS X (A ⨯ A) V).hom ≫
            Limits.prod.fst)))).hom x =
      ((chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A k φ).val.app
        (op (Over.mk ((openChartOfComparisonOver B S hS X (A ⨯ A) V).hom ≫
          Limits.prod.snd)))).hom x :=
  have hpc : pc B S hS X I (idealComplementChart B S hS X I hIc (A ⨯ A) V hV) =
      (openChartOfComparisonOver B S hS X (A ⨯ A) V).left :=
    pc_idealComplementChart_eq_openChartOfComparison B S hS X I hIc (A ⨯ A) V hV
  (chartAlphaSheaf_val_app_eq_homOnChart_of_homRestrict B S hS X I hIc G F θ hZt hNo hIq hFq hG
        A k φ hφ hpc
        ((openChartOfComparisonOver B S hS X (A ⨯ A) V).hom ≫ Limits.prod.fst) x).trans
    (chartAlphaSheaf_val_app_eq_homOnChart_of_homRestrict B S hS X I hIc G F θ hZt hNo hIq hFq
      hG A k φ hφ hpc
      ((openChartOfComparisonOver B S hS X (A ⨯ A) V).hom ≫ Limits.prod.snd) x).symm

/-- **Two morphisms on the scheme of the kernel pair whose chart transports are the two
relocalizations of the chart transport of `θ` have the same component at the object of the slice
which a Zariski open off the support cuts out.**

The two hypotheses rewrite each side into a relocalization — consumed at the level of
*morphisms*, where no component is projected — and
`AlgebraicGeometry.Space.homRestr_val_app_eq_of_val_app_eq` then reduces the claim to
`AlgebraicGeometry.Space.chartAlphaSheaf_val_app_over_mk_prod_eq`. -/
theorem chartAlphaSheaf_val_app_eq_of_val_eq_homRestr_prod
    (φ : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A) ⟶
      chartPush B S hS X F A)
    (hφ : Stacks.AlgebraicGeometry.IdealPowerColimit.homRestrict
        (idealSheafDataOfChart B S hS X I hIc A)
        (Stacks.AlgebraicGeometry.IdealPowerColimit.disjoint_supportCompl_support
          (idealSheafDataOfChart B S hS X I hIc A)) φ =
      chartThetaOver B S hS X I hIc G F θ A)
    (ψ₁ ψ₂ : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc (A ⨯ A)) k
        (chartPush B S hS X G (A ⨯ A)) ⟶ chartPush B S hS X F (A ⨯ A))
    (h₁ : (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG (A ⨯ A) k ψ₁).val =
      homRestr (smallEtaleStructurePresheaf B S hS X.1 X.2) (idealPowModule I k G).val F.val
        (Limits.prod.fst : (A ⨯ A : SmallEtale B S hS X.1) ⟶ A)
        (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A k φ).val)
    (h₂ : (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG (A ⨯ A) k ψ₂).val =
      homRestr (smallEtaleStructurePresheaf B S hS X.1 X.2) (idealPowModule I k G).val F.val
        (Limits.prod.snd : (A ⨯ A : SmallEtale B S hS X.1) ⟶ A)
        (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A k φ).val)
    (V : (chartScheme (A ⨯ A : SmallEtale B S hS X.1)).Opens)
    (hV : V ≤ ((idealSheafDataOfChart B S hS X I hIc (A ⨯ A)).support.compl :
      (chartScheme (A ⨯ A : SmallEtale B S hS X.1)).Opens))
    (x : ((restrFun (smallEtaleStructurePresheaf B S hS X.1 X.2)
        (A ⨯ A : SmallEtale B S hS X.1)).obj (idealPowModule I k G).val).obj
      (op (openChartOfComparisonOver B S hS X (A ⨯ A) V))) :
    ((chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG (A ⨯ A) k ψ₁).val.app
          (op (openChartOfComparisonOver B S hS X (A ⨯ A) V))).hom x =
      ((chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG (A ⨯ A) k ψ₂).val.app
        (op (openChartOfComparisonOver B S hS X (A ⨯ A) V))).hom x := by
  refine Eq.trans (congrArg
    (fun m : (restrFun (smallEtaleStructurePresheaf B S hS X.1 X.2)
          (A ⨯ A : SmallEtale B S hS X.1)).obj (idealPowModule I k G).val ⟶
        (restrFun (smallEtaleStructurePresheaf B S hS X.1 X.2)
          (A ⨯ A : SmallEtale B S hS X.1)).obj F.val =>
      (m.app (op (openChartOfComparisonOver B S hS X (A ⨯ A) V))).hom x) h₁) ?_
  refine Eq.trans ?_ (congrArg
    (fun m : (restrFun (smallEtaleStructurePresheaf B S hS X.1 X.2)
          (A ⨯ A : SmallEtale B S hS X.1)).obj (idealPowModule I k G).val ⟶
        (restrFun (smallEtaleStructurePresheaf B S hS X.1 X.2)
          (A ⨯ A : SmallEtale B S hS X.1)).obj F.val =>
      (m.app (op (openChartOfComparisonOver B S hS X (A ⨯ A) V))).hom x) h₂.symm)
  exact Stacks.PresheafOfModules.homRestr_app_eq_of_app_apply_eq
    (smallEtaleStructurePresheaf B S hS X.1 X.2) (idealPowModule I k G).val F.val
    Limits.prod.fst Limits.prod.snd
    (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A k φ).val
    (op (openChartOfComparisonOver B S hS X (A ⨯ A) V)) x
    (chartAlphaSheaf_val_app_over_mk_prod_eq B S hS X I hIc G F θ hZt hNo hIq hFq hG A k φ hφ
      V hV x)

/-! ### The statement on the scheme of the kernel pair -/

/-- **Two morphisms on the scheme of the kernel pair whose chart transports are the two
relocalizations of the chart transport of `θ` restrict equally to the complement of the support of
the chartwise sheaf of ideals.**

By `Stacks.AlgebraicGeometry.IdealPowerColimit.homRestrict_eq_of_forall_app` it suffices to
compare their components over a Zariski open off the support, and there every section comes from a
section of the chart restriction of `ℐᵏ𝒢`
(`AlgebraicGeometry.Space.exists_chartPushFactor_val_app_eq`).  On such a section the component
is read off the component of the chart transport at the object of the slice which the open cuts
out (`AlgebraicGeometry.Space.chartAlphaSheaf_val_app_openChartOfComparisonOver_apply`), and
there the two relocalizations agree because the chart which the open cuts out lies over
`U = X ∖ V(ℐ)`, so the component determination
`AlgebraicGeometry.Space.chartAlphaSheaf_val_app_eq_homOnChart_of_homRestrict` evaluates the
component of the chart transport at both of its images to the transport of `θ` at that one chart.
Nothing about the two projections is used.

This is the statement the injectivity clause of [Stacks, Tag 01YB] on the scheme of `A ⨯ A`
consumes; raising the exponent of the ideal is what turns it into an agreement over the whole
kernel pair. -/
theorem homRestrict_eq_of_chartAlphaSheaf_val_eq_homRestr_prod
    (φ : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A) ⟶
      chartPush B S hS X F A)
    (hφ : Stacks.AlgebraicGeometry.IdealPowerColimit.homRestrict
        (idealSheafDataOfChart B S hS X I hIc A)
        (Stacks.AlgebraicGeometry.IdealPowerColimit.disjoint_supportCompl_support
          (idealSheafDataOfChart B S hS X I hIc A)) φ =
      chartThetaOver B S hS X I hIc G F θ A)
    (ψ₁ ψ₂ : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc (A ⨯ A)) k
        (chartPush B S hS X G (A ⨯ A)) ⟶ chartPush B S hS X F (A ⨯ A))
    (h₁ : (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG (A ⨯ A) k ψ₁).val =
      homRestr (smallEtaleStructurePresheaf B S hS X.1 X.2) (idealPowModule I k G).val F.val
        (Limits.prod.fst : (A ⨯ A : SmallEtale B S hS X.1) ⟶ A)
        (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A k φ).val)
    (h₂ : (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG (A ⨯ A) k ψ₂).val =
      homRestr (smallEtaleStructurePresheaf B S hS X.1 X.2) (idealPowModule I k G).val F.val
        (Limits.prod.snd : (A ⨯ A : SmallEtale B S hS X.1) ⟶ A)
        (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A k φ).val) :
    Stacks.AlgebraicGeometry.IdealPowerColimit.homRestrict
        (idealSheafDataOfChart B S hS X I hIc (A ⨯ A))
        (Stacks.AlgebraicGeometry.IdealPowerColimit.disjoint_supportCompl_support
          (idealSheafDataOfChart B S hS X I hIc (A ⨯ A))) ψ₁ =
      Stacks.AlgebraicGeometry.IdealPowerColimit.homRestrict
        (idealSheafDataOfChart B S hS X I hIc (A ⨯ A))
        (Stacks.AlgebraicGeometry.IdealPowerColimit.disjoint_supportCompl_support
          (idealSheafDataOfChart B S hS X I hIc (A ⨯ A))) ψ₂ := by
  refine Stacks.AlgebraicGeometry.IdealPowerColimit.homRestrict_eq_of_forall_app
    (idealSheafDataOfChart B S hS X I hIc (A ⨯ A)) ψ₁ ψ₂ fun V hV x => ?_
  obtain ⟨y, rfl⟩ := exists_chartPushFactor_val_app_eq B S hS X I hIc G hIq
    hG.toIsQuasicoherentOnSite (A ⨯ A) k V hV x
  refine (chartPushEquiv B S hS X F (A ⨯ A) V).injective ?_
  refine Eq.trans
    (chartAlphaSheaf_val_app_openChartOfComparisonOver_apply B S hS X I hIc G F hZt hNo hIq hFq
      hG (A ⨯ A) k ψ₁ V y).symm ?_
  refine Eq.trans ?_ (chartAlphaSheaf_val_app_openChartOfComparisonOver_apply B S hS X I hIc G F
    hZt hNo hIq hFq hG (A ⨯ A) k ψ₂ V y)
  exact chartAlphaSheaf_val_app_eq_of_val_eq_homRestr_prod B S hS X I hIc G F θ hZt hNo hIq hFq
    hG A k φ hφ ψ₁ ψ₂ h₁ h₂ V hV _

end AlgebraicGeometry.Space

end
