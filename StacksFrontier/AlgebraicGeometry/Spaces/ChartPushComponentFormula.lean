module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartHomEquivComponent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentHomColimitChartTransport

/-!
# The component formula at the direct-image spelling of a chart restriction

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B`, let `A` be an étale scheme
chart of `X` and let `V` be a Zariski open of the chart's scheme.  The `V`-component of the Hom-set
transport `AlgebraicGeometry.Space.chartSchemeModuleHomEquiv` is computed by
`AlgebraicGeometry.Space.chartSectionsLinearEquiv_chartSchemeModuleHomEquiv_apply`, which reads the
sections of the chart restriction through
`AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule` and
`AlgebraicGeometry.Space.chartSectionsLinearEquiv`.  Everything that applies [Stacks, Tag 01YB] on
the chart's scheme, however, works at the direct-image spelling
`AlgebraicGeometry.Space.chartPush`, whose sections identification is
`AlgebraicGeometry.Space.chartPushEquiv`.  This file identifies the two readings and restates the
component formula at the second.

## Main results

* `AlgebraicGeometry.Space.chartPushEquiv_chartSchemeModuleIsoChartPush_apply`: **the sections
  identification of the direct-image spelling, read after
  `AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush`, is the chart sections identification
  read after `AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule`.**
* `AlgebraicGeometry.Space.chartPushEquiv_chartSchemeModuleHomEquiv_apply` and
  `AlgebraicGeometry.Space.chartPushEquiv_chartSchemeModuleHomEquiv_symm_apply`: **the component
  formula for the Hom-set transport of the chart restriction, read at the direct-image
  spelling.**  The second is the direction in which a morphism produced on the chart's scheme —
  such as the one `AlgebraicGeometry.Space.chartAlpha` carries back from the first display of
  [Stacks, Tag 01YB] — has its components over the Zariski opens of the chart's scheme computed.

## Implementation notes

**The two spellings of the chart restriction are only expensively definitionally equal, and the
cost is paid whenever a projection of a transport along their equality is forced.**  The equality
`AlgebraicGeometry.Space.restrictModule_chartSchemeEtaleModule_eq_chartPush` holds by `rfl`, but
deciding it means seeing a fourfold composite of
`CategoryTheory.SheafOfModules.pushforward` collapse to a single one.  Projecting the `val` field
of `CategoryTheory.eqToHom` of that equality — which is what the component of a *composite* in
`CategoryTheory.SheafOfModules` asks for, since the composite is built by projecting the `val`
fields of its factors — forces `CategoryTheory.eqToHom` into constructor form, hence forces that
decision, and exhausts the heartbeat budget.  Every statement below therefore keeps
`(CategoryTheory.eqToIso …).hom.val.app (op V)` as an opaque unit.

**The generic lemmas are half-specialised.**  Instantiating a lemma stated for an arbitrary site,
ring sheaf and pair of sheaves of modules at the chart data leaves the elaborator enough
metavariables that it falls back on definitional unification and pays the cost above; so does
leaving the *source* sheaf of modules a variable, which is the object the chart data determines.
`AlgebraicGeometry.Space.eqToHom_chartPush_obj_eqToIso_hom_val_app_apply` and
`AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModuleSheaf_hom_comp_val_app_apply` are
therefore stated with the chart, the open and the source spelling of the chart restriction already
written out, and only the transported object, the transport and the second factor as variables:
every instantiation is then first-order.

**The isomorphisms are compared unapplied, and only then carried to sections.**
`AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush_hom` and
`AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModuleSheaf_hom_val_app` hold unapplied and
are applied by `congrArg` and `DFunLike.congr_fun`; the applied forms time out.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (M N : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)

/-! ### The two sections identifications of a chart restriction -/

/-- The sections identification of the direct-image spelling of the chart restriction is the
transport along `AlgebraicGeometry.Space.chartPush_obj`. -/
theorem chartPushEquiv_eq_eqToHom_apply (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens) (w : (chartPush B S hS X M A).val.obj (op V)) :
    chartPushEquiv B S hS X M A V w = (eqToHom (chartPush_obj B S hS X M A V)).hom w :=
  Stacks.ModuleCat.eqToIso_toLinearEquiv_apply (chartPush_obj B S hS X M A V) w

/-- **A transport of the chart restriction along an equality of sheaves of modules, read on a
section and followed by a sections identification of the target, is a sections identification of
the source.**

The target sheaf of modules, the equality and the two sections identifications are variables; the
source spelling of the chart restriction is written out, because it is what the chart data
determines and leaving it a variable makes the instantiation pay for the definitional collapse of
the fourfold pushforward. -/
theorem eqToHom_chartPush_obj_eqToIso_hom_val_app_apply (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens)
    {P : SheafOfModules.{u} (chartScheme A).ringCatSheaf}
    (h : ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
            (chartSchemeEtaleModule B S hS X M hM A) :
          SheafOfModules.{u} (chartScheme A).ringCatSheaf) = P)
    {W : ModuleCat.{u} ↑((chartScheme A).ringCatSheaf.obj.obj (op V))}
    (hP : P.val.obj (op V) = W)
    (hL : ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X M hM A)).val.obj (op V) = W)
    (z : ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X M hM A)).val.obj (op V)) :
    (eqToHom hP).hom (((eqToIso h).hom.val.app (op V)).hom z) = (eqToHom hL).hom z := by
  subst h
  exact congrArg (fun k : ((_root_.AlgebraicGeometry.SmallEtale.restrictModule
      (associatedBigEtaleSite B) (chartScheme A)
        (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X M hM A)).val.obj (op V) = W =>
    (eqToHom k).hom z) (proof_irrel hL hP)

/-- **The chart sections identification is the sections identification of the direct-image
spelling, read through the pinned equality of the two spellings of the chart restriction.** -/
theorem chartPushEquiv_eqToIso_apply (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens)
    (z : ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X M hM A)).val.obj (op V)) :
    chartPushEquiv B S hS X M A V
        (((eqToIso (restrictModule_chartSchemeEtaleModule_eq_chartPush
          B S hS X M hM A)).hom.val.app (op V)).hom z) =
      chartSectionsLinearEquiv B S hS X M hM A V z :=
  (chartPushEquiv_eq_eqToHom_apply B S hS X M A V _).trans
    ((eqToHom_chartPush_obj_eqToIso_hom_val_app_apply B S hS X M hM A V
        (restrictModule_chartSchemeEtaleModule_eq_chartPush B S hS X M hM A)
        (chartPush_obj B S hS X M A V)
        (restrictModule_chartSchemeEtaleModule_obj_moduleCat B S hS X M hM A V) z).trans
      (chartSectionsLinearEquiv_apply B S hS X M hM A V z).symm)

/-! ### The component of the chart transport isomorphism -/

/-- The component of a composite out of the pinned chart restriction isomorphism, read on a
section.  The second factor is a variable: with it written out, matching the composite forces the
`val` field of a transport along
`AlgebraicGeometry.Space.restrictModule_chartSchemeEtaleModule_eq_chartPush` and the heartbeat
budget is gone. -/
theorem chartSchemeModuleIsoRestrictModuleSheaf_hom_comp_val_app_apply
    (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens)
    (b : ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
            (chartSchemeEtaleModule B S hS X M hM A) :
          SheafOfModules.{u} (chartScheme A).ringCatSheaf) ⟶ chartPush B S hS X M A)
    (x : (chartSchemeModule B S hS X M hM A).val.obj (op V)) :
    (((chartSchemeModuleIsoRestrictModuleSheaf B S hS X M hM A).hom ≫ b).val.app (op V)).hom x =
      (b.val.app (op V)).hom
        (((chartSchemeModuleIsoRestrictModuleSheaf B S hS X M hM A).hom.val.app (op V)).hom x) :=
  Stacks.SheafOfModules.comp_val_app_hom_apply
    (chartSchemeModuleIsoRestrictModuleSheaf B S hS X M hM A).hom b (op V) x

/-- The component of `AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush` on a section, split
into its two pinned factors. -/
theorem chartSchemeModuleIsoChartPush_hom_val_app_apply (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens) (x : (chartSchemeModule B S hS X M hM A).val.obj (op V)) :
    ((chartSchemeModuleIsoChartPush B S hS X M hM A).hom.val.app (op V)).hom x =
      ((eqToIso (restrictModule_chartSchemeEtaleModule_eq_chartPush
          B S hS X M hM A)).hom.val.app (op V)).hom
        (((chartSchemeModuleIsoRestrictModule B S hS X M hM A).hom.val.app (op V)).hom x) :=
  (congrArg
      (fun k : (chartSchemeModule B S hS X M hM A :
            SheafOfModules.{u} (chartScheme A).ringCatSheaf) ⟶ chartPush B S hS X M A =>
        (k.val.app (op V)).hom x)
      (chartSchemeModuleIsoChartPush_hom B S hS X M hM A)).trans
    ((chartSchemeModuleIsoRestrictModuleSheaf_hom_comp_val_app_apply B S hS X M hM A V _ x).trans
      (congrArg
        (fun y => ((eqToIso (restrictModule_chartSchemeEtaleModule_eq_chartPush
            B S hS X M hM A)).hom.val.app (op V)).hom y)
        (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
          (chartSchemeModuleIsoRestrictModuleSheaf_hom_val_app B S hS X M hM A V)) x)))

/-- **The bridge between the two sections identifications of the chart restriction**: reading a
section of the chosen spelling through
`AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush` and the sections identification of the
direct-image spelling is reading it through
`AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule` and the chart sections
identification. -/
theorem chartPushEquiv_chartSchemeModuleIsoChartPush_apply (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens) (x : (chartSchemeModule B S hS X M hM A).val.obj (op V)) :
    chartPushEquiv B S hS X M A V
        (((chartSchemeModuleIsoChartPush B S hS X M hM A).hom.val.app (op V)).hom x) =
      chartSectionsLinearEquiv B S hS X M hM A V
        (((chartSchemeModuleIsoRestrictModule B S hS X M hM A).hom.val.app (op V)).hom x) :=
  (congrArg (fun w : (chartPush B S hS X M A).val.obj (op V) =>
        chartPushEquiv B S hS X M A V w)
      (chartSchemeModuleIsoChartPush_hom_val_app_apply B S hS X M hM A V x)).trans
    (chartPushEquiv_eqToIso_apply B S hS X M hM A V _)

/-! ### The component formula at the direct-image spelling -/

/-- **The component formula for the Hom-set transport of the chart restriction, read at the
direct-image spelling.**  This is
`AlgebraicGeometry.Space.chartSectionsLinearEquiv_chartSchemeModuleHomEquiv_apply` with both
sections identifications respelled through `AlgebraicGeometry.Space.chartPushEquiv`. -/
theorem chartPushEquiv_chartSchemeModuleHomEquiv_apply (A : SmallEtale B S hS X.1)
    (α : M.over A ⟶ N.over A) (V : (chartScheme A).Opens)
    (x : (chartSchemeModule B S hS X M hM A).val.obj (op V)) :
    chartPushEquiv B S hS X N A V
        (((chartSchemeModuleIsoChartPush B S hS X N hN A).hom.val.app (op V)).hom
          (((chartSchemeModuleHomEquiv B S hS X M N hM hN A α).val.app (op V)).hom x)) =
      (α.val.app (op (openChartOfComparisonOver B S hS X A V))).hom
        (chartPushEquiv B S hS X M A V
          (((chartSchemeModuleIsoChartPush B S hS X M hM A).hom.val.app (op V)).hom x)) :=
  ((chartPushEquiv_chartSchemeModuleIsoChartPush_apply B S hS X N hN A V _).trans
      (chartSectionsLinearEquiv_chartSchemeModuleHomEquiv_apply
        B S hS X M N hM hN A α V x)).trans
    (congrArg (fun w => (α.val.app (op (openChartOfComparisonOver B S hS X A V))).hom w)
      (chartPushEquiv_chartSchemeModuleIsoChartPush_apply B S hS X M hM A V x).symm)

/-- **The component formula at the direct-image spelling, read backwards.**  This is
`AlgebraicGeometry.Space.chartSectionsLinearEquiv_chartSchemeModuleHomEquiv_symm_apply` with both
sections identifications respelled through `AlgebraicGeometry.Space.chartPushEquiv`. -/
theorem chartPushEquiv_chartSchemeModuleHomEquiv_symm_apply (A : SmallEtale B S hS X.1)
    (β : chartSchemeModule B S hS X M hM A ⟶ chartSchemeModule B S hS X N hN A)
    (V : (chartScheme A).Opens)
    (x : (chartSchemeModule B S hS X M hM A).val.obj (op V)) :
    (((chartSchemeModuleHomEquiv B S hS X M N hM hN A).symm β).val.app
          (op (openChartOfComparisonOver B S hS X A V))).hom
        (chartPushEquiv B S hS X M A V
          (((chartSchemeModuleIsoChartPush B S hS X M hM A).hom.val.app (op V)).hom x)) =
      chartPushEquiv B S hS X N A V
        (((chartSchemeModuleIsoChartPush B S hS X N hN A).hom.val.app (op V)).hom
          ((β.val.app (op V)).hom x)) :=
  (congrArg (fun w => (((chartSchemeModuleHomEquiv B S hS X M N hM hN A).symm β).val.app
          (op (openChartOfComparisonOver B S hS X A V))).hom w)
      (chartPushEquiv_chartSchemeModuleIsoChartPush_apply B S hS X M hM A V x)).trans
    ((chartSectionsLinearEquiv_chartSchemeModuleHomEquiv_symm_apply
        B S hS X M N hM hN A β V x).trans
      (chartPushEquiv_chartSchemeModuleIsoChartPush_apply B S hS X N hN A V _).symm)

end AlgebraicGeometry.Space

end
