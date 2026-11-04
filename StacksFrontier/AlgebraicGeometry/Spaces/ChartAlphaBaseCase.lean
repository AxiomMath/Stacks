module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartComponentDetermination
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealPowHomEquiv

/-!
# The base case of the component determination of Stacks 07UM

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B`, let `ℐ ⊆ 𝒪_X` be a sheaf
of ideals which is cartesian on affine charts, let `U = X ∖ V(ℐ)`, let `𝒢` be coherent and `ℱ`
quasi-coherent, and let `θ : 𝒢|_U ⟶ ℱ|_U`.  `AlgebraicGeometry.Space.chartAlpha` reads a morphism
`φ` out of `Iᵏ` times the chart restriction of `𝒢` on the scheme of an étale chart `A` as a
morphism `(ℐᵏ𝒢)|_A ⟶ ℱ|_A` of the restrictions to the slice of the small étale site of `X` at `A`.

The component determination of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartComponentDetermination.lean` takes as a hypothesis
`hbase` that the component of that morphism at the chart cut out by a Zariski open of the chart's
scheme off the support of the chartwise sheaf of ideals is the transport of `θ` there.  **This
file discharges `hbase`**, and therefore gives the component determination with no hypothesis
beyond `AlgebraicGeometry.Space.exists_homRestrict_eq_chartThetaOver`'s conclusion
`homRestrict φ = chartThetaOver`.

## Main results

* `Stacks.SheafOfModules.iso_hom_val_app_inv_val_app_apply` and
  `Stacks.SheafOfModules.val_app_apply_of_comp_eq₃`: the two generic facts about components of
  morphisms of sheaves of modules used throughout — an isomorphism is undone by its inverse on
  sections, and two factorizations of one morphism give the same value on a section.
* `AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush_inv` and
  `AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush_inv_comp_hom`: **the inverse of the
  chart restriction isomorphism decomposed into its two pinned factors**, and the cancellation
  which leaves only the transport along the equality of the two spellings of the chart
  restriction.
* `AlgebraicGeometry.Space.chartSectionsLinearEquiv_eqToIso_inv_apply`: the chart sections
  identification read after the inverse of that transport is the sections identification of the
  direct-image spelling.  This is the mirror of
  `AlgebraicGeometry.Space.chartPushEquiv_eqToIso_apply`.
* `AlgebraicGeometry.Space.chartSchemeModuleHomEquiv_symm_val_app_conj_apply'`: **the component
  formula for the inverse Hom-set transport of a conjugated morphism** — for
  `β = iso.hom ≫ ψ ≫ iso.inv`, the component of `(chartSchemeModuleHomEquiv … A).symm β` over the
  object of the slice which a Zariski open `V` cuts out is the `V`-component of `ψ`, read through
  the sections identifications of the direct-image spelling.
* `AlgebraicGeometry.Space.phi_val_app_chartPushFactor_apply`: **a morphism out of `Iᵏ` times the
  chart restriction of `𝒢` whose restriction off the support is the transport of `θ` is the
  transport of `θ` on every section of the chart restriction of `ℐᵏ𝒢` over a Zariski open off the
  support.**
* `AlgebraicGeometry.Space.chartAlphaSheaf_val_app_openChartInclusion_eq_complementHomOnChart`:
  **the base case**, in exactly the shape the hypothesis `hbase` of
  `AlgebraicGeometry.Space.chartAlpha_val_app_eq_homOnChart` asks for.
* `AlgebraicGeometry.Space.chartAlphaSheaf_val_app_eq_homOnChart_of_homRestrict`: **the component
  determination for the chart transport of [Stacks, Tag 07UM], with its base case discharged.**

## Implementation notes

**A composite whose second factor is the chart restriction isomorphism must never have its `val`
field projected.**  `AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush` is a composite with
`CategoryTheory.eqToIso` of an equality of sheaves of modules whose decision costs the heartbeat
budget, and matching the component of such a composite against its decomposition forces that
decision.  With the isomorphism as the *first* factor and the second factor a variable
the match is immediate; with the isomorphism as the *second* factor it times out, in every
spelling — including the instantiation of a fully generic lemma, and including the
instantiation of a generic lemma whose only content is the cancellation `e.hom ∘ e.inv = id`.

Every statement below is therefore shaped so that the isomorphism occurs either alone or as the
first factor of a composite.  Three devices do this:

1. **The conjugated morphism is a parameter with an equation.**
   `AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModuleSheaf_hom_val_app_conj_apply` takes
   `β` and `hβ : β = iso.hom ≫ ψ ≫ iso.inv`, so its conclusion mentions each morphism alone;
   the equation is consumed at the level of *morphisms*, where no `val` field is projected.
2. **The equality of the two spellings is a parameter.**
   `AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush_hom_comp_eqToIso_inv_val_app_apply`
   leaves the equality and the object it transports to as variables, exactly as
   `AlgebraicGeometry.Space.eqToHom_chartPush_obj_eqToIso_hom_val_app_apply` does; written out,
   the instantiation of a composite second factor times out.
3. **The pinned half of the isomorphism is used wherever an inverse is needed.**
   `AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModuleSheaf` contains no
   `CategoryTheory.eqToIso`, so the cancellation of its forward and inverse components *is*
   affordable, and the surjectivity statements below are built from it rather than from
   `AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush`.

**Surjectivity is obtained by `Function.Surjective.exists`, not by an inverse.**  The witness in
`AlgebraicGeometry.Space.chartSchemeModuleHomEquiv_symm_val_app_conj_apply'` is produced by
`LinearEquiv.surjective`, so the section of the pinned spelling stays a local variable; writing
it as `(chartSectionsLinearEquiv …).symm w` makes the elaborator unfold the transport.

**Every lambda binder carries its type.**  An unannotated `fun z => …` in a `congrArg` over the
sections of a chart restriction makes the elaborator reconstruct that type, and the fourfold
pushforward is reconstructed with it.

**No declaration here carries a `stacks` tag.**  This is an input to [Stacks, Tag 07UM], not an
assertion of it: the descent from the chart is not proved here, and the surjectivity clause of
Tag 07UM is therefore still unavailable.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

universe w m v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : CategoryTheory.Sheaf J RingCat.{w}}

/-- The component of the forward map of an isomorphism of sheaves of modules undoes the component
of its inverse. -/
theorem iso_hom_val_app_inv_val_app_apply {M N : _root_.SheafOfModules.{m} R} (e : M ≅ N)
    (Z : Cᵒᵖ) (w : N.val.obj Z) :
    (e.hom.val.app Z).hom ((e.inv.val.app Z).hom w) = w :=
  (comp_val_app_hom_apply e.inv e.hom Z w).symm.trans
    (congrArg (fun k : N ⟶ N => (k.val.app Z).hom w) e.inv_hom_id)

/-- **Two factorizations of one morphism of sheaves of modules give the same value on a
section**, the second factorization having three factors.  The factorization equality is a
hypothesis, so that a consumer instantiating this never has a composite matched against a
decomposition: every morphism occurring in the conclusion occurs alone. -/
theorem val_app_apply_of_comp_eq₃ {M N P Q T : _root_.SheafOfModules.{m} R}
    (a : M ⟶ N) (b : N ⟶ P) (e : M ⟶ T) (c : T ⟶ Q) (d : Q ⟶ P)
    (h : a ≫ b = e ≫ c ≫ d) (Z : Cᵒᵖ) (x : M.val.obj Z) :
    (b.val.app Z).hom ((a.val.app Z).hom x) =
      (d.val.app Z).hom ((c.val.app Z).hom ((e.val.app Z).hom x)) :=
  (comp_val_app_hom_apply a b Z x).symm.trans
    ((congrArg (fun m : M ⟶ P => (m.val.app Z).hom x) h).trans
      ((comp_val_app_hom_apply e (c ≫ d) Z x).trans
        (comp_val_app_hom_apply c d Z _)))

end Stacks.SheafOfModules

namespace Stacks.AlgebraicGeometry.Scheme.Modules

universe u₁

/-- The component of a morphism of modules on a scheme, read on a section. -/
theorem app_apply {T : _root_.AlgebraicGeometry.Scheme.{u₁}}
    {M N : T.Modules} (f : M ⟶ N) (V : T.Opens) (x : Γ(M, V)) :
    f.app V x = (f.val.app (op V)).hom x := rfl

end Stacks.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (M N : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)

/-! ### The inverse of the chart restriction isomorphism, pinned -/

/-- The inverse of the pinned chart restriction isomorphism is the inverse of the unpinned one on
sections, compared **unapplied**. -/
theorem chartSchemeModuleIsoRestrictModuleSheaf_inv_val_app (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens) :
    (chartSchemeModuleIsoRestrictModuleSheaf B S hS X M hM A).inv.val.app (op V) =
      (chartSchemeModuleIsoRestrictModule B S hS X M hM A).inv.val.app (op V) := rfl

/-- The inverse of `AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush` is the composite of
the inverses of its two pinned factors. -/
theorem chartSchemeModuleIsoChartPush_inv (A : SmallEtale B S hS X.1) :
    (chartSchemeModuleIsoChartPush B S hS X M hM A).inv =
      (eqToIso (restrictModule_chartSchemeEtaleModule_eq_chartPush B S hS X M hM A)).inv ≫
        (chartSchemeModuleIsoRestrictModuleSheaf B S hS X M hM A).inv :=
  (congrArg Iso.inv (chartSchemeModuleIsoChartPush_eq B S hS X M hM A)).trans
    (Iso.trans_inv _ _)

/-- **Composing the inverse of `AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush` with the
forward map of its pinned first factor leaves the transport along the equality of the two
spellings of the chart restriction.** -/
theorem chartSchemeModuleIsoChartPush_inv_comp_hom (A : SmallEtale B S hS X.1) :
    (chartSchemeModuleIsoChartPush B S hS X M hM A).inv ≫
        (chartSchemeModuleIsoRestrictModuleSheaf B S hS X M hM A).hom =
      (eqToIso (restrictModule_chartSchemeEtaleModule_eq_chartPush B S hS X M hM A)).inv := by
  rw [chartSchemeModuleIsoChartPush_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-! ### Half-specialised component lemmas -/

/-- A composite whose second factor is the forward map of the pinned chart restriction
isomorphism, read on a section.  The first factor is a variable. -/
theorem comp_chartSchemeModuleIsoRestrictModuleSheaf_hom_val_app_apply
    (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens)
    {Q : SheafOfModules.{u} (chartScheme A).ringCatSheaf}
    (a : Q ⟶ chartSchemeModule B S hS X M hM A) (x : Q.val.obj (op V)) :
    ((a ≫ (chartSchemeModuleIsoRestrictModuleSheaf B S hS X M hM A).hom).val.app (op V)).hom x =
      ((chartSchemeModuleIsoRestrictModuleSheaf B S hS X M hM A).hom.val.app (op V)).hom
        ((a.val.app (op V)).hom x) :=
  Stacks.SheafOfModules.comp_val_app_hom_apply a
    (chartSchemeModuleIsoRestrictModuleSheaf B S hS X M hM A).hom (op V) x

/-- A composite whose second factor is the inverse of a transport of the chart restriction along
an equality of sheaves of modules, read on a section.  The equality, the transported object and
the first factor are variables; the source spelling of the chart restriction is written out. -/
theorem comp_eqToIso_inv_val_app_apply (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens)
    {P : SheafOfModules.{u} (chartScheme A).ringCatSheaf}
    (h : ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
            (chartSchemeEtaleModule B S hS X M hM A) :
          SheafOfModules.{u} (chartScheme A).ringCatSheaf) = P)
    {Q : SheafOfModules.{u} (chartScheme A).ringCatSheaf} (a : Q ⟶ P) (x : Q.val.obj (op V)) :
    ((a ≫ (eqToIso h).inv).val.app (op V)).hom x =
      ((eqToIso h).inv.val.app (op V)).hom ((a.val.app (op V)).hom x) :=
  Stacks.SheafOfModules.comp_val_app_hom_apply a (eqToIso h).inv (op V) x

/-- A composite whose first factor is the forward map of
`AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush`, read on a section.  The second factor and
its target are variables. -/
theorem chartSchemeModuleIsoChartPush_hom_comp_val_app_apply (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens) {P : AlgebraicGeometry.Scheme.Modules (chartScheme A)}
    (b : chartPush B S hS X M A ⟶ P)
    (x : (chartSchemeModule B S hS X M hM A).val.obj (op V)) :
    (((chartSchemeModuleIsoChartPush B S hS X M hM A).hom ≫ b).val.app (op V)).hom x =
      (b.val.app (op V)).hom
        (((chartSchemeModuleIsoChartPush B S hS X M hM A).hom.val.app (op V)).hom x) :=
  Stacks.SheafOfModules.comp_val_app_hom_apply
    (chartSchemeModuleIsoChartPush B S hS X M hM A).hom b (op V) x

/-- **A transport of the chart restriction along an equality of sheaves of modules, read
backwards on a section and followed by a sections identification of the source, is a sections
identification of the target.**

This is the mirror, for the inverse of the transport, of
`AlgebraicGeometry.Space.eqToHom_chartPush_obj_eqToIso_hom_val_app_apply`. -/
theorem eqToHom_eqToIso_inv_val_app_apply (A : SmallEtale B S hS X.1)
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
    (z : P.val.obj (op V)) :
    (eqToHom hL).hom (((eqToIso h).inv.val.app (op V)).hom z) = (eqToHom hP).hom z := by
  subst h
  exact congrArg (fun k : ((_root_.AlgebraicGeometry.SmallEtale.restrictModule
      (associatedBigEtaleSite B) (chartScheme A)
        (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X M hM A)).val.obj (op V) = W =>
    (eqToHom k).hom z) (proof_irrel hL hP)

/-- **The chart sections identification, read after the inverse of the pinned equality of the two
spellings of the chart restriction, is the sections identification of the direct-image
spelling.**  This is the mirror of `AlgebraicGeometry.Space.chartPushEquiv_eqToIso_apply`. -/
theorem chartSectionsLinearEquiv_eqToIso_inv_apply (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens) (z : (chartPush B S hS X M A).val.obj (op V)) :
    chartSectionsLinearEquiv B S hS X M hM A V
        (((eqToIso (restrictModule_chartSchemeEtaleModule_eq_chartPush
          B S hS X M hM A)).inv.val.app (op V)).hom z) =
      chartPushEquiv B S hS X M A V z :=
  (chartSectionsLinearEquiv_apply B S hS X M hM A V _).trans
    ((eqToHom_eqToIso_inv_val_app_apply B S hS X M hM A V
        (restrictModule_chartSchemeEtaleModule_eq_chartPush B S hS X M hM A)
        (chartPush_obj B S hS X M A V)
        (restrictModule_chartSchemeEtaleModule_obj_moduleCat B S hS X M hM A V) z).trans
      (chartPushEquiv_eq_eqToHom_apply B S hS X M A V z).symm)

/-! ### The component of a conjugated morphism -/

/-- **Postcomposing the inverse of the chart restriction isomorphism with the forward map of its
pinned first factor leaves the transport along the equality of the two spellings.** -/
theorem comp_chartSchemeModuleIsoChartPush_inv_comp_hom (A : SmallEtale B S hS X.1)
    (ψ : (chartPush B S hS X M A : SheafOfModules.{u} (chartScheme A).ringCatSheaf) ⟶
      chartPush B S hS X N A) :
    (ψ ≫ (chartSchemeModuleIsoChartPush B S hS X N hN A).inv) ≫
        (chartSchemeModuleIsoRestrictModuleSheaf B S hS X N hN A).hom =
      ψ ≫ (eqToIso (restrictModule_chartSchemeEtaleModule_eq_chartPush B S hS X N hN A)).inv := by
  rw [Category.assoc, chartSchemeModuleIsoChartPush_inv_comp_hom]

/-- **The factorization of a conjugated morphism, composed with the pinned sections
identification of the target.**  The conjugated morphism is a parameter with an equation, so that
the conclusion of the component lemma below mentions each morphism alone. -/
theorem comp_chartSchemeModuleIsoRestrictModuleSheaf_hom_eq (A : SmallEtale B S hS X.1)
    (ψ : (chartPush B S hS X M A : SheafOfModules.{u} (chartScheme A).ringCatSheaf) ⟶
      chartPush B S hS X N A)
    (β : (chartSchemeModule B S hS X M hM A :
        SheafOfModules.{u} (chartScheme A).ringCatSheaf) ⟶
      chartSchemeModule B S hS X N hN A)
    (hβ : β = (chartSchemeModuleIsoChartPush B S hS X M hM A).hom ≫ ψ ≫
      (chartSchemeModuleIsoChartPush B S hS X N hN A).inv) :
    β ≫ (chartSchemeModuleIsoRestrictModuleSheaf B S hS X N hN A).hom =
      (chartSchemeModuleIsoChartPush B S hS X M hM A).hom ≫ ψ ≫
        (eqToIso (restrictModule_chartSchemeEtaleModule_eq_chartPush B S hS X N hN A)).inv := by
  subst hβ
  rw [Category.assoc, comp_chartSchemeModuleIsoChartPush_inv_comp_hom]

/-- **The conjugated morphism, read through the pinned sections identification of the target, is
its factorization through the transport**, on a section. -/
theorem chartSchemeModuleIsoRestrictModuleSheaf_hom_comp_val_app_conj_apply
    (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens)
    (ψ : (chartPush B S hS X M A : SheafOfModules.{u} (chartScheme A).ringCatSheaf) ⟶
      chartPush B S hS X N A)
    (β : (chartSchemeModule B S hS X M hM A :
        SheafOfModules.{u} (chartScheme A).ringCatSheaf) ⟶
      chartSchemeModule B S hS X N hN A)
    (hβ : β = (chartSchemeModuleIsoChartPush B S hS X M hM A).hom ≫ ψ ≫
      (chartSchemeModuleIsoChartPush B S hS X N hN A).inv)
    (x : (chartSchemeModule B S hS X M hM A).val.obj (op V)) :
    ((β ≫ (chartSchemeModuleIsoRestrictModuleSheaf B S hS X N hN A).hom).val.app (op V)).hom x =
      (((chartSchemeModuleIsoChartPush B S hS X M hM A).hom ≫ ψ ≫
          (eqToIso (restrictModule_chartSchemeEtaleModule_eq_chartPush
            B S hS X N hN A)).inv).val.app (op V)).hom x :=
  congrArg
    (fun m : (chartSchemeModule B S hS X M hM A :
          SheafOfModules.{u} (chartScheme A).ringCatSheaf) ⟶
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
            (chartSchemeEtaleModule B S hS X N hN A) :
          SheafOfModules.{u} (chartScheme A).ringCatSheaf) => (m.val.app (op V)).hom x)
    (comp_chartSchemeModuleIsoRestrictModuleSheaf_hom_eq B S hS X M N hM hN A ψ β hβ)

/-- **The component of the factorization.**  The equality of the two spellings of the chart
restriction and the object it transports to are parameters; with them written out the
instantiation of
`AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush_hom_comp_val_app_apply` at a composite
second factor forces the definitional collapse of the fourfold pushforward. -/
theorem chartSchemeModuleIsoChartPush_hom_comp_eqToIso_inv_val_app_apply
    (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens)
    {P : SheafOfModules.{u} (chartScheme A).ringCatSheaf}
    (h : ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
            (chartSchemeEtaleModule B S hS X N hN A) :
          SheafOfModules.{u} (chartScheme A).ringCatSheaf) = P)
    (ψ : (chartPush B S hS X M A : SheafOfModules.{u} (chartScheme A).ringCatSheaf) ⟶ P)
    (x : (chartSchemeModule B S hS X M hM A).val.obj (op V)) :
    (((chartSchemeModuleIsoChartPush B S hS X M hM A).hom ≫ ψ ≫
          (eqToIso h).inv).val.app (op V)).hom x =
      ((eqToIso h).inv.val.app (op V)).hom
        ((ψ.val.app (op V)).hom
          (((chartSchemeModuleIsoChartPush B S hS X M hM A).hom.val.app (op V)).hom x)) :=
  (chartSchemeModuleIsoChartPush_hom_comp_val_app_apply B S hS X M hM A V
      (ψ ≫ (eqToIso h).inv) x).trans
    (comp_eqToIso_inv_val_app_apply B S hS X N hN A V h ψ _)

/-- **The component of a conjugated morphism of the chosen chart restrictions, read through the
pinned sections identification of the target.**  The conjugated morphism is a parameter with an
equation. -/
theorem chartSchemeModuleIsoRestrictModuleSheaf_hom_val_app_conj_apply
    (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens)
    (ψ : (chartPush B S hS X M A : SheafOfModules.{u} (chartScheme A).ringCatSheaf) ⟶
      chartPush B S hS X N A)
    (β : (chartSchemeModule B S hS X M hM A :
        SheafOfModules.{u} (chartScheme A).ringCatSheaf) ⟶
      chartSchemeModule B S hS X N hN A)
    (hβ : β = (chartSchemeModuleIsoChartPush B S hS X M hM A).hom ≫ ψ ≫
      (chartSchemeModuleIsoChartPush B S hS X N hN A).inv)
    (x : (chartSchemeModule B S hS X M hM A).val.obj (op V)) :
    ((chartSchemeModuleIsoRestrictModuleSheaf B S hS X N hN A).hom.val.app (op V)).hom
        ((β.val.app (op V)).hom x) =
      ((eqToIso (restrictModule_chartSchemeEtaleModule_eq_chartPush
            B S hS X N hN A)).inv.val.app (op V)).hom
        ((ψ.val.app (op V)).hom
          (((chartSchemeModuleIsoChartPush B S hS X M hM A).hom.val.app (op V)).hom x)) :=
  (comp_chartSchemeModuleIsoRestrictModuleSheaf_hom_val_app_apply B S hS X N hN A V β x).symm.trans
    ((chartSchemeModuleIsoRestrictModuleSheaf_hom_comp_val_app_conj_apply
        B S hS X M N hM hN A V ψ β hβ x).trans
      (chartSchemeModuleIsoChartPush_hom_comp_eqToIso_inv_val_app_apply B S hS X M N hM hN A V
        (restrictModule_chartSchemeEtaleModule_eq_chartPush B S hS X N hN A) ψ x))

/-! ### The component of the inverse Hom-set transport at a Zariski open -/

/-- The component of the unpinned chart restriction isomorphism is the component of its pinned
spelling, read on a section. -/
theorem chartSchemeModuleIsoRestrictModule_hom_val_app_apply (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens) (t : (chartSchemeModule B S hS X M hM A).val.obj (op V)) :
    ((chartSchemeModuleIsoRestrictModule B S hS X M hM A).hom.val.app (op V)).hom t =
      ((chartSchemeModuleIsoRestrictModuleSheaf B S hS X M hM A).hom.val.app (op V)).hom t :=
  (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (chartSchemeModuleIsoRestrictModuleSheaf_hom_val_app B S hS X M hM A V)) t).symm

/-- The component of the pinned chart restriction isomorphism undoes the component of its
inverse. -/
theorem chartSchemeModuleIsoRestrictModuleSheaf_hom_inv_val_app_apply
    (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens)
    (s : ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X M hM A)).val.obj (op V)) :
    ((chartSchemeModuleIsoRestrictModuleSheaf B S hS X M hM A).hom.val.app (op V)).hom
        (((chartSchemeModuleIsoRestrictModuleSheaf B S hS X M hM A).inv.val.app (op V)).hom s) =
      s :=
  Stacks.SheafOfModules.iso_hom_val_app_inv_val_app_apply
    (chartSchemeModuleIsoRestrictModuleSheaf B S hS X M hM A) (op V) s

/-- The chart sections identification is unchanged by inserting the component of the chart
restriction isomorphism after the component of the inverse of its pinned spelling. -/
theorem chartSectionsLinearEquiv_isoRestrictSheaf_inv_apply (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens)
    (t : ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X M hM A)).val.obj (op V)) :
    chartSectionsLinearEquiv B S hS X M hM A V
        (((chartSchemeModuleIsoRestrictModule B S hS X M hM A).hom.val.app (op V)).hom
          (((chartSchemeModuleIsoRestrictModuleSheaf B S hS X M hM A).inv.val.app
            (op V)).hom t)) =
      chartSectionsLinearEquiv B S hS X M hM A V t :=
  congrArg (fun z : ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X M hM A)).val.obj (op V) =>
      chartSectionsLinearEquiv B S hS X M hM A V z)
    ((chartSchemeModuleIsoRestrictModule_hom_val_app_apply B S hS X M hM A V
        (((chartSchemeModuleIsoRestrictModuleSheaf B S hS X M hM A).inv.val.app
          (op V)).hom t)).trans
      (chartSchemeModuleIsoRestrictModuleSheaf_hom_inv_val_app_apply B S hS X M hM A V t))

/-- **The component of the chart restriction isomorphism carries the witness built from a
section of the pinned spelling to the section of the direct-image spelling it identifies.** -/
theorem chartSchemeModuleIsoChartPush_hom_val_app_isoRestrictSheaf_inv_apply
    (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens)
    (t : ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X M hM A)).val.obj (op V))
    (y : (chartPush B S hS X M A).val.obj (op V))
    (ht : chartSectionsLinearEquiv B S hS X M hM A V t = chartPushEquiv B S hS X M A V y) :
    ((chartSchemeModuleIsoChartPush B S hS X M hM A).hom.val.app (op V)).hom
        (((chartSchemeModuleIsoRestrictModuleSheaf B S hS X M hM A).inv.val.app (op V)).hom t) =
      y :=
  (chartPushEquiv B S hS X M A V).injective
    ((chartPushEquiv_chartSchemeModuleIsoChartPush_apply B S hS X M hM A V
          (((chartSchemeModuleIsoRestrictModuleSheaf B S hS X M hM A).inv.val.app
            (op V)).hom t)).trans
      ((chartSectionsLinearEquiv_isoRestrictSheaf_inv_apply B S hS X M hM A V t).trans ht))

/-- **The component formula for the inverse Hom-set transport of a conjugated morphism, at the
sections identifications of the direct-image spelling.**

The conjugated morphism is a parameter with an equation. -/
theorem chartSchemeModuleHomEquiv_symm_val_app_conj_apply (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens)
    (ψ : (chartPush B S hS X M A : SheafOfModules.{u} (chartScheme A).ringCatSheaf) ⟶
      chartPush B S hS X N A)
    (β : (chartSchemeModule B S hS X M hM A :
        SheafOfModules.{u} (chartScheme A).ringCatSheaf) ⟶
      chartSchemeModule B S hS X N hN A)
    (hβ : β = (chartSchemeModuleIsoChartPush B S hS X M hM A).hom ≫ ψ ≫
      (chartSchemeModuleIsoChartPush B S hS X N hN A).inv)
    (x : (chartSchemeModule B S hS X M hM A).val.obj (op V)) :
    (((chartSchemeModuleHomEquiv B S hS X M N hM hN A).symm β).val.app
          (op (openChartOfComparisonOver B S hS X A V))).hom
        (chartSectionsLinearEquiv B S hS X M hM A V
          (((chartSchemeModuleIsoRestrictModule B S hS X M hM A).hom.val.app (op V)).hom x)) =
      chartPushEquiv B S hS X N A V
        ((ψ.val.app (op V)).hom
          (((chartSchemeModuleIsoChartPush B S hS X M hM A).hom.val.app (op V)).hom x)) :=
  (chartSectionsLinearEquiv_chartSchemeModuleHomEquiv_symm_apply B S hS X M N hM hN A β V x).trans
    ((congrArg
        (fun z : ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X N hN A)).val.obj (op V) =>
          chartSectionsLinearEquiv B S hS X N hN A V z)
        ((chartSchemeModuleIsoRestrictModule_hom_val_app_apply B S hS X N hN A V
            ((β.val.app (op V)).hom x)).trans
          (chartSchemeModuleIsoRestrictModuleSheaf_hom_val_app_conj_apply
            B S hS X M N hM hN A V ψ β hβ x))).trans
      (chartSectionsLinearEquiv_eqToIso_inv_apply B S hS X N hN A V
        ((ψ.val.app (op V)).hom
          (((chartSchemeModuleIsoChartPush B S hS X M hM A).hom.val.app (op V)).hom x))))

/-- **The component formula for the inverse Hom-set transport of a conjugated morphism, at an
arbitrary section of the direct-image spelling over a Zariski open of the chart's scheme.**

This is the base case which the component determination of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartComponentDetermination.lean` takes as a
hypothesis. -/
theorem chartSchemeModuleHomEquiv_symm_val_app_conj_apply' (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens)
    (ψ : (chartPush B S hS X M A : SheafOfModules.{u} (chartScheme A).ringCatSheaf) ⟶
      chartPush B S hS X N A)
    (β : (chartSchemeModule B S hS X M hM A :
        SheafOfModules.{u} (chartScheme A).ringCatSheaf) ⟶
      chartSchemeModule B S hS X N hN A)
    (hβ : β = (chartSchemeModuleIsoChartPush B S hS X M hM A).hom ≫ ψ ≫
      (chartSchemeModuleIsoChartPush B S hS X N hN A).inv)
    (y : (chartPush B S hS X M A).val.obj (op V)) :
    (((chartSchemeModuleHomEquiv B S hS X M N hM hN A).symm β).val.app
          (op (openChartOfComparisonOver B S hS X A V))).hom
        (chartPushEquiv B S hS X M A V y) =
      chartPushEquiv B S hS X N A V ((ψ.val.app (op V)).hom y) := by
  obtain ⟨t, ht⟩ := (chartSectionsLinearEquiv B S hS X M hM A V).surjective
    (chartPushEquiv B S hS X M A V y)
  refine Eq.trans (congrArg
    (fun v : (ModuleCat.restrictScalars (chartSectionsRingHom B S hS X A V)).obj
        (M.val.obj (op (openChartOfComparison B S hS X A V))) =>
      (((chartSchemeModuleHomEquiv B S hS X M N hM hN A).symm β).val.app
          (op (openChartOfComparisonOver B S hS X A V))).hom v)
    (((chartSectionsLinearEquiv_isoRestrictSheaf_inv_apply B S hS X M hM A V t).trans
      ht).symm)) ?_
  refine Eq.trans (chartSchemeModuleHomEquiv_symm_val_app_conj_apply B S hS X M N hM hN A V ψ β hβ
    (((chartSchemeModuleIsoRestrictModuleSheaf B S hS X M hM A).inv.val.app (op V)).hom t)) ?_
  exact congrArg
    (fun v : (chartPush B S hS X M A).val.obj (op V) =>
      chartPushEquiv B S hS X N A V ((ψ.val.app (op V)).hom v))
    (chartSchemeModuleIsoChartPush_hom_val_app_isoRestrictSheaf_inv_apply
      B S hS X M hM A V t y ht)

/-! ### The base case for the chart transport of Stacks 07UM -/

section ChartAlpha

variable (I : IdealSheaves B S hS X.1 X.2)
    (hIc : IsCartesianOnAffineCharts I.toSheafOfModules)
    (G F : Modules.{u, u} B S hS X.1 X.2)

/-- The chart restriction of the inclusion `ℐᵏ𝒢 ⟶ 𝒢`, read through the sections
identifications, is that inclusion on the sections over the étale chart which the open cuts
out. -/
theorem chartPushEquiv_chartPushι_apply (A : SmallEtale B S hS X.1) (k : ℕ)
    (V : (chartScheme A).Opens)
    (y : (chartPush B S hS X (idealPowModule I k G) A).val.obj (op V)) :
    chartPushEquiv B S hS X G A V (((chartPushι B S hS X I G A k).val.app (op V)).hom y) =
      ((idealPowModuleι I k G).val.app
        (op (openChartOfComparison B S hS X A V))).hom
          (chartPushEquiv B S hS X (idealPowModule I k G) A V y) := rfl

/-- The factorization of the chart restriction of `ℐᵏ𝒢 ⟶ 𝒢` through `Iᵏ` times the chart
restriction of `𝒢`, read on a section: it is that chart restriction, with the membership
witness attached. -/
theorem chartPushFactor_val_app_apply (hIq : I.toSheafOfModules.IsQuasicoherentOnSite)
    (hGq : G.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1) (k : ℕ)
    (V : (chartScheme A).Opens)
    (y : (chartPush B S hS X (idealPowModule I k G) A).val.obj (op V)) :
    ((chartPushFactor B S hS X I hIc G hIq hGq A k).val.app (op V)).hom y =
      ⟨((chartPushι B S hS X I G A k).val.app (op V)).hom y,
        chartPushι_app_mem B S hS X I hIc G hIq hGq A k (op V) y⟩ := rfl

/-- A composite whose first factor is the factorization of the chart restriction of
`ℐᵏ𝒢 ⟶ 𝒢`, read on a section.  The second factor and its target are variables. -/
theorem chartPushFactor_comp_val_app_apply (hIq : I.toSheafOfModules.IsQuasicoherentOnSite)
    (hGq : G.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1) (k : ℕ)
    (V : (chartScheme A).Opens)
    {P : AlgebraicGeometry.Scheme.Modules (chartScheme A)}
    (b : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A) ⟶ P)
    (y : (chartPush B S hS X (idealPowModule I k G) A).val.obj (op V)) :
    (((chartPushFactor B S hS X I hIc G hIq hGq A k) ≫ b).val.app (op V)).hom y =
      (b.val.app (op V)).hom
        (((chartPushFactor B S hS X I hIc G hIq hGq A k).val.app (op V)).hom y) :=
  Stacks.SheafOfModules.comp_val_app_hom_apply
    (chartPushFactor B S hS X I hIc G hIq hGq A k) b (op V) y

/-- The composite out of which `AlgebraicGeometry.Space.chartAlpha` is built, reassociated so
that the factorization and the morphism on the chart's scheme form a single factor. -/
theorem chartAlphaComposite_assoc (hZt : B.Contains (⊤_ Scheme.{u}))
    (hNo : IsNoetherian B S hS hZt X.1)
    (hIq : I.toSheafOfModules.IsQuasicoherentOnSite) (hFq : F.IsQuasicoherentOnSite)
    (hG : IsCoherent B S hS X.1 X.2 G) (A : SmallEtale B S hS X.1) (k : ℕ)
    (φ : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A) ⟶
      chartPush B S hS X F A) :
    (chartSchemeModuleIsoChartPush B S hS X (idealPowModule I k G)
          (isQuasicoherentOnSite_idealPowModule B S hS X I G hZt hNo hIq hG k) A).hom ≫
        chartPushFactor B S hS X I hIc G hIq hG.toIsQuasicoherentOnSite A k ≫ φ ≫
          (chartSchemeModuleIsoChartPush B S hS X F hFq A).inv =
      (chartSchemeModuleIsoChartPush B S hS X (idealPowModule I k G)
          (isQuasicoherentOnSite_idealPowModule B S hS X I G hZt hNo hIq hG k) A).hom ≫
        (chartPushFactor B S hS X I hIc G hIq hG.toIsQuasicoherentOnSite A k ≫ φ) ≫
          (chartSchemeModuleIsoChartPush B S hS X F hFq A).inv :=
  congrArg
    (fun m : chartPush B S hS X (idealPowModule I k G) A ⟶
        chartSchemeModule B S hS X F hFq A =>
      (chartSchemeModuleIsoChartPush B S hS X (idealPowModule I k G)
          (isQuasicoherentOnSite_idealPowModule B S hS X I G hZt hNo hIq hG k) A).hom ≫ m)
    (Category.assoc (chartPushFactor B S hS X I hIc G hIq hG.toIsQuasicoherentOnSite A k) φ
      (chartSchemeModuleIsoChartPush B S hS X F hFq A).inv).symm

/-- **The component of `AlgebraicGeometry.Space.chartAlpha` at the object of the slice which a
Zariski open of the chart's scheme cuts out.**  It is `φ` on the sections over that open,
precomposed with the factorization of the chart restriction of `ℐᵏ𝒢 ⟶ 𝒢`. -/
theorem chartAlphaSheaf_val_app_openChartOfComparisonOver_apply
    (hZt : B.Contains (⊤_ Scheme.{u})) (hNo : IsNoetherian B S hS hZt X.1)
    (hIq : I.toSheafOfModules.IsQuasicoherentOnSite) (hFq : F.IsQuasicoherentOnSite)
    (hG : IsCoherent B S hS X.1 X.2 G) (A : SmallEtale B S hS X.1) (k : ℕ)
    (φ : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A) ⟶
      chartPush B S hS X F A)
    (V : (chartScheme A).Opens)
    (y : (chartPush B S hS X (idealPowModule I k G) A).val.obj (op V)) :
    ((chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A k φ).val.app
          (op (openChartOfComparisonOver B S hS X A V))).hom
        (chartPushEquiv B S hS X (idealPowModule I k G) A V y) =
      chartPushEquiv B S hS X F A V
        ((φ.val.app (op V)).hom
          (((chartPushFactor B S hS X I hIc G hIq hG.toIsQuasicoherentOnSite A k).val.app
            (op V)).hom y)) :=
  (chartSchemeModuleHomEquiv_symm_val_app_conj_apply' B S hS X (idealPowModule I k G) F
      (isQuasicoherentOnSite_idealPowModule B S hS X I G hZt hNo hIq hG k) hFq A V
      (chartPushFactor B S hS X I hIc G hIq hG.toIsQuasicoherentOnSite A k ≫ φ) _
      (chartAlphaComposite_assoc B S hS X I hIc G F hZt hNo hIq hFq hG A k φ) y).trans
    (congrArg
      (fun v : (chartPush B S hS X F A).val.obj (op V) => chartPushEquiv B S hS X F A V v)
      (chartPushFactor_comp_val_app_apply B S hS X I hIc G hIq hG.toIsQuasicoherentOnSite A k V
        φ y))

variable (θ : (restrictToIdealComplement B S hS X I).obj G ⟶
  (restrictToIdealComplement B S hS X I).obj F)

/-- **The morphism which [Stacks, Tag 01YB] produces on the chart's scheme, read on a section of
the chart restriction of `ℐᵏ𝒢` over a Zariski open off the support, is the transport of `θ`
there.**  The section is carried into `Iᵏ` times the chart restriction of `𝒢` by the
factorization, and over an open off the support that submodule is the whole of the chart
restriction, so the value is read off by
`Stacks.AlgebraicGeometry.IdealPowerColimit.overApp_homRestrict`. -/
theorem phi_val_app_chartPushFactor_apply
    (hIq : I.toSheafOfModules.IsQuasicoherentOnSite) (hGq : G.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) (k : ℕ)
    (φ : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A) ⟶
      chartPush B S hS X F A)
    (hφ : Stacks.AlgebraicGeometry.IdealPowerColimit.homRestrict
        (idealSheafDataOfChart B S hS X I hIc A)
        (Stacks.AlgebraicGeometry.IdealPowerColimit.disjoint_supportCompl_support
          (idealSheafDataOfChart B S hS X I hIc A)) φ =
      chartThetaOver B S hS X I hIc G F θ A)
    (V : (chartScheme A).Opens)
    (hV : V ≤ ((idealSheafDataOfChart B S hS X I hIc A).support.compl : (chartScheme A).Opens))
    (y : (chartPush B S hS X (idealPowModule I k G) A).val.obj (op V)) :
    (φ.val.app (op V)).hom
        (((chartPushFactor B S hS X I hIc G hIq hGq A k).val.app (op V)).hom y) =
      (chartTheta B S hS X I hIc G F θ A V hV).hom
        (((chartPushι B S hS X I G A k).val.app (op V)).hom y) :=
  have h1 := chartPushFactor_val_app_apply B S hS X I hIc G hIq hGq A k V y
  (congrArg
      (fun v : Γ(Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
          (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A), V) =>
        (φ.val.app (op V)).hom v) h1).trans
    ((Stacks.AlgebraicGeometry.Scheme.Modules.app_apply φ V _).symm.trans
      ((Stacks.AlgebraicGeometry.IdealPowerColimit.overApp_homRestrict
            (idealSheafDataOfChart B S hS X I hIc A)
            (Stacks.AlgebraicGeometry.IdealPowerColimit.disjoint_supportCompl_support
              (idealSheafDataOfChart B S hS X I hIc A)) φ hV
            (((chartPushι B S hS X I G A k).val.app (op V)).hom y)).symm.trans
        ((congrArg
            (fun ω : (chartPush B S hS X G A).over
                  ((idealSheafDataOfChart B S hS X I hIc A).support.compl :
                    (chartScheme A).Opens) ⟶
                (chartPush B S hS X F A).over
                  ((idealSheafDataOfChart B S hS X I hIc A).support.compl :
                    (chartScheme A).Opens) =>
              Stacks.AlgebraicGeometry.IdealPowerColimit.overApp ω hV
                (((chartPushι B S hS X I G A k).val.app (op V)).hom y)) hφ).trans
          (overApp_chartThetaOver B S hS X I hIc G F θ A hV
            (((chartPushι B S hS X I G A k).val.app (op V)).hom y)))))

/-- **The base case of the component determination for the chart transport of
[Stacks, Tag 07UM]**: the component of `AlgebraicGeometry.Space.chartAlpha` at the object of the
slice which a Zariski open of the chart's scheme off the support cuts out is the transport of `θ`
there, precomposed with the inclusion `ℐᵏ𝒢 ⟶ 𝒢`. -/
theorem chartAlphaSheaf_val_app_eq_homOnChart
    (hZt : B.Contains (⊤_ Scheme.{u})) (hNo : IsNoetherian B S hS hZt X.1)
    (hIq : I.toSheafOfModules.IsQuasicoherentOnSite) (hFq : F.IsQuasicoherentOnSite)
    (hG : IsCoherent B S hS X.1 X.2 G) (A : SmallEtale B S hS X.1) (k : ℕ)
    (φ : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A) ⟶
      chartPush B S hS X F A)
    (hφ : Stacks.AlgebraicGeometry.IdealPowerColimit.homRestrict
        (idealSheafDataOfChart B S hS X I hIc A)
        (Stacks.AlgebraicGeometry.IdealPowerColimit.disjoint_supportCompl_support
          (idealSheafDataOfChart B S hS X I hIc A)) φ =
      chartThetaOver B S hS X I hIc G F θ A)
    (V : (chartScheme A).Opens)
    (hV : V ≤ ((idealSheafDataOfChart B S hS X I hIc A).support.compl : (chartScheme A).Opens))
    (hpc : pc B S hS X I (idealComplementChart B S hS X I hIc A V hV) =
      openChartOfComparison B S hS X A V)
    (y : (chartPush B S hS X (idealPowModule I k G) A).val.obj (op V)) :
    ((chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A k φ).val.app
          (op (openChartOfComparisonOver B S hS X A V))).hom
        (chartPushEquiv B S hS X (idealPowModule I k G) A V y) =
      (homOnChart B S hS X I G F θ hpc).hom
        (((idealPowModuleι I k G).val.app (op (openChartOfComparison B S hS X A V))).hom
          (chartPushEquiv B S hS X (idealPowModule I k G) A V y)) :=
  have hg : ((chartPushι B S hS X I G A k).val.app (op V)).hom y =
      ((idealPowModuleι I k G).val.app (op (openChartOfComparison B S hS X A V))).hom
        (chartPushEquiv B S hS X (idealPowModule I k G) A V y) :=
    (chartPushEquiv_apply B S hS X G A V
        (((chartPushι B S hS X I G A k).val.app (op V)).hom y)).symm.trans
      (chartPushEquiv_chartPushι_apply B S hS X I G A k V y)
  (chartAlphaSheaf_val_app_openChartOfComparisonOver_apply B S hS X I hIc G F hZt hNo hIq hFq
        hG A k φ V y).trans
    ((chartPushEquiv_apply B S hS X F A V _).trans
      ((phi_val_app_chartPushFactor_apply B S hS X I hIc G F θ hIq
            hG.toIsQuasicoherentOnSite A k φ hφ V hV y).trans
        ((chartTheta_apply B S hS X I hIc G F θ A V hV
            (((chartPushι B S hS X I G A k).val.app (op V)).hom y)).trans
          (congrArg
            (fun v : (ModuleCat.restrictScalars (chartSectionsRingHom B S hS X A V)).obj
                (G.val.obj (op (openChartOfComparison B S hS X A V))) =>
              (homOnChart B S hS X I G F θ hpc).hom v) hg))))

/-- `AlgebraicGeometry.Space.chartAlphaSheaf_val_app_eq_homOnChart` at an arbitrary section of
`ℐᵏ𝒢` over the étale chart which the Zariski open cuts out: the sections identification of the
direct-image spelling is bijective. -/
theorem chartAlphaSheaf_val_app_eq_homOnChart'
    (hZt : B.Contains (⊤_ Scheme.{u})) (hNo : IsNoetherian B S hS hZt X.1)
    (hIq : I.toSheafOfModules.IsQuasicoherentOnSite) (hFq : F.IsQuasicoherentOnSite)
    (hG : IsCoherent B S hS X.1 X.2 G) (A : SmallEtale B S hS X.1) (k : ℕ)
    (φ : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A) ⟶
      chartPush B S hS X F A)
    (hφ : Stacks.AlgebraicGeometry.IdealPowerColimit.homRestrict
        (idealSheafDataOfChart B S hS X I hIc A)
        (Stacks.AlgebraicGeometry.IdealPowerColimit.disjoint_supportCompl_support
          (idealSheafDataOfChart B S hS X I hIc A)) φ =
      chartThetaOver B S hS X I hIc G F θ A)
    (V : (chartScheme A).Opens)
    (hV : V ≤ ((idealSheafDataOfChart B S hS X I hIc A).support.compl : (chartScheme A).Opens))
    (hpc : pc B S hS X I (idealComplementChart B S hS X I hIc A V hV) =
      openChartOfComparison B S hS X A V)
    (w : (idealPowModule I k G).val.obj (op (openChartOfComparison B S hS X A V))) :
    ((chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A k φ).val.app
          (op (openChartOfComparisonOver B S hS X A V))).hom w =
      (homOnChart B S hS X I G F θ hpc).hom
        (((idealPowModuleι I k G).val.app (op (openChartOfComparison B S hS X A V))).hom w) := by
  obtain ⟨y, hy⟩ := (chartPushEquiv B S hS X (idealPowModule I k G) A V).surjective w
  subst hy
  exact chartAlphaSheaf_val_app_eq_homOnChart B S hS X I hIc G F θ hZt hNo hIq hFq hG A k φ hφ
    V hV hpc y

/-- **The transport of the base case across the identification of the two spellings of the object
of the slice which a Zariski open of the chart's scheme cuts out.**  The object of the slice and
its identification are parameters, so that the whole statement is carried by a `subst`. -/
theorem val_app_eq_homOnChart_of_over_eq (k : ℕ) (A : SmallEtale B S hS X.1)
    (α : (asStructureSheafModule B S hS X (idealPowModule I k G)).over A ⟶
      (asStructureSheafModule B S hS X F).over A)
    (V : (chartScheme A).Opens)
    {P : SmallEtale B S hS (idealComplement B S hS X I).1}
    (ZO : CategoryTheory.Over A) (hZ : openChartOfComparisonOver B S hS X A V = ZO)
    (hpc : pc B S hS X I P = ZO.left)
    (hb : ∀ (hpc' : pc B S hS X I P = (openChartOfComparisonOver B S hS X A V).left)
        (w : (idealPowModule I k G).val.obj
          (op (openChartOfComparisonOver B S hS X A V).left)),
        (α.val.app (op (openChartOfComparisonOver B S hS X A V))).hom w =
          (homOnChart B S hS X I G F θ hpc').hom
            (((idealPowModuleι I k G).val.app
              (op (openChartOfComparisonOver B S hS X A V).left)).hom w))
    (y : (idealPowModule I k G).val.obj (op ZO.left)) :
    (α.val.app (op ZO)).hom y =
      (homOnChart B S hS X I G F θ hpc).hom
        (((idealPowModuleι I k G).val.app (op ZO.left)).hom y) := by
  subst hZ
  exact hb hpc y

/-- **The base case of the component determination, at the spelling
`Over.mk (openChartInclusion … A V)` of the object of the slice.**  This is exactly the hypothesis
`hbase` of `AlgebraicGeometry.Space.chartAlpha_val_app_eq_homOnChart`. -/
theorem chartAlphaSheaf_val_app_openChartInclusion_eq_complementHomOnChart
    (hZt : B.Contains (⊤_ Scheme.{u})) (hNo : IsNoetherian B S hS hZt X.1)
    (hIq : I.toSheafOfModules.IsQuasicoherentOnSite) (hFq : F.IsQuasicoherentOnSite)
    (hG : IsCoherent B S hS X.1 X.2 G) (A : SmallEtale B S hS X.1) (k : ℕ)
    (φ : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A) ⟶
      chartPush B S hS X F A)
    (hφ : Stacks.AlgebraicGeometry.IdealPowerColimit.homRestrict
        (idealSheafDataOfChart B S hS X I hIc A)
        (Stacks.AlgebraicGeometry.IdealPowerColimit.disjoint_supportCompl_support
          (idealSheafDataOfChart B S hS X I hIc A)) φ =
      chartThetaOver B S hS X I hIc G F θ A)
    (V : (chartScheme A).Opens)
    (hV : V ≤ ((idealSheafDataOfChart B S hS X I hIc A).support.compl : (chartScheme A).Opens))
    (y : (idealPowModule I k G).val.obj (op (openChart B S hS X.1 A V))) :
    ((chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A k φ).val.app
          (op (Over.mk (openChartInclusion B S hS X.1 A V)))).hom y =
      (complementHomOnChart B S hS X I G F θ hIc A V hV).hom
        (((idealPowModuleι I k G).val.app (op (openChart B S hS X.1 A V))).hom y) :=
  val_app_eq_homOnChart_of_over_eq B S hS X I G F θ k A
    (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A k φ) V
    (Over.mk (openChartInclusion B S hS X.1 A V))
    (openChartOfComparisonOver_eq B S hS X A V)
    (pc_idealComplementChart B S hS X I hIc A V hV)
    (fun hpc' w =>
      chartAlphaSheaf_val_app_eq_homOnChart' B S hS X I hIc G F θ hZt hNo hIq hFq hG A k φ hφ
        V hV hpc' w)
    y

/-- **The component determination for the morphism which the chart transport of
[Stacks, Tag 07UM] produces, with its base case discharged.**  For every étale chart `Z` of `X`
lying over `U = X ∖ V(ℐ)` and every morphism `h : Z ⟶ A`, the component of
`AlgebraicGeometry.Space.chartAlpha` at `h` is the transport of `θ` at `Z`, precomposed with the
inclusion `ℐᵏ𝒢 ⟶ 𝒢`.

The base case is `AlgebraicGeometry.Space.chartAlphaSheaf_val_app_eq_homOnChart`; the passage
from it to an arbitrary chart over `U` is
`AlgebraicGeometry.Space.chartAlpha_val_app_eq_homOnChart`. -/
theorem chartAlphaSheaf_val_app_eq_homOnChart_of_homRestrict
    (hZt : B.Contains (⊤_ Scheme.{u})) (hNo : IsNoetherian B S hS hZt X.1)
    (hIq : I.toSheafOfModules.IsQuasicoherentOnSite) (hFq : F.IsQuasicoherentOnSite)
    (hG : IsCoherent B S hS X.1 X.2 G) (A : SmallEtale B S hS X.1) (k : ℕ)
    (φ : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A) ⟶
      chartPush B S hS X F A)
    (hφ : Stacks.AlgebraicGeometry.IdealPowerColimit.homRestrict
        (idealSheafDataOfChart B S hS X I hIc A)
        (Stacks.AlgebraicGeometry.IdealPowerColimit.disjoint_supportCompl_support
          (idealSheafDataOfChart B S hS X I hIc A)) φ =
      chartThetaOver B S hS X I hIc G F θ A)
    {P : SmallEtale B S hS (idealComplement B S hS X I).1} {Z : SmallEtale B S hS X.1}
    (hP : pc B S hS X I P = Z) (h : Z ⟶ A)
    (y : (idealPowModule I k G).val.obj (op Z)) :
    ((chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A k φ).val.app
        (op (Over.mk h))).hom y =
      (homOnChart B S hS X I G F θ hP).hom
        (((idealPowModuleι I k G).val.app (op Z)).hom y) :=
  chartAlpha_val_app_eq_homOnChart B S hS X I hIc G F θ hZt hNo hIq hFq hG A k φ
    (fun V hV y =>
      chartAlphaSheaf_val_app_openChartInclusion_eq_complementHomOnChart
        B S hS X I hIc G F θ hZt hNo hIq hFq hG A k φ hφ V hV y)
    hP h y

end ChartAlpha

end AlgebraicGeometry.Space

end
