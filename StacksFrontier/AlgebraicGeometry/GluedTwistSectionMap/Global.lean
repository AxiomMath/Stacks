module

public import StacksFrontier.AlgebraicGeometry.GluedTwistAlgebra.Basic
public import StacksFrontier.AlgebraicGeometry.GluedTwistSectionMap.Basic
public import StacksFrontier.Topology.Sheaves.Basis.ModuleHomOnBasis

/-!
# Tag 01NR's homogeneous-section map for the glued twists, globally

`Stacks.AlgebraicGeometry.GluedTwistSectionMap.mk` reduces
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` — the structure Stacks Tag 01NR asserts
the existence of — to three fields: a graded algebra `B` on the relative projective spectrum whose
homogeneous pieces are identified with the glued twists
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.gluedTwist`, the condition that those
identifications respect the product and the unit, and a homogeneous-section map `ψ` for the glued
twists satisfying the chart description
`Stacks.AlgebraicGeometry.GluedTwistSectionMap.PsiGluedChart`.

**This file constructs that map and proves its chart description**, so that Tag 01NR's twist datum
is reduced to the graded algebra alone.

`GluedTwistSectionMap/Basic.lean` built the map over a *single* affine open of the base as a
`Γ(S, U)`-linear map `psiGluedAffine`, and recorded that what was missing was the compatibility of
those components with restriction between two affine opens. That compatibility is
`gluedDegreeSection_resPiece` below; the affine opens of a scheme form a basis of its topology, so
Tag 009U's morphism-from-a-basis `Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis`
assembles the components into a morphism of sheaves of modules on the base.

## Main definitions

* `Stacks.AlgebraicGeometry.GluedTwistSectionMap.psiGlued`: **the homogeneous-section map of the
  glued twists**, a morphism `A.piece n ⟶ (pushforward toBase).obj (gluedTwist A n)` of sheaves of
  modules on the base, for every natural number `n`.
* `Stacks.AlgebraicGeometry.GluedTwistSectionMap.mkOfGradedAlgebra`: **Tag 01NR's twist datum from
  the graded algebra alone.**

## Main results

* `Stacks.AlgebraicGeometry.GluedTwistSectionMap.gluedChartIso_inv_app`: **the chart
  identification of the glued twist, on sections.** The inverse of
  `Stacks.Tag01VMVeryAmple.gluedChartIso` acts by
  `Stacks.AlgebraicGeometry.SchemeModuleGlue.chartSectionEquiv`. This is the value lemma for
  `Stacks.AlgebraicGeometry.ChartTransNonNested.ModelData.chartIso` that the tree did not have,
  and it is reusable by anything that has to compute with a sheaf of modules glued from local
  models; see the implementation notes for why it is *not* a single `rfl`.
* `Stacks.AlgebraicGeometry.GluedTwistSectionMap.meetLoc_resTop_degreeSection` and
  `cmpGen_resTop_degreeSection`: **Tag 01NO's twist comparison for a nested pair of affine opens
  of the base, on the homogeneous global sections of Tag 01MP.**
  `Stacks.AlgebraicGeometry.ChartTransRelativeProj.cmpNested_resTop_degreeSection` is this for the
  *nested* comparison; these lift it to the glued comparison `cmpGen`, which is the one the local
  models of the glued twist are built from.
* `Stacks.AlgebraicGeometry.GluedTwistSectionMap.trans_resTop_degreeSection`: the model transition
  of the glued twist carries the degree-`n` homogeneous section attached to a homogeneous element
  over the larger affine open to the one attached to its restriction.
* `Stacks.AlgebraicGeometry.GluedTwistSectionMap.gluedDegreeSection_resPiece`: **the restriction
  compatibility.** For affine opens `W ⊆ U` of the base, the degree-`n` homogeneous section of the
  glued twist attached to the restriction of a local section of the base algebra is the
  restriction of the one attached to the section itself. This is exactly
  `Stacks.BasisRestriction.IsCompatibleOnBasis` for the family of affine opens.
* `Stacks.AlgebraicGeometry.GluedTwistSectionMap.psiGluedChart`: `psiGlued` satisfies the chart
  description.

## Implementation notes

**The chart identification on sections is two steps, not one.**
`Stacks.Tag01VMVeryAmple.gluedChartIso` is by definition
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.chartIso`, which is by definition
`ModelData.chartIso`, which is by definition
`Stacks.AlgebraicGeometry.SchemeModuleGlue.chartIso`, whose two value lemmas `chartIso_hom_app`
and `chartIso_inv_app` are `rfl`. One might therefore expect `gluedChartIso_inv_app` to be
`SchemeModuleGlue.chartIso_inv_app` outright. It is not: the elaborator accepts that term, but the
**kernel** then exceeds its deterministic timeout, because `gluedChartIso`'s declared type is
spelled through `gluedTwist` and `twistingSheaf` while `chartIso_inv_app`'s is spelled through
`modelData`'s own fields, and reconciling the two underneath an `app` is too much at once. Split
into `gluedChartIso_eq`, an equality of *isomorphisms* proved by `rfl` — where the same
reconciliation is cheap, exactly as the implementation note at `ChartTransRelativeProj.chartIso`
records — followed by the library's value lemma at the `modelData` spelling, it goes through.
`restrictAppIso_chartSectionEquiv_top_symm` then carries the result to `chartSections`, which is
`Stacks.AlgebraicGeometry.SchemeModuleGlue.chartSectionsLinearEquiv`: these differ by the
`eqToHom` transport along `chart ⁻¹ᵁ (chart ''ᵁ V) = V`, which at `V = ⊤` is the restriction from
the top open because morphisms of opens are unique.

**`meetLoc` is cancelled through `modelPair_app`, and its index is a variable.** Two measurements,
both instances of the discipline the implementation notes of
`ChartTransNonNested/RelativeProj.lean` record. The member of `meetIndex W U` must be a variable
and not an anonymous constructor:
otherwise the two instances of `cmpNested_resTop_degreeSection` cannot be joined, the match driving
the elaborator through `cmpNested` into the pushforward of the twist until the recursion limit is
reached. And the cancellation of the member's two nested comparisons is taken by transporting
`meetLoc_eq` under `app` with `congrArg` and then applying `modelPair_app`, rather than by
`isComposite_meetLoc` followed by injectivity: the latter is an instance of the generic predicate
`IsComposite`, and reconciling it with a concrete chain of equations exhausts the recursion limit
too.

**No glued comparison over an affine open and itself is needed.** `ModelData.trans_app_of_le`
factors the model transition through *any* member of the refinement whose open contains the one in
question, so the transition from the chart over `m` to the chart over `l` is computed over a cover
by the inverse images of the affine opens `r` below both, where it is the composite of
`cmpGen A r m` and `cmpGen A r l` — both of them comparisons for a *strictly* nested pair. The
earlier plan for this file instead took `r = l`, which needs `cmpGen A l l` to be the identity, a
statement that does not exist in the tree and whose proof runs into the recursion limit by the
route above.

**The pushforward's restriction map is reached through `presheaf`.**
`AlgebraicGeometry.Scheme.Modules.pushforward_obj_presheaf_map` identifies it with the module's
own restriction map between the inverse images, and `ChartTransRelativeProj.map_eq_map` then
absorbs the difference between that morphism of opens and the one named by the containment. Going
at the same statement through `val.map` instead exceeds the kernel's deterministic timeout.

**Every delta step that crosses a spelling is taken in a statement with no other content.**
`gluedDegreeSection_eq`, `gluedChartIso_eq` and `psiGlued_app'` exist for that reason alone — as
does `Stacks.AlgebraicGeometry.GluedTwistAlgebra.modelData_cmp`, used below;
`psiGluedAffineHom` is built with `CategoryTheory.ConcreteCategory.ofHom` rather than
`ModuleCat.ofHom`, since the latter wraps its source and target in `ModuleCat.of` and the module
structure on the sections of a direct image is then no longer found.

## What is not done here

**No `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` is built.** `mkOfGradedAlgebra` still
takes three arguments: a graded algebra `B` on the relative projective spectrum, an identification
`e` of its homogeneous pieces with the glued twists, and
`Stacks.AlgebraicGeometry.RelativeProjTwists.IsGradedChartIso` for the resulting chart datum.
Nothing here constructs `B`, its multiplication, its unit, or that last condition. Tag 01NR's
existence assertion is earned only by a term of `TwistData`, so no `stacks` attribute is attached.

The `ψ` side of Tag 01NR is, however, complete: `psiGlued` is a genuine morphism of sheaves of
modules in every degree, and `psiGluedChart` is its chart description. The remaining
`GluedTwistSectionMap.mk` fields are all about the algebra.

`cover`, `chartModule`, `chartSections`, `chartSections_resLE`, `trans_chartSections`,
`modelData_cmp` and `trans_app_cmpGen` are `Stacks.AlgebraicGeometry.GluedTwistAlgebra`'s, opened
by name above. All seven were once restated here, while that file did not compile; it compiles
now, and the duplication is gone.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ChartTransNonNested
open Stacks.AlgebraicGeometry.ChartTransRelativeProj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.GluedTwistAlgebra
  (cover chartModule chartSections chartSections_resLE trans_chartSections modelData_cmp
    trans_app_cmpGen)

namespace Stacks.AlgebraicGeometry.GluedTwistSectionMap

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}

/-- The chart over an affine open of the base is an open immersion. This is
`Stacks.AlgebraicGeometry.RelativeProjTwistGlue.isOpenImmersion_chart` restated with the affine
open presented as a member of `Scheme.affineOpens`, at which spelling that instance does not
fire. -/
public instance chartOI (A : SheafGradedAlgebra S) (m : S.affineOpens) :
    IsOpenImmersion ((relativeProj A).chart (m.1 : S.Opens) m.2) :=
  RelativeProjTwistGlue.isOpenImmersion_chart (relativeProj A) (m.1 : S.Opens) m.2

/-- The restriction of a global section of the absolute twist on a chart, read as a section of
the chart module. -/
public abbrev chartResTop (A : SheafGradedAlgebra S) (n : ℤ) (m : S.affineOpens)
    (W : (relativeProj A).scheme.Opens)
    (t : (twistingSheaf (A.grading (m.1 : S.Opens)) n).val.obj (op ⊤)) :
    (chartModule A n m).obj (op W) :=
  resTop (A.grading (m.1 : S.Opens)) n ((relativeProj A).chart (m.1 : S.Opens) m.2 ⁻¹ᵁ W) t

/-! ### The chart identification of the glued twist on sections -/

/-- The chart identification `Tag01VMVeryAmple.gluedChartIso` of the glued twist over an affine
open of the base is the chart isomorphism `ChartTransRelativeProj.chartIso` of the model gluing
datum, by definition. Stated on its own so that this delta step, which crosses a spelling, is taken
in a statement with no other content. -/
public theorem gluedChartIso_eq (n : ℤ) (hcoc : IsNestedCocycle A n) (m : S.affineOpens) :
    Tag01VMVeryAmple.gluedChartIso A n hcoc (m.1 : S.Opens) m.2
      = ChartTransRelativeProj.chartIso A n hcoc m (hchart := chartOI A m) :=
  rfl

/-- On sections over an open `V` of the chart, the inverse of the chart identification of the
glued twist over an affine open `m` is the inverse of the model gluing datum's chart section
equivalence `SchemeModuleGlue.chartSectionEquiv`. -/
public theorem gluedChartIso_inv_app (n : ℤ) (hcoc : IsNestedCocycle A n) (m : S.affineOpens)
    (V : (AlgebraicGeometry.Proj (A.grading (m.1 : S.Opens))).Opens)
    (a : (twistingSheaf (A.grading (m.1 : S.Opens)) n).val.obj (op V)) :
    (Tag01VMVeryAmple.gluedChartIso A n hcoc (m.1 : S.Opens) m.2).inv.val.app (op V) a
      = (SchemeModuleGlue.chartSectionEquiv (modelData A n hcoc).toChartGlueData m
          (hom_isOpenImmersion := chartOI A m)
          (RelativeProjTwistGlue.chart_image_top (relativeProj A) (m.1 : S.Opens) m.2).le
          V).symm a := by
  rw [gluedChartIso_eq]
  exact SchemeModuleGlue.chartIso_inv_app (modelData A n hcoc).toChartGlueData m
    (hom_isOpenImmersion := chartOI A m)
    (RelativeProjTwistGlue.chart_image_top (relativeProj A) (m.1 : S.Opens) m.2).le V a

/-- On global sections of the chart, restricting along the chart the section of the glued twist
given by the inverse chart section equivalence is the inverse of `chartSections` at the
restriction `chartResTop` of the section. The two equivalences differ by the transport along
`chart ⁻¹ᵁ (chart ''ᵁ ⊤) = ⊤`, which is the restriction from the top open. -/
public theorem restrictAppIso_chartSectionEquiv_top_symm (n : ℤ) (hcoc : IsNestedCocycle A n)
    (m : S.affineOpens)
    (hV : (relativeProj A).chart (m.1 : S.Opens) m.2 ''ᵁ
        (⊤ : (AlgebraicGeometry.Proj (A.grading (m.1 : S.Opens))).Opens) ≤ cover A m)
    (t : (twistingSheaf (A.grading (m.1 : S.Opens)) n).val.obj (op ⊤)) :
    (Scheme.Modules.restrictAppIso ((relativeProj A).chart (m.1 : S.Opens) m.2)
          (gluedTwist A n hcoc) ⊤).hom
        ((SchemeModuleGlue.chartSectionEquiv (modelData A n hcoc).toChartGlueData m
          (hom_isOpenImmersion := chartOI A m)
          (RelativeProjTwistGlue.chart_image_top (relativeProj A) (m.1 : S.Opens) m.2).le
          ⊤).symm t)
      = (chartSections A n hcoc m hV).symm (chartResTop A n m _ t) :=
  rfl

/-- The glued section map over an affine open `m` of the base, on a global section `t` of the
chart's own twist, is the inverse of `chartSections` at the restriction `chartResTop` of `t`. -/
public theorem gluedMapSection_top_eq (n : ℤ) (hcoc : IsNestedCocycle A n) (m : S.affineOpens)
    (hV : (relativeProj A).chart (m.1 : S.Opens) m.2 ''ᵁ
        (⊤ : (AlgebraicGeometry.Proj (A.grading (m.1 : S.Opens))).Opens) ≤ cover A m)
    (t : (twistingSheaf (A.grading (m.1 : S.Opens)) n).val.obj (op ⊤)) :
    gluedMapSection n hcoc (m.1 : S.Opens) m.2 ⊤ t
      = (chartSections A n hcoc m hV).symm (chartResTop A n m _ t) :=
  (congrArg (fun z => (Scheme.Modules.restrictAppIso
        ((relativeProj A).chart (m.1 : S.Opens) m.2) (gluedTwist A n hcoc) ⊤).hom z)
    (gluedChartIso_inv_app n hcoc m ⊤ t)).trans
    (restrictAppIso_chartSectionEquiv_top_symm n hcoc m hV t)

/-- `chartSections` carries the glued section map over an affine open `m` of the base, on a
global section `t` of the chart's own twist, to the restriction `chartResTop` of `t`. -/
public theorem chartSections_gluedMapSection_top (n : ℤ) (hcoc : IsNestedCocycle A n)
    (m : S.affineOpens)
    (hV : (relativeProj A).chart (m.1 : S.Opens) m.2 ''ᵁ
        (⊤ : (AlgebraicGeometry.Proj (A.grading (m.1 : S.Opens))).Opens) ≤ cover A m)
    (t : (twistingSheaf (A.grading (m.1 : S.Opens)) n).val.obj (op ⊤)) :
    chartSections A n hcoc m hV (gluedMapSection n hcoc (m.1 : S.Opens) m.2 ⊤ t)
      = chartResTop A n m _ t :=
  (congrArg (chartSections A n hcoc m hV) (gluedMapSection_top_eq n hcoc m hV t)).trans
    (LinearEquiv.apply_symm_apply _ _)


/-! ### The glued comparison of Tag 01NO on the homogeneous global sections -/

/-- In the pushforward of the twist along a chart, restricting from `V` to a smaller open `V₀`
the restriction of a global section to the inverse image of `V` gives its restriction to the
inverse image of `V₀`. -/
public theorem resLE_resTop (n : ℤ) (U : S.Opens) (hU : IsAffineOpen U)
    {V V₀ : (relativeProj A).scheme.Opens} (hV₀ : V₀ ≤ V)
    (t : (twistingSheaf (A.grading U) n).val.obj (op ⊤)) :
    (pushforwardVal ((relativeProj A).chart U hU) (twistingSheaf (A.grading U) n)).resLE hV₀
        (resTop (A.grading U) n ((relativeProj A).chart U hU ⁻¹ᵁ V) t)
      = resTop (A.grading U) n ((relativeProj A).chart U hU ⁻¹ᵁ V₀) t :=
  map_map_eq_map (twistingSheaf (A.grading U) n).val _ _ _ t

/-- Restricting a homogeneous element along `W ≤ U` is restricting it along `W ≤ V ≤ U` in two
steps, on the homogeneous global sections of Tag 01MP over any open of the chart. -/
private theorem resTop_degreeSection_res_comp (k : ℕ) {W V U : S.Opens} (hWV : W ≤ V)
    (hVU : V ≤ U) (hW : IsAffineOpen W) (O : (relativeProj A).scheme.Opens)
    (c : (A.grading U) k) :
    resTop (A.grading W) (k : ℤ) ((relativeProj A).chart W hW ⁻¹ᵁ O)
        (degreeSection (A.grading W) k ⟨A.res (hWV.trans hVU) c, (A.res _).map_mem c.2⟩)
      = resTop (A.grading W) (k : ℤ) ((relativeProj A).chart W hW ⁻¹ᵁ O)
          (degreeSection (A.grading W) k ⟨A.res hWV (⟨A.res hVU c, (A.res hVU).map_mem c.2⟩ :
            (A.grading V) k), (A.res hWV).map_mem ((A.res hVU).map_mem c.2)⟩) :=
  congrArg (fun z : (A.grading W) k =>
    resTop (A.grading W) (k : ℤ) ((relativeProj A).chart W hW ⁻¹ᵁ O) (degreeSection _ k z))
    (Subtype.ext (RingHom.congr_fun (A.resRingHom_comp hWV hVU) c.1))

/-- **The comparison over one member of the cover, on a homogeneous global section.** For affine
opens `W ⊆ U` of the base and a member `p` of the family of affine opens of the base below both,
`meetLoc` carries the degree-`k` homogeneous section of Tag 01MP attached to a homogeneous element
of the graded ring of sections over `U` to the one attached to its restriction to `W`.

`meetLoc` is the cancellation of the member's own two nested comparisons, each of which computes
on these sections by `cmpNested_resTop_degreeSection`; what is left is that restricting from `U`
to `W` and then to `p` is restricting from `U` to `p`, which is
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.resRingHom_comp`.

Two measurements shape the proof. The member is a **variable** of `meetIndex W U`, not an
anonymous constructor: with the latter spelling the two instances of
`cmpNested_resTop_degreeSection` cannot be joined, the match driving the elaborator through
`cmpNested` into the pushforward of the twist until the recursion limit is reached. And the
cancellation is taken through `modelPair_app` rather than through `isComposite_meetLoc` followed
by injectivity of the second comparison: the latter is the generic predicate `IsComposite` and
reconciling its instance with a concrete chain of equations exhausts the recursion limit too. -/
public theorem meetLoc_resTop_degreeSection (k : ℕ) (W U : S.Opens) (h : W ≤ U)
    (hW : IsAffineOpen W) (hU : IsAffineOpen U) (p : meetIndex W U) (c : (A.grading U) k)
    (V : (relativeProj A).scheme.Opens)
    (hVp : V ≤ (relativeProj A).toBase ⁻¹ᵁ (p.1.1 : S.Opens)) :
    (meetLoc A W U hW hU (k : ℤ) p).app V hVp
        (resTop (A.grading U) (k : ℤ) ((relativeProj A).chart U hU ⁻¹ᵁ V)
          (degreeSection (A.grading U) k c))
      = resTop (A.grading W) (k : ℤ) ((relativeProj A).chart W hW ⁻¹ᵁ V)
          (degreeSection (A.grading W) k ⟨A.res h c, (A.res h).map_mem c.2⟩) := by
  have hpW : (p.1.1 : S.Opens) ≤ W := p.2.trans inf_le_left
  have hpU : (p.1.1 : S.Opens) ≤ U := p.2.trans inf_le_right
  have h2 := cmpNested_resTop_degreeSection A (p.1.1 : S.Opens) U hpU p.1.2 hU k c V hVp
  have h3 := cmpNested_resTop_degreeSection A (p.1.1 : S.Opens) W hpW p.1.2 hW k
    ⟨A.res h c, (A.res h).map_mem c.2⟩ V hVp
  have h6 := h2.trans
    ((resTop_degreeSection_res_comp k hpW h p.1.2 V c).trans h3.symm)
  refine Eq.trans (congrArg (fun e : TopCat.Sheaf.LocalModuleEquiv
        (pushforwardVal ((relativeProj A).chart U hU) (twistingSheaf (A.grading U) (k : ℤ)))
        (pushforwardVal ((relativeProj A).chart W hW) (twistingSheaf (A.grading W) (k : ℤ)))
        ((relativeProj A).toBase ⁻¹ᵁ (p.1.1 : S.Opens)) =>
      e.app V hVp (resTop (A.grading U) (k : ℤ) ((relativeProj A).chart U hU ⁻¹ᵁ V)
        (degreeSection (A.grading U) k c)))
    (meetLoc_eq A W U hW hU (k : ℤ) p hpW hpU)) ?_
  refine Eq.trans (modelPair_app
    (cmpNested A (p.1.1 : S.Opens) U hpU p.1.2 hU (k : ℤ))
    (cmpNested A (p.1.1 : S.Opens) W hpW p.1.2 hW (k : ℤ)) V hVp _) ?_
  refine Eq.trans (congrArg
    ((cmpNested A (p.1.1 : S.Opens) W hpW p.1.2 hW (k : ℤ)).app V hVp).symm h6) ?_
  exact LinearEquiv.symm_apply_apply _ _

/-- **Tag 01NO's glued comparison on a homogeneous global section.** For affine opens `W ⊆ U` of
the base, the comparison for the pair carries the degree-`k` homogeneous section of Tag 01MP
attached to a homogeneous element of the graded ring of sections over `U` to the one attached to
its restriction to `W`, over every open inside the inverse image of `W`.

Checked on the cover of that open by the inverse images of the affine opens of the base below
both: over such a member the glued comparison is that member's own `meetLoc`
(`cmpGen_agreeOn_meetLoc`), where `meetLoc_resTop_degreeSection` applies, and both sides commute
with the restriction maps. -/
public theorem cmpGen_resTop_degreeSection (k : ℕ) (W U : S.Opens) (h : W ≤ U)
    (hW : IsAffineOpen W) (hU : IsAffineOpen U)
    (hpre : (relativeProj A).toBase ⁻¹ᵁ W ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (hcoc : IsNestedCocycle A (k : ℤ)) (c : (A.grading U) k)
    (V : (relativeProj A).scheme.Opens) (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ W) :
    (cmpGen A W U hW hU (k : ℤ) hpre hcoc).app V hV
        (resTop (A.grading U) (k : ℤ) ((relativeProj A).chart U hU ⁻¹ᵁ V)
          (degreeSection (A.grading U) k c))
      = resTop (A.grading W) (k : ℤ) ((relativeProj A).chart W hW ⁻¹ᵁ V)
          (degreeSection (A.grading W) k ⟨A.res h c, (A.res h).map_mem c.2⟩) := by
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf (isSheaf_pushChart A W hW (k : ℤ))
    (fun r : {r : S.affineOpens // (r.1 : S.Opens) ≤ W ⊓ U} => V ⊓ cover A r.1)
    (fun _ => inf_le_left)
    (TopCat.Sheaf.le_iSup_inf_of_le (le_iSup_preimage_inf A W U V hV (hV.trans hpre)))
    fun r => ?_
  have hrW : (r.1.1 : S.Opens) ≤ W := r.2.trans inf_le_left
  have hrU : (r.1.1 : S.Opens) ≤ U := r.2.trans inf_le_right
  refine Eq.trans ((cmpGen A W U hW hU (k : ℤ) hpre hcoc).naturality hV inf_le_left _).symm ?_
  refine Eq.trans ?_ (resLE_resTop (k : ℤ) W hW (inf_le_left : V ⊓ cover A r.1 ≤ V)
    (degreeSection (A.grading W) k ⟨A.res h c, (A.res h).map_mem c.2⟩)).symm
  refine Eq.trans (congrArg ((cmpGen A W U hW hU (k : ℤ) hpre hcoc).app
      (V ⊓ cover A r.1) (inf_le_left.trans hV))
    (resLE_resTop (k : ℤ) U hU (inf_le_left : V ⊓ cover A r.1 ≤ V)
      (degreeSection (A.grading U) k c))) ?_
  refine Eq.trans (cmpGen_agreeOn_meetLoc A W U hW hU (k : ℤ) hpre hcoc r.1 hrW hrU
    (V ⊓ cover A r.1) (inf_le_left.trans hV) inf_le_right _) ?_
  exact meetLoc_resTop_degreeSection k W U h hW hU ⟨r.1, le_inf hrW hrU⟩ c
    (V ⊓ cover A r.1) inf_le_right


/-! ### The model transition on the homogeneous global sections -/

/-- **The model transition of the glued twist on a homogeneous global section.** For affine opens
`l ⊆ m` of the base, the transition from the chart over `m` to the chart over `l` carries the
degree-`k` homogeneous section of Tag 01MP attached to a homogeneous element of the graded ring of
sections over `m` to the one attached to its restriction to `l`.

Checked on the cover of the open by the inverse images of the affine opens `r` of the base below
both: over such a member the transition is the composite of the two glued comparisons
`cmpGen A r m` and `cmpGen A r l` (`trans_app_cmpGen`), both of which compute on these sections by
`cmpGen_resTop_degreeSection`, and the two restricted elements agree because restricting from `m`
to `l` and then to `r` is restricting from `m` to `r`. -/
public theorem trans_resTop_degreeSection (k : ℕ) (hcoc : IsNestedCocycle A (k : ℤ))
    (m l : S.affineOpens) (hlm : (l.1 : S.Opens) ≤ (m.1 : S.Opens))
    (c : (A.grading (m.1 : S.Opens)) k) {V : (relativeProj A).scheme.Opens}
    (hm : V ≤ cover A m) (hl : V ≤ cover A l) :
    (modelData A (k : ℤ) hcoc).trans m l hm hl
        (resTop (A.grading (m.1 : S.Opens)) (k : ℤ)
          ((relativeProj A).chart (m.1 : S.Opens) m.2 ⁻¹ᵁ V)
          (degreeSection (A.grading (m.1 : S.Opens)) k c))
      = resTop (A.grading (l.1 : S.Opens)) (k : ℤ)
          ((relativeProj A).chart (l.1 : S.Opens) l.2 ⁻¹ᵁ V)
          (degreeSection (A.grading (l.1 : S.Opens)) k
            ⟨A.res hlm c, (A.res hlm).map_mem c.2⟩) := by
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf
    (isSheaf_pushChart A (l.1 : S.Opens) l.2 (k : ℤ))
    (fun r : {r : S.affineOpens // (r.1 : S.Opens) ≤ (l.1 : S.Opens) ⊓ (m.1 : S.Opens)} =>
      V ⊓ cover A r.1)
    (fun _ => inf_le_left)
    (TopCat.Sheaf.le_iSup_inf_of_le
      (le_iSup_preimage_inf A (l.1 : S.Opens) (m.1 : S.Opens) V hl hm)) fun r => ?_
  have hrl : (r.1.1 : S.Opens) ≤ (l.1 : S.Opens) := r.2.trans inf_le_left
  have hrm : (r.1.1 : S.Opens) ≤ (m.1 : S.Opens) := r.2.trans inf_le_right
  have hk : cover A r.1 ≤ cover A m ⊓ cover A l :=
    le_inf (((relativeProj A).toBase).preimage_mono hrm)
      (((relativeProj A).toBase).preimage_mono hrl)
  have hcm := cmpGen_resTop_degreeSection k (r.1.1 : S.Opens) (m.1 : S.Opens) hrm r.1.2 m.2
    (hk.trans inf_le_left) hcoc c (V ⊓ cover A r.1) inf_le_right
  have hcl := cmpGen_resTop_degreeSection k (r.1.1 : S.Opens) (l.1 : S.Opens) hrl r.1.2 l.2
    (hk.trans inf_le_right) hcoc ⟨A.res hlm c, (A.res hlm).map_mem c.2⟩
    (V ⊓ cover A r.1) inf_le_right
  have hres' := resTop_degreeSection_res_comp k hrl hlm r.1.2 (V ⊓ cover A r.1) c
  refine Eq.trans
    (((modelData A (k : ℤ) hcoc).trans_map m l hm hl (inf_le_left : V ⊓ cover A r.1 ≤ V) _)).symm
    ?_
  refine Eq.trans ?_ (resLE_resTop (k : ℤ) (l.1 : S.Opens) l.2
    (inf_le_left : V ⊓ cover A r.1 ≤ V)
    (degreeSection (A.grading (l.1 : S.Opens)) k
      ⟨A.res hlm c, (A.res hlm).map_mem c.2⟩)).symm
  refine Eq.trans (congrArg ((modelData A (k : ℤ) hcoc).trans m l
      (inf_le_left.trans hm) (inf_le_left.trans hl))
    (resLE_resTop (k : ℤ) (m.1 : S.Opens) m.2 (inf_le_left : V ⊓ cover A r.1 ≤ V)
      (degreeSection (A.grading (m.1 : S.Opens)) k c))) ?_
  refine Eq.trans (trans_app_cmpGen A (k : ℤ) hcoc m l r.1 hk inf_le_right
    (inf_le_left.trans hm) (inf_le_left.trans hl) _) ?_
  refine Eq.trans (congrArg
    ((cmpGen A (r.1.1 : S.Opens) (l.1 : S.Opens) r.1.2 l.2 (k : ℤ)
      (hk.trans inf_le_right) hcoc).app (V ⊓ cover A r.1) inf_le_right).symm
    (hcm.trans (hres'.trans hcl.symm))) ?_
  exact LinearEquiv.symm_apply_apply _ _


/-! ### The homogeneous section of the glued twist, read through the chart comparison -/

/-- **The transport of `pushTransport` through the chart comparison.** The open is a variable and
the transport is substituted away; what is carried across it is the computation of the chart
comparison at that open, which is why it appears as a hypothesis rather than inside the proof. -/
public theorem chartSections_pushTransport (n : ℤ) (hcoc : IsNestedCocycle A n)
    (m : S.affineOpens) {W : (relativeProj A).scheme.Opens} (hW : W = cover A m)
    (hV : W ≤ cover A m) (z : (gluedTwist A n hcoc).val.obj (op W))
    (t : (twistingSheaf (A.grading (m.1 : S.Opens)) n).val.obj (op ⊤))
    (hcs : chartSections A n hcoc m hV z = chartResTop A n m W t) :
    chartSections A n hcoc m (le_refl (cover A m))
        (pushTransport (gluedTwist A n hcoc) (m.1 : S.Opens) hW z)
      = chartResTop A n m (cover A m) t := by
  cases hW
  exact hcs

/-- The delta step unfolding `gluedDegreeSection`, taken in a statement whose two sides have the
same type so that the kernel reconciles the sections of the direct image with the sections of the
glued twist over the inverse image only once, in the `congrArg` below. -/
public theorem gluedDegreeSection_eq (hcoc : ∀ n : ℤ, IsNestedCocycle A n) (n : ℕ)
    (m : S.affineOpens) (a : A.sectionPieces (m.1 : S.Opens) n) :
    gluedDegreeSection A hcoc n (m.1 : S.Opens) m.2 a
      = pushTransport (gluedTwist A (n : ℤ) (hcoc (n : ℤ))) (m.1 : S.Opens)
          (RelativeProjTwistGlue.chart_image_top (relativeProj A) (m.1 : S.Opens) m.2)
          (gluedMapSection (n : ℤ) (hcoc (n : ℤ)) (m.1 : S.Opens) m.2 ⊤
            (degreeSection (A.grading (m.1 : S.Opens)) n
              ⟨DirectSum.of (A.sectionPieces (m.1 : S.Opens)) n a,
                A.of_mem_grading (m.1 : S.Opens) a⟩)) :=
  rfl

/-- **The degree-`n` homogeneous section of the glued twist, read through the chart comparison**
over the affine open it was built on: it is the absolute homogeneous section of Tag 01MP on that
chart. -/
public theorem chartSections_gluedDegreeSection (hcoc : ∀ n : ℤ, IsNestedCocycle A n) (n : ℕ)
    (m : S.affineOpens) (a : A.sectionPieces (m.1 : S.Opens) n) :
    chartSections A (n : ℤ) (hcoc (n : ℤ)) m (le_refl (cover A m))
        (gluedDegreeSection A hcoc n (m.1 : S.Opens) m.2 a)
      = chartResTop A (n : ℤ) m (cover A m)
          (degreeSection (A.grading (m.1 : S.Opens)) n
            ⟨DirectSum.of (A.sectionPieces (m.1 : S.Opens)) n a,
              A.of_mem_grading (m.1 : S.Opens) a⟩) :=
  (congrArg (chartSections A (n : ℤ) (hcoc (n : ℤ)) m (le_refl (cover A m)))
      (gluedDegreeSection_eq hcoc n m a)).trans
    (chartSections_pushTransport (n : ℤ) (hcoc (n : ℤ)) m
      (RelativeProjTwistGlue.chart_image_top (relativeProj A) (m.1 : S.Opens) m.2)
      (RelativeProjTwistGlue.chart_image_top (relativeProj A) (m.1 : S.Opens) m.2).le _ _
      (chartSections_gluedMapSection_top (n : ℤ) (hcoc (n : ℤ)) m
        (RelativeProjTwistGlue.chart_image_top (relativeProj A) (m.1 : S.Opens) m.2).le _))

/-- The restriction map of the direct image between two opens of the base is the restriction map
of the module between their inverse images. -/
public theorem pushforward_presheaf_map_eq_resLE (M : (relativeProj A).scheme.Modules)
    {U U' : S.Opens} (h : U' ≤ U)
    (hcov : (relativeProj A).toBase ⁻¹ᵁ U' ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (z : M.val.obj (op ((relativeProj A).toBase ⁻¹ᵁ U))) :
    ((Scheme.Modules.pushforward (relativeProj A).toBase).obj M).presheaf.map (homOfLE h).op z
      = M.val.resLE hcov z := by
  rw [Scheme.Modules.pushforward_obj_presheaf_map]
  exact map_eq_map M.val _ _ z

/-! ### The restriction compatibility -/

/-- **The homogeneous-section map of the glued twist commutes with restriction between affine
opens of the base.** This is `Stacks.BasisRestriction.IsCompatibleOnBasis` for the family of
affine opens, and it is the one statement that
`Stacks.AlgebraicGeometry.GluedTwistSectionMap.psiGluedAffine` was missing.

Both sides are compared through the chart comparison of the glued twist over the smaller open,
which is injective. On the left `chartSections_gluedDegreeSection` reads the section as the
absolute homogeneous section on that chart. On the right the restriction of the direct image is a
restriction of the glued twist (`pushforward_presheaf_map_eq_resLE`), which the chart comparison
over the *larger* open commutes with (`chartSections_resLE`) and which differs from the comparison
over the smaller one by the model transition (`trans_chartSections`); and the model transition
carries the one absolute homogeneous section to the other by
`trans_resTop_degreeSection`. -/
public theorem gluedDegreeSection_resPiece (hcoc : ∀ n : ℤ, IsNestedCocycle A n) (n : ℕ)
    (m l : S.affineOpens) (h : (l.1 : S.Opens) ≤ (m.1 : S.Opens))
    (a : A.sectionPieces (m.1 : S.Opens) n) :
    gluedDegreeSection A hcoc n (l.1 : S.Opens) l.2 (A.resPiece h n a)
      = ((Scheme.Modules.pushforward (relativeProj A).toBase).obj
          (gluedTwist A (n : ℤ) (hcoc (n : ℤ)))).val.map (homOfLE h).op
          (gluedDegreeSection A hcoc n (m.1 : S.Opens) m.2 a) := by
  have hcov : cover A l ≤ cover A m := ((relativeProj A).toBase).preimage_mono h
  have hx := chartSections_gluedDegreeSection hcoc n m a
  have h0 := pushforward_presheaf_map_eq_resLE (gluedTwist A (n : ℤ) (hcoc (n : ℤ))) h hcov
    (gluedDegreeSection A hcoc n (m.1 : S.Opens) m.2 a)
  have h1 := trans_chartSections A (n : ℤ) (hcoc (n : ℤ)) m l hcov (le_refl (cover A l))
    ((gluedTwist A (n : ℤ) (hcoc (n : ℤ))).val.resLE hcov
      (gluedDegreeSection A hcoc n (m.1 : S.Opens) m.2 a))
  have h2 := chartSections_resLE A (n : ℤ) (hcoc (n : ℤ)) m (le_refl (cover A m)) hcov
    (gluedDegreeSection A hcoc n (m.1 : S.Opens) m.2 a)
  have h3 := resLE_resTop (n : ℤ) (m.1 : S.Opens) m.2 hcov
    (degreeSection (A.grading (m.1 : S.Opens)) n
      ⟨DirectSum.of (A.sectionPieces (m.1 : S.Opens)) n a,
        A.of_mem_grading (m.1 : S.Opens) a⟩)
  have h4 := trans_resTop_degreeSection n (hcoc (n : ℤ)) m l h
    ⟨DirectSum.of (A.sectionPieces (m.1 : S.Opens)) n a,
      A.of_mem_grading (m.1 : S.Opens) a⟩ hcov (le_refl (cover A l))
  have h5 : (⟨A.res h (⟨DirectSum.of (A.sectionPieces (m.1 : S.Opens)) n a,
            A.of_mem_grading (m.1 : S.Opens) a⟩ : (A.grading (m.1 : S.Opens)) n),
          (A.res h).map_mem (A.of_mem_grading (m.1 : S.Opens) a)⟩ :
        (A.grading (l.1 : S.Opens)) n)
      = ⟨DirectSum.of (A.sectionPieces (l.1 : S.Opens)) n (A.resPiece h n a),
          A.of_mem_grading (l.1 : S.Opens) (A.resPiece h n a)⟩ :=
    Subtype.ext (A.resRingHom_of h a)
  have h6 := congrArg (fun z : (A.grading (l.1 : S.Opens)) n =>
      chartResTop A (n : ℤ) l (cover A l)
        (degreeSection (A.grading (l.1 : S.Opens)) n z)) h5
  have hy := chartSections_gluedDegreeSection hcoc n l (A.resPiece h n a)
  refine (chartSections A (n : ℤ) (hcoc (n : ℤ)) l (le_refl (cover A l))).injective ?_
  refine hy.trans ?_
  refine Eq.trans (h6.symm.trans (h4.symm.trans (congrArg
    ((modelData A (n : ℤ) (hcoc (n : ℤ))).trans m l hcov (le_refl (cover A l))) h3.symm))) ?_
  refine Eq.trans (congrArg ((modelData A (n : ℤ) (hcoc (n : ℤ))).trans m l hcov
    (le_refl (cover A l))) (congrArg ((chartModule A (n : ℤ) m).resLE hcov) hx.symm)) ?_
  refine Eq.trans (congrArg ((modelData A (n : ℤ) (hcoc (n : ℤ))).trans m l hcov
    (le_refl (cover A l))) h2.symm) ?_
  exact h1.trans (congrArg (chartSections A (n : ℤ) (hcoc (n : ℤ)) l (le_refl (cover A l)))
    h0.symm)


/-! ### The global homogeneous-section map -/

/-- The affine opens of a scheme, indexed by `AlgebraicGeometry.Scheme.affineOpens`, form a basis
of its topology. `AlgebraicGeometry.Scheme.isBasis_affineOpens` gives this for the *set* of affine
opens; the morphism-from-a-basis API wants the range of a family. -/
public theorem isBasis_range_affineOpens (S : Scheme.{u}) :
    Opens.IsBasis (Set.range fun m : S.affineOpens => (m.1 : S.Opens)) := by
  have heq : (Set.range fun m : S.affineOpens => (m.1 : S.Opens)) = S.affineOpens := by
    ext W
    exact ⟨fun ⟨m, hm⟩ => hm ▸ m.property, fun hW => ⟨⟨W, hW⟩, rfl⟩⟩
  rw [heq]
  exact S.isBasis_affineOpens

/-- `psiGluedAffine` as a morphism of the modules of sections, which is the shape the
morphism-from-a-basis API asks for. -/
public def psiGluedAffineHom (hcoc : ∀ n : ℤ, IsNestedCocycle A n) (n : ℕ)
    (m : S.affineOpens) :
    (A.piece (n : ℤ)).val.obj (op (m.1 : S.Opens)) ⟶
      ((Scheme.Modules.pushforward (relativeProj A).toBase).obj
        (gluedTwist A (n : ℤ) (hcoc (n : ℤ)))).val.obj (op (m.1 : S.Opens)) :=
  ConcreteCategory.ofHom (psiGluedAffine A hcoc n (m.1 : S.Opens) m.2)

/-- The component is `gluedDegreeSection` on the nose. -/
public theorem psiGluedAffineHom_apply (hcoc : ∀ n : ℤ, IsNestedCocycle A n) (n : ℕ)
    (m : S.affineOpens) (a : A.sectionPieces (m.1 : S.Opens) n) :
    psiGluedAffineHom hcoc n m a = gluedDegreeSection A hcoc n (m.1 : S.Opens) m.2 a :=
  rfl

/-- **The components over the affine opens are compatible with restriction.** This is
`gluedDegreeSection_resPiece`. -/
public theorem isCompatibleOnBasis_psiGluedAffine (hcoc : ∀ n : ℤ, IsNestedCocycle A n) (n : ℕ) :
    BasisRestriction.IsCompatibleOnBasis (A.piece (n : ℤ))
      ((Scheme.Modules.pushforward (relativeProj A).toBase).obj
        (gluedTwist A (n : ℤ) (hcoc (n : ℤ))))
      (fun m : S.affineOpens => (m.1 : S.Opens)) (psiGluedAffineHom hcoc n) := by
  intro m l h s
  refine Eq.trans (psiGluedAffineHom_apply hcoc n l _) ?_
  refine Eq.trans (gluedDegreeSection_resPiece hcoc n m l h s) ?_
  exact congrArg (fun z => ((Scheme.Modules.pushforward (relativeProj A).toBase).obj
      (gluedTwist A (n : ℤ) (hcoc (n : ℤ)))).val.map (homOfLE h).op z)
    (psiGluedAffineHom_apply hcoc n m s).symm

/-- **The homogeneous-section map of the glued twists.** For each natural number `n`, a morphism
of sheaves of modules from the degree-`n` piece of the base algebra to the direct image of the
degree-`n` glued twist, whose component over an affine open `U` of the base is `psiGluedAffine`.

The affine opens form a basis of the base, and the components are `Γ(S, U)`-linear and compatible
with restriction, so Tag 009U's morphism-from-a-basis
(`Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis`) assembles them, uniquely. -/
public def psiGlued (hcoc : ∀ n : ℤ, IsNestedCocycle A n) (n : ℕ) :
    A.piece (n : ℤ) ⟶ (Scheme.Modules.pushforward (relativeProj A).toBase).obj
      (gluedTwist A (n : ℤ) (hcoc (n : ℤ))) :=
  BasisRestriction.moduleSheafHomOfSectionHomOnBasis (A.piece (n : ℤ))
    ((Scheme.Modules.pushforward (relativeProj A).toBase).obj
      (gluedTwist A (n : ℤ) (hcoc (n : ℤ))))
    (fun m : S.affineOpens => (m.1 : S.Opens)) (psiGluedAffineHom hcoc n)
    (isBasis_range_affineOpens S) (isCompatibleOnBasis_psiGluedAffine hcoc n)

/-- The component of `psiGlued` over an affine open of the base is `psiGluedAffine`. -/
public theorem psiGlued_app (hcoc : ∀ n : ℤ, IsNestedCocycle A n) (n : ℕ) (m : S.affineOpens) :
    (psiGlued hcoc n).val.app (op (m.1 : S.Opens)) = psiGluedAffineHom hcoc n m :=
  BasisRestriction.moduleSheafHomOfSectionHomOnBasis_app (A.piece (n : ℤ))
    ((Scheme.Modules.pushforward (relativeProj A).toBase).obj
      (gluedTwist A (n : ℤ) (hcoc (n : ℤ))))
    (fun m : S.affineOpens => (m.1 : S.Opens)) (psiGluedAffineHom hcoc n)
    (isBasis_range_affineOpens S) (isCompatibleOnBasis_psiGluedAffine hcoc n) m

/-- `psiGlued_app` with the affine open presented as an open together with its affineness, which
is the shape `PsiGluedChart` quantifies over. -/
public theorem psiGlued_app' (hcoc : ∀ n : ℤ, IsNestedCocycle A n) (n : ℕ) (U : S.Opens)
    (hU : IsAffineOpen U) :
    (psiGlued hcoc n).val.app (op U) = psiGluedAffineHom hcoc n ⟨U, hU⟩ :=
  psiGlued_app hcoc n ⟨U, hU⟩

/-- **`psiGlued` satisfies the chart description of the homogeneous-section map.** Its component
over an affine open is `gluedDegreeSection` (`psiGlued_app`), whose chart description is
`Stacks.AlgebraicGeometry.GluedTwistSectionMap.gluedMapSection_degreeSection`. -/
public theorem psiGluedChart (hcoc : ∀ n : ℤ, IsNestedCocycle A n) :
    PsiGluedChart hcoc (psiGlued hcoc) := by
  intro U hU n a
  rw [psiGlued_app' hcoc n U hU]
  exact gluedMapSection_degreeSection A hcoc n U hU a

/-! ### Tag 01NR's twist datum from a graded algebra alone -/

/-- **Tag 01NR's twist datum, assembled from the graded algebra alone.** Of the fields
`Stacks.AlgebraicGeometry.GluedTwistSectionMap.mk` asks for, the homogeneous-section map and
its chart description are constructed here: they are `psiGlued` and `psiGluedChart`.

What remains is a graded algebra `B` on the relative projective spectrum together with an
identification `e` of its homogeneous pieces with the glued twists, and the condition that its
product and unit agree on the charts with those of the absolute twists. -/
public def mkOfGradedAlgebra (hcoc : ∀ n : ℤ, IsNestedCocycle A n)
    (B : SchemeGradedAlgebra (relativeProj A).scheme)
    (e : ∀ n : ℤ, B.piece n ≅ gluedTwist A n (hcoc n))
    (hD : IsGradedChartIso (GluedTwistChartData.chartData hcoc B e)) : TwistData A :=
  mk hcoc B e hD (psiGlued hcoc) (psiGluedChart hcoc)

end Stacks.AlgebraicGeometry.GluedTwistSectionMap

end
