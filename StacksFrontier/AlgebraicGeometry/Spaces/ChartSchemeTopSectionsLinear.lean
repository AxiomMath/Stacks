module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleSemilinear

/-!
# The global sections of the chart restriction are the sections over the chart, linearly

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `M` be an
`𝒪_X`-module on the small étale site of `X` and let `A` be an étale scheme chart of `X`.  Three
constructions carry `M` to a module on the Zariski site of the chart's scheme —
`AlgebraicGeometry.Space.restrictToChart`, its unsheafified form
`AlgebraicGeometry.Space.chartRestrictionSheaf`, and the chart-scheme transport
`AlgebraicGeometry.Space.chartSchemeModule` through the comparison equivalences of Stacks 04M0
and Descent, Proposition 03DX (2) — and over a Zariski open `W` of the chart's scheme their
sections are the sections of `M` over the étale chart which `W` cuts out.  Over a general `W`
that identification is only *semilinear*: the scalars are the functions on `W` on one side and
the sections of `𝒪_X` over the étale chart on the other, matched by a ring map which is not an
isomorphism.

**At `W = ⊤` it is linear.**  The chart which `⊤` cuts out is the chart itself, the ring map
becomes an isomorphism of two spellings of one and the same ring of global functions, and the
identification of global sections

  `Γ(A, M) ≃ₗ[Γ(chartScheme A, ⊤)] Γ(chartScheme A, 𝓕)`

is an equivalence of `Γ(chartScheme A, ⊤)`-modules.  This file forms it, for all three
constructions: for the first two with no hypothesis on `M`, and for the chart-scheme transport
with the quasi-coherence its definition requires.

## Main definitions

* `Stacks.PresheafOfModules.mapLinearEquiv`: a presheaf of modules sends an isomorphism of the
  site to a linear equivalence of the sections at the target onto the sections at the source,
  scalars restricted along the structure map.
* `Stacks.SheafOfModules.sectionsLinearEquivOfIso`: an isomorphism of sheaves of modules induces
  a linear equivalence of sections over every object of the site.
* `AlgebraicGeometry.Space.chartOpensTopIso`: the chart cut out by the whole of the chart's
  scheme, as an isomorphism of charts.
* `AlgebraicGeometry.Space.chartRestrictionSheafTopLinearEquiv` and
  `AlgebraicGeometry.Space.restrictToChartTopLinearEquiv`: **the global sections of the chart
  restriction of an `𝒪_X`-module are the sections of the module over the chart, as a linear
  equivalence** over the global functions on the chart's scheme, with no hypothesis on the
  module.
* `AlgebraicGeometry.Space.chartSchemeModuleTopLinearEquiv`: **the same for the chart-scheme
  transport of a quasi-coherent `𝒪_X`-module.**

## Main results

* `AlgebraicGeometry.Space.chartSectionsRingHom_top`: **the composite scalar map of the chart at
  the open `⊤` is the structure sheaf of `X` applied to
  `AlgebraicGeometry.Space.openChartOfComparisonTopIso`** — the identification whose absence the
  implementation notes of
  `StacksFrontier/AlgebraicGeometry/Spaces/CoherentChartSchemeRestriction.lean` record, and which is
  what makes the global sections identification linear rather than merely semilinear.
* `AlgebraicGeometry.Space.chartRestrictionSheafTopLinearEquiv_apply`: the hypothesis-free
  equivalence is the restriction map of `M` along
  `AlgebraicGeometry.Space.chartOpensTopHom`.

## Implementation notes

**The obstruction recorded in `CoherentChartSchemeRestriction` has since been removed.**  That
file says of the composite of the four restriction-of-scalars maps that "identifying it with the
structure sheaf applied to `AlgebraicGeometry.Space.openChartOfComparisonTopIso` would need that
isomorphism of charts to be the comparison counit, which the library does not record".  Both
halves are now recorded, in files written after it:
`AlgebraicGeometry.Space.counit_representedSmallEtaleEquivalence_opensObj` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionCoherent.lean` computes the counit of the
comparison of the two small étale sites at the chart which a Zariski open cuts out — it is the
identity, morphisms of the small étale site into such a chart being unique — and
`AlgebraicGeometry.Space.openChartOfComparisonTopIso_hom` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionSections.lean` identifies the chart
isomorphism at `⊤` with `AlgebraicGeometry.Space.chartOpensTopHom`.  Put together they give
`AlgebraicGeometry.Space.chartSectionsRingHom_top`, which is the obstruction discharged.

**The equivalence is nevertheless built on the unsheafified chart restriction, and so costs no
hypothesis.**  `AlgebraicGeometry.Space.chartRestrictionSheaf` is a
`PresheafOfModules.pushforward` along `AlgebraicGeometry.Space.chartOpens` whose structure map at
`⊤` is *already* the structure sheaf of `X` applied to
`AlgebraicGeometry.Space.chartOpensTopHom`, by
`AlgebraicGeometry.Space.structureRingSheaf_map_chartOpensTopHom`; so the equivalence there is
the restriction map of `M` along that isomorphism of charts and needs nothing of `M`, whereas the
chart-scheme transport does not even exist without quasi-coherence.  The transport is then
reached from it by `AlgebraicGeometry.Space.restrictToChartIsoChartSchemeModule`, an isomorphism
of sheaves of modules, which is linear on sections.

**The module is spelled `AlgebraicGeometry.Space.Modules`, not
`CategoryTheory.SheafOfModules`.**  The two are the same by an `abbrev`, but the instance
`AlgebraicGeometry.Space.moduleChartSections` — which is what makes `Γ(chartScheme A, ⊤)` act on
the sections of `M` over `A`, the structure sheaf of the small étale site being valued in
`RingCat` while `Γ(chartScheme A, ⊤)` is spelled in `CommRingCat` — is stated at the first
spelling, and instance search is syntactic.  The same bridge is needed on the other side, for the
sections of a module on the chart's scheme, and the two instances below supply it at both
spellings of `AlgebraicGeometry.Scheme.Modules`, which is a plain definition and so is not
unfolded by instance search either.

**Every composition is ascribed.**  `LinearEquiv.trans` asks for the coefficient ring of its two
arguments to agree, and it compares them syntactically: handed the sections of a module on the
chart's scheme it reads the ring as `(chartScheme A).ringCatSheaf.obj.obj (op ⊤)` and asks for a
`RingHomCompTriple` against `Γ(chartScheme A, ⊤)`, which is the same ring.  Each step below is
therefore ascribed to the `Γ` spelling with `show … from` before it is composed.

**Bijectivity of a restriction map comes from the underlying presheaf of abelian groups.**
`PresheafOfModules.map` is not the action of a functor — its target moves with the morphism — so
an isomorphism of the site is not sent to an isomorphism by it.  What is functorial is
`PresheafOfModules.presheaf`, the underlying presheaf of abelian groups, and it has the same
restriction maps; bijectivity is read off there and the linear structure restored by
`LinearEquiv.ofBijective`.

No declaration here carries a `stacks` tag: this is the linear form of the sections of the chart
restriction, an input to the tags that consume that construction rather than an assertion of any
tag.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.PresheafOfModules

universe w v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{w}}

/-- **A presheaf of modules sends an isomorphism of the site to a linear equivalence.**  For
`f : P ≅ Q` the restriction map along `f` identifies the sections over `Q` with the sections over
`P`, scalars restricted along `R.map f.hom.op`; it is linear over the sections of `R` at `Q`, and
bijective because the underlying presheaf of abelian groups is a functor. -/
noncomputable def mapLinearEquiv (N : _root_.PresheafOfModules.{w} R) {P Q : C} (f : P ≅ Q) :
    N.obj (op Q) ≃ₗ[R.obj (op Q)]
      (ModuleCat.restrictScalars (R.map f.hom.op).hom).obj (N.obj (op P)) :=
  LinearEquiv.ofBijective (N.map f.hom.op).hom
    (ConcreteCategory.bijective_of_isIso (N.presheaf.map f.hom.op))

end Stacks.PresheafOfModules

namespace Stacks.SheafOfModules

universe w m v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : CategoryTheory.Sheaf J RingCat.{w}}

/-- **An isomorphism of sheaves of modules is a linear equivalence on sections.**  Over every
object of the site the two components of the isomorphism are mutually inverse linear maps, the
coefficient ring being the same on both sides. -/
noncomputable def sectionsLinearEquivOfIso {F G : _root_.SheafOfModules.{m} R} (e : F ≅ G)
    (A : C) : F.val.obj (op A) ≃ₗ[R.obj.obj (op A)] G.val.obj (op A) :=
  ((_root_.SheafOfModules.evaluation R (op A)).mapIso e).toLinearEquiv

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

/-- **The sections of a module on a scheme are a module over the functions on the open.**  The
coefficient ring of a module on a scheme is `AlgebraicGeometry.Scheme.ringCatSheaf`, valued in
`RingCat`, while `Γ(T, W)` is spelled in `CommRingCat`; the two are definitionally equal and this
supplies the second spelling, instance search being syntactic. -/
instance moduleSchemeSections (T : Scheme.{u}) (N : SheafOfModules.{u} T.ringCatSheaf)
    (W : T.Opens) : Module Γ(T, W) (N.val.obj (op W)) :=
  (N.val.obj (op W)).isModule

/-- `AlgebraicGeometry.Space.moduleSchemeSections` at the `AlgebraicGeometry.Scheme.Modules`
spelling of the same category, which is a plain definition and so is not unfolded by instance
search. -/
instance moduleSchemeModulesSections (T : Scheme.{u}) (N : T.Modules) (W : T.Opens) :
    Module Γ(T, W) (N.val.obj (op W)) :=
  (N.val.obj (op W)).isModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
  (M : Modules.{u, u} B S hS X.1 X.2)

/-! ### The composite scalar map at the whole chart -/

/-- **At the open `⊤` the composite scalar map of the chart is the structure sheaf of `X` applied
to the chart isomorphism.**

This is the identification recorded as missing in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentChartSchemeRestriction.lean`, and it is what makes
the global sections of the chart restriction *linearly*, and not merely semilinearly, the
sections of the module over the chart.  Two facts give it: the counit of the comparison of
the two small étale sites is the identity at the chart which a Zariski open cuts out, so only the
comparison of structure sheaves of the small étale site of the chart's scheme survives in
`AlgebraicGeometry.Space.chartSectionsRingHom`; and the chart isomorphism at `⊤` is
`AlgebraicGeometry.Space.chartOpensTopHom`, along which that comparison is the change of scalars
of the chart restriction on the nose. -/
theorem chartSectionsRingHom_top (A : SmallEtale B S hS X.1) :
    chartSectionsRingHom B S hS X A ⊤ =
      ((structureRingSheaf B S hS X).obj.map
        (openChartOfComparisonTopIso B S hS X A).hom.op).hom := by
  rw [openChartOfComparisonTopIso_hom, chartSectionsRingHom, reindexBackSharp_hom_app_opensObj]
  rfl

/-- `AlgebraicGeometry.Space.chartSectionsRingHom_top` read as an equality of modules: the
sections of `M` over the chart which `⊤` cuts out, with scalars restricted along the composite
scalar map of the chart, are those sections with scalars restricted along the structure sheaf of
`X` at the chart isomorphism. -/
theorem restrictScalars_chartSectionsRingHom_top (A : SmallEtale B S hS X.1) :
    (ModuleCat.restrictScalars (chartSectionsRingHom B S hS X A ⊤)).obj
        (M.val.obj (op (openChartOfComparison B S hS X A ⊤))) =
      (ModuleCat.restrictScalars ((structureRingSheaf B S hS X).obj.map
          (openChartOfComparisonTopIso B S hS X A).hom.op).hom).obj
        (M.val.obj (op (openChartOfComparison B S hS X A ⊤))) :=
  congrArg (fun φ => (ModuleCat.restrictScalars φ).obj
      (M.val.obj (op (openChartOfComparison B S hS X A ⊤))))
    (chartSectionsRingHom_top B S hS X A)

/-! ### The linear equivalence -/

/-- The chart cut out by the whole of the chart's scheme is the chart itself:
`AlgebraicGeometry.Space.chartOpensTopHom` as an isomorphism. -/
noncomputable def chartOpensTopIso (A : SmallEtale B S hS X.1) :
    (chartOpens B S hS A).obj ⊤ ≅ A :=
  asIso (chartOpensTopHom B S hS X A)

/-- The restriction map of `M` along `AlgebraicGeometry.Space.chartOpensTopIso` as a linear
equivalence onto the global sections of the unsheafified chart restriction, with the universe of
the sections raised as that construction raises it. -/
noncomputable def chartRestrictionSheafTopLinearEquivULift (A : SmallEtale B S hS X.1) :
    ULift.{u} (M.val.obj (op A)) ≃ₗ[Γ(chartScheme A, ⊤)]
      (chartRestrictionSheaf B S hS X M A).val.obj (op (⊤ : (chartScheme A).Opens)) :=
  Stacks.PresheafOfModules.mapLinearEquiv
    (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u} M).val (chartOpensTopIso B S hS X A)

/-- **The global sections of the unsheafified chart restriction of an `𝒪_X`-module are the
sections of the module over the chart, linearly.**

`AlgebraicGeometry.Space.chartRestrictionSheaf` is a direct image along
`AlgebraicGeometry.Space.chartOpens`, so its sections over `⊤` are the sections of `M` over the
chart which `⊤` cuts out with scalars restricted along the structure sheaf of `X` at
`AlgebraicGeometry.Space.chartOpensTopHom`, by
`AlgebraicGeometry.Space.structureRingSheaf_map_chartOpensTopHom`; and that morphism of charts is
an isomorphism, so the restriction map of `M` along it is a linear equivalence.  No hypothesis on
`M` is needed. -/
noncomputable def chartRestrictionSheafTopLinearEquiv (A : SmallEtale B S hS X.1) :
    M.val.obj (op A) ≃ₗ[Γ(chartScheme A, ⊤)]
      (chartRestrictionSheaf B S hS X M A).val.obj (op (⊤ : (chartScheme A).Opens)) :=
  (show M.val.obj (op A) ≃ₗ[Γ(chartScheme A, ⊤)] ULift.{u} (M.val.obj (op A)) from
      ULift.moduleEquiv.symm).trans
    (chartRestrictionSheafTopLinearEquivULift B S hS X M A)

/-- The equivalence of `AlgebraicGeometry.Space.chartRestrictionSheafTopLinearEquiv` is the
restriction map of `M` along `AlgebraicGeometry.Space.chartOpensTopHom`, with the universe of the
sections raised as `AlgebraicGeometry.Space.chartRestrictionSheaf` raises it. -/
theorem chartRestrictionSheafTopLinearEquiv_apply (A : SmallEtale B S hS X.1)
    (x : M.val.obj (op A)) :
    chartRestrictionSheafTopLinearEquiv B S hS X M A x =
      ULift.up (M.val.map (chartOpensTopHom B S hS X A).op x) :=
  rfl

/-- **The global sections of the chart restriction of an `𝒪_X`-module are the sections of the
module over the chart, linearly.**  The chart restriction needs no sheafification
(`AlgebraicGeometry.Space.restrictToChartIsoChartRestrictionSheaf`), and an isomorphism of sheaves
of modules is a linear equivalence on sections. -/
noncomputable def restrictToChartTopLinearEquiv (A : SmallEtale B S hS X.1) :
    M.val.obj (op A) ≃ₗ[Γ(chartScheme A, ⊤)]
      (restrictToChart B S hS X.2 M A).val.obj (op (⊤ : (chartScheme A).Opens)) :=
  (chartRestrictionSheafTopLinearEquiv B S hS X M A).trans
    (show (chartRestrictionSheaf B S hS X M A).val.obj (op (⊤ : (chartScheme A).Opens))
        ≃ₗ[Γ(chartScheme A, ⊤)]
          (restrictToChart B S hS X.2 M A).val.obj (op (⊤ : (chartScheme A).Opens)) from
      Stacks.SheafOfModules.sectionsLinearEquivOfIso
        (restrictToChartIsoChartRestrictionSheaf B S hS X M A).symm ⊤)

/-- **The global sections of the chart-scheme transport of a quasi-coherent `𝒪_X`-module are the
sections of the module over the chart, as a linear equivalence** over the global functions on the
chart's scheme.

This is the statement which the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentChartSchemeRestriction.lean` decline to form, the
obstruction they record being discharged by
`AlgebraicGeometry.Space.chartSectionsRingHom_top`.  It is the hypothesis-free equivalence of
`AlgebraicGeometry.Space.chartRestrictionSheafTopLinearEquiv` followed by the identification of
the chart restriction with the chart-scheme transport,
`AlgebraicGeometry.Space.restrictToChartIsoChartSchemeModule`, which is linear on sections. -/
noncomputable def chartSchemeModuleTopLinearEquiv (hM : M.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) :
    M.val.obj (op A) ≃ₗ[Γ(chartScheme A, ⊤)]
      (chartSchemeModule B S hS X M hM A).val.obj (op (⊤ : (chartScheme A).Opens)) :=
  (chartRestrictionSheafTopLinearEquiv B S hS X M A).trans
    (show (chartRestrictionSheaf B S hS X M A).val.obj (op (⊤ : (chartScheme A).Opens))
        ≃ₗ[Γ(chartScheme A, ⊤)]
          (chartSchemeModule B S hS X M hM A).val.obj (op (⊤ : (chartScheme A).Opens)) from
      Stacks.SheafOfModules.sectionsLinearEquivOfIso
        ((restrictToChartIsoChartRestrictionSheaf B S hS X M A).symm ≪≫
          restrictToChartIsoChartSchemeModule B S hS X M hM A) ⊤)

end AlgebraicGeometry.Space

end
