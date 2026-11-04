module

public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.AffineFlatness
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapFlatTargetSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction

/-!
# Flatness of a module on an algebraic space over an affine base, read on the sections

Let `S` be an affine scheme of a big fppf site, let `X` be an algebraic space over `S` and let
`G` be a quasi-coherent `𝒪_X`-module which is flat over `S` in the sense of Stacks 05VV, that is,
flat over the final algebraic space along the structure morphism.  This file draws the
consequence a consumer of that hypothesis needs: for every étale scheme chart of `X` with affine
underlying scheme, the module of sections of `G` over that chart is a flat module over the ring
of global functions on `S`.

The three inputs are all now available.  Flatness over the base is a condition on one commuting
square of étale scheme charts, and the base itself is the identity chart of the final algebraic
space, which gives the square (`AlgebraicGeometry.Space.baseChartDiagram`).  The restriction of
`G` to the chart is quasi-coherent on the Zariski site of the chart's scheme
(`AlgebraicGeometry.Space.isQuasicoherent_restrictToChart`) and its sections over the whole chart
are the sections of `G` over the chart
(`AlgebraicGeometry.Space.chartRestrictionSheaf_obj`).  With both affine,
`AlgebraicGeometry.isFlatOver_iff_flat_sections` turns the stalkwise condition of Stacks 08KT
into flatness of the global sections.

## Main definitions

* `AlgebraicGeometry.Space.baseChartDiagram` is the commuting square of étale scheme charts over
  the base attached to an étale scheme chart of `X`: the base is the identity chart of the final
  algebraic space.
* `AlgebraicGeometry.Space.chartToBase` is the structure morphism of an étale scheme chart of `X`
  to the base, as a morphism of schemes.

## Main results

* `AlgebraicGeometry.Space.flat_sections_of_isFlatOver`: **the sections of a quasi-coherent
  `𝒪_X`-module flat over an affine base, over an étale scheme chart with affine underlying
  scheme, are a flat module over the global functions on the base.**
* `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.flat_sections_G`: the same statement for
  the target module of the standing situation of Stacks 0CWA.
* `AlgebraicGeometry.Space.chartToBase_eq`: the vertical morphism of that square is the structure
  morphism of the chart over the base.

## Implementation notes

The scalar action on the sections is the restriction of scalars along the pullback of functions
`Γ(S, ⊤) ⟶ Γ(chartScheme A, ⊤)` of the chart's structure morphism, written with
`Module.compHom` exactly as `AlgebraicGeometry.isFlatOver_iff_flat_sections` writes it.  The
sections of `𝒪_X` over an étale chart *are* the global functions on the chart's scheme, on the
nose, so no comparison of coefficient rings intervenes.

The passage from the sections of the chart restriction over the open `⊤` to the sections of `G`
over the chart is `AlgebraicGeometry.Space.chartRestrictionSheafTopEquiv`, which is linear over
the global functions on the chart's scheme.  Flatness is carried across by
`Module.Flat.of_semilinearEquiv` at the identity of `Γ(S, ⊤)`: both actions of `Γ(S, ⊤)` are
restrictions of scalars along the pullback of functions of the chart's structure morphism, so the
semilinearity needed is that equivalence's own linearity, read at the values of that pullback.

No declaration here carries a `stacks` tag.  Stacks 05VV is the definition being consumed and is
already tagged at `AlgebraicGeometry.Space.IsFlatOver`; Stacks 0CWA is tagged at
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation`.  What is added is the chartwise
consequence of the hypothesis, not a clause of either.

## References

* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 0CWA](https://stacks.math.columbia.edu/tag/0CWA)
* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The commuting square of étale scheme charts over the base attached to an étale scheme chart
`A` of `X`: the chart of the final algebraic space is the identity chart of the base, and the
vertical morphism is the structure morphism of `A`. -/
noncomputable def baseChartDiagram (A : SmallEtale B S hS X.1) :
    ChartDiagram B S hS X.1 (terminalSpace B S hS).1
      ((terminalSpace_isTerminal B S hS).from X).hom where
  U := A
  V := selfChart B S hS (baseTerminal B S hS)
  g := Over.mkIdTerminal.from (chartFppfObject B S hS X A)
  comm := (baseTerminal_yonedaIsTerminal B S hS).hom_ext _ _

/-- The structure morphism of an étale scheme chart of `X` to the base, as a morphism of
schemes. -/
noncomputable abbrev chartToBase (A : SmallEtale B S hS X.1) : chartScheme A ⟶ S :=
  (BigFppfOver.toScheme B S hS).map (baseChartDiagram B S hS X A).g

/-- The vertical morphism of `AlgebraicGeometry.Space.baseChartDiagram` really is the structure
morphism of the chart over the base: it is the unique morphism to the final object of the big
fppf category over `S`, and that is the structure morphism. -/
theorem chartToBase_eq (A : SmallEtale B S hS X.1) :
    chartToBase B S hS X A = B.inclusion.map (chartFppfObject B S hS X A).hom :=
  congrArg (BigFppfOver.toScheme B S hS).map
    (Over.mkIdTerminal.hom_ext _
      (Over.homMk (U := chartFppfObject B S hS X A) (V := Over.mk (𝟙 (B.obj hS)))
        (chartFppfObject B S hS X A).hom (Category.comp_id _)))

/-- **The sections of a quasi-coherent module flat over an affine base, over an affine étale
scheme chart, are flat over the base.**

Let `G` be a quasi-coherent `𝒪_X`-module which is flat over the base in the sense of
Stacks 05VV, and let `A` be an étale scheme chart of `X` whose scheme is affine.  Then the
`Γ(S, ⊤)`-module `G(A)` — scalars acting through the pullback of functions along the structure
morphism of the chart — is flat. -/
theorem flat_sections_of_isFlatOver [IsAffine S] (G : Modules.{u, u} B S hS X.1 X.2)
    (hG : G.IsQuasicoherentOnSite)
    (hflat : IsFlatOver B S hS X.2 ((terminalSpace_isTerminal B S hS).from X).hom G)
    (A : SmallEtale B S hS X.1) (hA : IsAffine (chartScheme A)) :
    letI : Module Γ(S, ⊤) (G.val.obj (op A)) :=
      Module.compHom _ (chartToBase B S hS X A).appTop.hom
    Module.Flat Γ(S, ⊤) (G.val.obj (op A)) := by
  have := hA
  have : SheafOfModules.IsQuasicoherent (chartRestrictionSheaf B S hS X G A) :=
    isQuasicoherent_chartRestrictionSheaf B S hS X G hG A
  have h2 : AlgebraicGeometry.IsFlatOver (chartToBase B S hS X A).toLRSHom.toShHom
      (chartRestrictionSheaf B S hS X G A) :=
    (AlgebraicGeometry.isFlatOver_iff_of_moduleIso _
        (restrictToChartIsoChartRestrictionSheaf B S hS X G A)).1
      (hflat (baseChartDiagram B S hS X A))
  let : Module Γ(S, ⊤) Γ(chartRestrictionSheaf B S hS X G A, ⊤) :=
    Module.compHom _ (chartToBase B S hS X A).appTop.hom
  have : Module.Flat Γ(S, ⊤) Γ(chartRestrictionSheaf B S hS X G A, ⊤) :=
    (AlgebraicGeometry.isFlatOver_iff_flat_sections (chartToBase B S hS X A)
      (chartRestrictionSheaf B S hS X G A)).1 h2
  let : Module Γ(S, ⊤) (G.val.obj (op A)) :=
    Module.compHom _ (chartToBase B S hS X A).appTop.hom
  refine Module.Flat.of_semilinearEquiv (RingEquiv.refl Γ(S, ⊤))
    (chartRestrictionSheafTopEquiv B S hS X G A).toAddEquiv (fun a m => ?_)
  exact (chartRestrictionSheafTopEquiv B S hS X G A).map_smul
    ((chartToBase B S hS X A).appTop.hom a) m

/-- **The sections of the target module of Stacks 0CWA over an affine étale chart are flat over
the base.**  This is `AlgebraicGeometry.Space.flat_sections_of_isFlatOver` at the standing data
of Stacks 0CWA, whose target module is quasi-coherent and flat over the base by hypothesis. -/
theorem ModuleMapFlatTargetSituation.flat_sections_G [IsAffine S]
    (D : ModuleMapFlatTargetSituation B S hS) (A : SmallEtale B S hS D.X.1)
    (hA : IsAffine (chartScheme A)) :
    letI : Module Γ(S, ⊤) (D.G.val.obj (op A)) :=
      Module.compHom _ (chartToBase B S hS D.X A).appTop.hom
    Module.Flat Γ(S, ⊤) (D.G.val.obj (op A)) :=
  flat_sections_of_isFlatOver B S hS D.X D.G D.quasicoherent_G D.flat_G A hA

end AlgebraicGeometry.Space

end
