module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalChartAssociatedModuleRestriction
public import StacksFrontier.CategoryTheory.CommutingSquares

/-!
# The composition law of Stacks 04CO at the restriction data of a presented chart

`AlgebraicGeometry.Space.conormalModulePresentedChartAssociatedIso` identifies the inverse image
of the conormal module `𝒞_{Z/X'}` to the small étale site of a chart of `Z` cut out by a
cartesian square with the associated module of the Zariski conormal sheaf of the presenting
closed immersion, and its middle factor is the identification of [Stacks Project, Tag 04CO] at
the base-changed subspace of the chart space.  This file reads that factor's composition law in
the étale source, `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionCanonicalIso_comp`, at
the data a *restriction* of the presented chart to a smaller ambient chart supplies.

That is the [Stacks Project, Tag 04CO] factor of the fourth compatibility of
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.IsActionSectionRestrictionNatural` —
the compatibility in the chart of the target comparison
`AlgebraicGeometry.Space.ChartLiftPresentation.chartTargetIso`.

## Main results

* `AlgebraicGeometry.Space.presentedSubspaceRangeMap_square_comp` and
  `AlgebraicGeometry.Space.isPullback_presentedSubspaceRangeMap_comp`: the smaller presented
  chart's commuting and cartesian squares, read over the **composite** étale morphism
  `chartMap ≫ chartToSpace` instead of over `chartToSpace` of the smaller ambient chart.
* `AlgebraicGeometry.Space.presentedRangeMap_comp_square` and
  `AlgebraicGeometry.Space.isPullback_presentedRangeMap_comp`: the same two squares read over
  that composite **and** with the projection to `Z` split through the bigger base-changed
  subspace.  These four are the propositions that the composition law of
  [Stacks Project, Tag 04CO] has to be read at.
* `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionCanonicalIso_chartMap_comp_chartToSpace`:
  **the identification of [Stacks Project, Tag 04CO] at the smaller presented chart is the
  identification read over the composite étale morphism.**  This is the first derived statement
  about that identification at a presented chart's restriction.

## What is here, and what the remaining step is

The composition law `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionCanonicalIso_comp`
states the identification at a *composite* étale morphism and a *composite* morphism of
subspaces, while `AlgebraicGeometry.Space.conormalModulePresentedChartAssociatedIso` at the
smaller presentation reads it at `AlgebraicGeometry.Space.chartToSpace` of the smaller ambient
chart and at `AlgebraicGeometry.Space.presentedSubspaceRangeMap` of that presentation.  Those
agree with the two composites, by `AlgebraicGeometry.Space.chartMap_comp_chartToSpace` and by
`AlgebraicGeometry.Space.presentedSubspaceRangeMap_comp`, and the two agreements have to be used
differently: the étale morphism occurs in the identification's type only inside propositions, so
changing it is a plain equation of isomorphisms — that is
`AlgebraicGeometry.Space.conormalModuleEtaleRestrictionCanonicalIso_congr`, and the last main
result above is its instantiation; the morphism of subspaces occurs in the type under
`AlgebraicGeometry.Space.modulePullback`, so changing it can only be an equation of
`CategoryTheory.eqToHom`-transported morphisms, which is
`AlgebraicGeometry.Space.conormalModuleEtaleRestrictionCanonicalIso_hom_eq_of_eq`.

**The second of those two, and the composition law it feeds, are not here, and the reason is
elaboration cost.**  Each of the three instantiations — the congruence, the transported equation, and the
composition law — elaborates in about 3 s when its type is *inferred*, and the three of them in
one declaration exhaust the 200 000-heartbeat budget, failing inside the third.  Splitting them
into declarations of their own does not help as long as the declaration's statement is an
equation of **underlying morphisms**: the statement alone is affordable (checked, with the
conclusion taken as a hypothesis), the proof term alone is affordable, and the two together are a
`whnf` timeout at every split that was tried — the congruence and the transport pasted, the
transport alone, and the composition law alone, each at 200 000 heartbeats.  A type ascription
naming the source and target of each comparison does not change it; `attribute [local
irreducible] modulePullback modulePullbackCompIso`, which this file needs and which is the idiom
of `StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalChartAssociatedModule`, moves the
cost from the statement into the proof but does not remove it.

What *is* affordable is an equation **between the isomorphisms**, carrying no composite, no
`CategoryTheory.eqToHom` and no `CategoryTheory.Iso.hom` — the last main result above, which
elaborates with its proof in well under the budget.  So the shape the remaining two steps have to
be given is the same one: equations of isomorphisms, with the consumer projecting them onto its
square by `congrArg CategoryTheory.Iso.hom`.  That is also how the source-side square of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftActionSheafChartSourceRestrictionSquare`
crosses its own comparison, and its module docstring records the same measurement: crossing a
junction inside a composite of chart-level comparisons is a timeout, crossing it between
isomorphisms or at an object costs nothing.

No `@[stacks]` attribute is claimed: Tags 03LU, 04CO and 04G2 (1) are registered where the
constructions they name are built, and what is proved here is one of those constructions read at
the restriction data of a presented chart, which is an interior step of
[Stacks Project, Tag 04AM].

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X' : AlgebraicSpaces B S hS}
variable (Z : ClosedSubspaces B S hS X'.1) (U' V' : SmallEtale B S hS X'.1) (m : V' ⟶ U')
    {T T₂ : BigFppfOver B S hS}
    (incl : T ⟶ (SmallEtale.toOver B S hS X'.1).obj U')
    (hincl : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map incl))
    (c : yoneda.obj T ⟶ Z.1.toFunctor)
    (hpb : IsPullback (yoneda.map incl) c U'.1.hom Z.1.ι)
    (incl₂ : T₂ ⟶ (SmallEtale.toOver B S hS X'.1).obj V')
    (hincl₂ : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map incl₂))
    (c₂ : yoneda.obj T₂ ⟶ Z.1.toFunctor)
    (hpb₂ : IsPullback (yoneda.map incl₂) c₂ V'.1.hom Z.1.ι)
    (σ : T₂ ⟶ T)
    (hσ : σ ≫ incl = incl₂ ≫ (SmallEtale.toOver B S hS X'.1).map m)
    (hσc : yoneda.map σ ≫ c = c₂)

include hpb₂ in
/-- The square of inclusions of the smaller presented chart, read over the **composite** étale
morphism `chartMap ≫ chartToSpace` rather than over `chartToSpace` of the smaller ambient chart.
The two are the same morphism, by `AlgebraicGeometry.Space.chartMap_comp_chartToSpace`. -/
theorem presentedSubspaceRangeMap_square_comp :
    subspaceInclusion B S hS (chartSpace B S hS X' V')
          (closedSubspaceRange B S hS incl₂ hincl₂) ≫
        (chartMap B S hS X' m ≫ chartToSpace B S hS X' U') =
      presentedSubspaceRangeMap B S hS Z V' incl₂ hincl₂ c₂ ≫
        subspaceInclusion B S hS X' Z := by
  rw [chartMap_comp_chartToSpace]
  exact presentedSubspaceRangeMap_square B S hS Z V' incl₂ hincl₂ c₂ hpb₂

include hpb₂ in
/-- The cartesian square of the smaller presented chart, read over the **composite** étale
morphism `chartMap ≫ chartToSpace`. -/
theorem isPullback_presentedSubspaceRangeMap_comp :
    IsPullback (closedSubspaceRange B S hS incl₂ hincl₂).1.ι
      (presentedSubspaceRangeMap B S hS Z V' incl₂ hincl₂ c₂).hom
      (chartMap B S hS X' m ≫ chartToSpace B S hS X' U').hom Z.1.ι := by
  rw [chartMap_comp_chartToSpace]
  exact isPullback_presentedSubspaceRangeMap B S hS Z V' incl₂ hincl₂ c₂ hpb₂

include hpb hσ in
/-- The square of inclusions of the smaller presented chart, read over the **composite** étale
morphism and with the projection to `Z` split through the bigger base-changed subspace.  This is
the square that the composition law of [Stacks Project, Tag 04CO] is stated at.

It is the two stages' own squares glued along the inclusion of the bigger base-changed subspace,
by `CategoryTheory.square_comp`, which is already stated at this bracketing.  Gluing them rather
than rewriting `AlgebraicGeometry.Space.presentedSubspaceRangeMap_comp` into the smaller chart's
square is what keeps it affordable: the backward rewrite has to abstract an occurrence underneath
`CategoryTheory.ObjectProperty.Hom.hom`, and that is a `whnf` timeout. -/
theorem presentedRangeMap_comp_square :
    subspaceInclusion B S hS (chartSpace B S hS X' V')
          (closedSubspaceRange B S hS incl₂ hincl₂) ≫
        (chartMap B S hS X' m ≫ chartToSpace B S hS X' U') =
      (presentedRangeMap B S hS U' V' incl hincl incl₂ hincl₂ σ ≫
          presentedSubspaceRangeMap B S hS Z U' incl hincl c) ≫
        subspaceInclusion B S hS X' Z :=
  CategoryTheory.square_comp
    (presentedRangeMap_square B S hS U' V' m incl hincl incl₂ hincl₂ σ hσ)
    (presentedSubspaceRangeMap_square B S hS Z U' incl hincl c hpb)

include hpb₂ hσc in
/-- The cartesian square of the smaller presented chart, read over the **composite** étale
morphism and with the projection to `Z` split through the bigger base-changed subspace.

It is `AlgebraicGeometry.Space.isPullback_presentedSubspaceRangeMap_comp` with
`AlgebraicGeometry.Space.presentedSubspaceRangeMap_comp` rewritten into it **at the underlying
morphism of presheaves**, not at the morphism of algebraic spaces.  That is what makes the
rewrite affordable: the two squares differ in one morphism and in nothing else, so abstracting it
leaves `CategoryTheory.IsPullback`'s other three arguments untouched, whereas pasting the two
stages' cartesian squares horizontally obliges the elaborator to identify
`(f ≫ f').hom` with `f.hom ≫ f'.hom` underneath the pasted square's implicit objects — a `whnf`
timeout at 200 000 heartbeats. -/
theorem isPullback_presentedRangeMap_comp :
    IsPullback (closedSubspaceRange B S hS incl₂ hincl₂).1.ι
      (presentedRangeMap B S hS U' V' incl hincl incl₂ hincl₂ σ ≫
        presentedSubspaceRangeMap B S hS Z U' incl hincl c).hom
      (chartMap B S hS X' m ≫ chartToSpace B S hS X' U').hom Z.1.ι := by
  rw [← congrArg (fun t => t.hom)
    (presentedSubspaceRangeMap_comp B S hS Z U' V' incl hincl c incl₂ hincl₂ c₂ σ hσc)]
  exact isPullback_presentedSubspaceRangeMap_comp B S hS Z U' V' m incl₂ hincl₂ c₂ hpb₂

section Law

attribute [local irreducible] modulePullback modulePullbackCompIso

include hpb₂ in
/-- **The identification of [Stacks Project, Tag 04CO] at the smaller presented chart, re-read
over the composite étale morphism.**  The étale morphism of the smaller presented chart is the
morphism of ambient charts followed by the étale structure morphism of the bigger one, by
`AlgebraicGeometry.Space.chartMap_comp_chartToSpace`, and that morphism occurs in the
identification's type only inside propositions — so the two readings are isomorphisms of one
type and the re-reading is a plain equation, by
`AlgebraicGeometry.Space.conormalModuleEtaleRestrictionCanonicalIso_congr`.

This is stated **between the isomorphisms** and not between their underlying morphisms, and that
is forced rather than stylistic: at the isomorphisms the two sides have the same type and the
equation carries no composite, while the `.hom` form has to be written with a
`CategoryTheory.eqToHom` and a composition in it, and checking that written form against the
congruence's own conclusion is an `isDefEq` timeout at 200 000 heartbeats.  The consumer projects
this onto its square with `congrArg CategoryTheory.Iso.hom`. -/
theorem conormalModuleEtaleRestrictionCanonicalIso_chartMap_comp_chartToSpace :
    conormalModuleEtaleRestrictionCanonicalIso B S hS
        (closedSubspaceRange B S hS incl₂ hincl₂) Z (chartToSpace B S hS X' V')
        (presentedSubspaceRangeMap B S hS Z V' incl₂ hincl₂ c₂)
        (presentedSubspaceRangeMap_square B S hS Z V' incl₂ hincl₂ c₂ hpb₂)
        (isPullback_presentedSubspaceRangeMap B S hS Z V' incl₂ hincl₂ c₂ hpb₂)
        (isEtale_chartToSpace B S hS X' V') =
      conormalModuleEtaleRestrictionCanonicalIso B S hS
        (closedSubspaceRange B S hS incl₂ hincl₂) Z
        (chartMap B S hS X' m ≫ chartToSpace B S hS X' U')
        (presentedSubspaceRangeMap B S hS Z V' incl₂ hincl₂ c₂)
        (presentedSubspaceRangeMap_square_comp B S hS Z U' V' m incl₂ hincl₂ c₂ hpb₂)
        (isPullback_presentedSubspaceRangeMap_comp B S hS Z U' V' m incl₂ hincl₂ c₂ hpb₂)
        (isEtale_comp B S hS (isEtale_chartMap B S hS X' m)
          (isEtale_chartToSpace B S hS X' U')) :=
  conormalModuleEtaleRestrictionCanonicalIso_congr B S hS
    (closedSubspaceRange B S hS incl₂ hincl₂) Z
    (presentedSubspaceRangeMap B S hS Z V' incl₂ hincl₂ c₂)
    (chartMap_comp_chartToSpace B S hS X' m).symm
    (presentedSubspaceRangeMap_square B S hS Z V' incl₂ hincl₂ c₂ hpb₂)
    (isPullback_presentedSubspaceRangeMap B S hS Z V' incl₂ hincl₂ c₂ hpb₂)
    (isEtale_chartToSpace B S hS X' V')
    (presentedSubspaceRangeMap_square_comp B S hS Z U' V' m incl₂ hincl₂ c₂ hpb₂)
    (isPullback_presentedSubspaceRangeMap_comp B S hS Z U' V' m incl₂ hincl₂ c₂ hpb₂)
    (isEtale_comp B S hS (isEtale_chartMap B S hS X' m)
      (isEtale_chartToSpace B S hS X' U'))

end Law

end AlgebraicGeometry.Space

end
