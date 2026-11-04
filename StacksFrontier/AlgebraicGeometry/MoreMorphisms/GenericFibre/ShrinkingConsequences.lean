module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GenericResidueField
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.ConnectedAfterShrinking
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GeometricallyConnectedFibres
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GeometricComponentCountConstant
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GeometricComponentCountConstructible
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.ComponentCount
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.LocusNeighbourhoodOfReducedFibre
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.FromGenericFibreIrreducibility
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.GeneralizationStableLocus
public import StacksCore.Tactic.StacksAttribute

/-!
# Connected components and geometrically irreducible fibres, unconditionally

The results of Stacks chapter 37 sections 28 and 29 were proved carrying two hypotheses that
their sources do not have: the conclusion of Tag 0559, and stability of the locus `X⁰` under
generalization. Both are now theorems, so this file states each of those results with the
hypotheses of its source and nothing more.

## Main results

* `AlgebraicGeometry.exists_open_geometricIrreducibleComponentCount_constant` (Tag 055A)
* `AlgebraicGeometry.isLocallyConstructible_level_geometricIrreducibleComponentCount` (Tag 055B)
* `AlgebraicGeometry.geometricallyConnectedAfterShrinking` (Tag 055G)
* `AlgebraicGeometry.ConnectedAlongSection.clopenLocusAfterShrinking` (Tag 055N)
* `AlgebraicGeometry.ConnectedAlongSection.isLocallyConstructible_locus` (Tag 055P)
* `AlgebraicGeometry.ConnectedAlongSection.locus_mem_nhdsSet_fiberComponent` (Tag 055Q)
* `AlgebraicGeometry.ConnectedAlongSection.isOpen_locus` (Tag 055R)
* `AlgebraicGeometry.exists_compactOpen_geometricallyConnected_fibers` (Tag 057I)
* `AlgebraicGeometry.exists_etaleNeighborhood_geometricallyConnected` (Tag 055W)
* `AlgebraicGeometry.exists_etaleNeighborhood_geometricallyIntegral` (Tag 057J)
* `AlgebraicGeometry.exists_finite_over_smooth` (Tag 057K)

## Implementation notes

The statements are the `Prop`s the conditional results were phrased against, so each proof here
is one application. Those `Prop`s were checked clause by clause against the `statement_latex` of
the corresponding row of the Stacks source before the tags were placed; in particular Tag 055Q
is recorded on the form whose reducedness hypothesis is about the single fibre over the chosen
point, matching its source, rather than on the form assuming every fibre reduced.

Tag 0554, which Tags 055A and 055B were also stated conditionally on, is discharged by
`AlgebraicGeometry.irreducibleComponentsLowerBoundAfterShrinking`.
-/

@[expose] public section

open CategoryTheory Topology TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 055A.** The number of geometrically irreducible components of the
fibres of a finite type morphism is constant on a nonempty open subset of the closure of any
point of the target. -/
@[stacks 055A]
theorem exists_open_geometricIrreducibleComponentCount_constant {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] (y : Y) :
    ∃ V : Opens (↑(closure ({y} : Set Y))), Nonempty V ∧
      ∃ n : ℕ∞, ∀ z : V, geometricIrreducibleComponentCount f z.1.1 = n :=
  exists_open_geometricIrreducibleComponentCount_eq
    irreducibleComponentsLowerBoundAfterShrinking geometricallyIrreducibleAfterShrinking f y

/-- **Stacks Project, Tag 055B.** Every level set of the number of geometrically irreducible
components of the fibres of a morphism of finite presentation is locally constructible. -/
@[stacks 055B, ega "IV 9.7.9" "n(s) (irreducible)", sga "4 XIV 1.11" "special case"]
theorem isLocallyConstructible_level_geometricIrreducibleComponentCount {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hf : FinitePresentation f) (n : ℕ∞) :
    IsLocallyConstructible {y : Y | geometricIrreducibleComponentCount f y = n} :=
  isLocallyConstructible_geometricIrreducibleComponentCount_fiber
    irreducibleComponentsLowerBoundAfterShrinking geometricallyIrreducibleAfterShrinking f hf n

/-- **Stacks Project, Tag 055G.** A finite type morphism onto an irreducible base whose fibre
over the generic point is geometrically connected has geometrically connected fibres over a
nonempty open subscheme of the base. -/
@[stacks 055G]
theorem geometricallyConnectedAfterShrinking : GeometricallyConnectedAfterShrinking.{u} :=
  geometricallyConnectedAfterShrinking_of_geometricallyIrreducible
    geometricallyIrreducibleAfterShrinking

namespace ConnectedAlongSection

/-- **Stacks Project, Tag 055N.** For a finite type morphism with a section and a point `y` of
the target, the locus `X⁰` is open and closed in the inverse image of a nonempty open subset of
the closure of `y`. -/
@[stacks 055N]
theorem clopenLocusAfterShrinking : ClopenLocusAfterShrinking.{u} :=
  clopenLocusAfterShrinking_of_geometricallyIrreducible geometricallyIrreducibleAfterShrinking

/-- **Stacks Project, Tag 055P.** For a morphism of finite presentation with a section, the
locus `X⁰` is locally constructible in the source. -/
@[stacks 055P, ega "IV 9.7.12"]
theorem isLocallyConstructible_locus : Statement055P.{u} :=
  statement055P_of_geometricallyIrreducibleAfterShrinking geometricallyIrreducibleAfterShrinking

/-- **Stacks Project, Tag 055Q.** For a flat morphism of finite presentation with a section
whose fibre over `y` is geometrically reduced, the locus `X⁰` is a neighbourhood of the
connected component of that fibre meeting the section. -/
@[stacks 055Q, ega "IV 15.6.5" "nbhd of X⁰_y", ega "IV 15.6.4" "special case"]
theorem locus_mem_nhdsSet_fiberComponent (D : ConnectedAlongSection.{u})
    (hfp : FinitePresentation D.f) [Flat D.f] (y : D.Y)
    (hgr : GeometricallyReduced (D.f.fiberToSpecResidueField y)) :
    D.locus ∈ nhdsSet (D.f.fiberι y '' D.fiberComponent y) :=
  locus_mem_nhdsSet_fiberComponent_of_fiber geometricallyIrreducibleAfterShrinking D hfp y hgr

/-- **Stacks Project, Tag 055R.** For a flat morphism of finite presentation with a section and
geometrically reduced fibres, the locus `X⁰` is open in the source. -/
@[stacks 055R, ega "IV 15.6.5" "In particular: X⁰ open"]
theorem isOpen_locus : Statement055R.{u} :=
  statement055R_of_geometricallyIrreducibleAfterShrinking geometricallyIrreducibleAfterShrinking
    locusStableUnderGeneralization

end ConnectedAlongSection

/-- **Stacks Project, Tag 057I.** A geometrically connected fibre in a flat, finitely presented
family with geometrically reduced fibres and a nonempty finite locally free multisection has a
quasi-compact open neighbourhood in the source whose nonempty fibres are geometrically
connected. -/
@[stacks 057I]
theorem exists_compactOpen_geometricallyConnected_fibers : Statement057I.{u} :=
  statement057I_of_geometricallyIrreducibleAfterShrinking geometricallyIrreducibleAfterShrinking
    locusStableUnderGeneralization

/-- **Stacks Project, Tag 055W.** A geometrically connected open in a fibre of a flat, finitely
presented morphism with geometrically reduced fibres spreads, after an affine elementary étale
base change, to a quasi-compact open with geometrically connected fibres. -/
@[stacks 055W]
theorem exists_etaleNeighborhood_geometricallyConnected : Statement055W.{u} :=
  statement055W_of_geometricallyIrreducibleAfterShrinking geometricallyIrreducibleAfterShrinking
    locusStableUnderGeneralization

/-- **Stacks Project, Tag 057J.** A geometrically irreducible open in a fibre of a normal,
finitely presented morphism spreads, after an affine elementary étale base change, to a
quasi-compact open with geometrically integral fibres. -/
@[stacks 057J]
theorem exists_etaleNeighborhood_geometricallyIntegral : Statement057J.{u} :=
  statement057J_of_geometricallyIrreducibleAfterShrinking geometricallyIrreducibleAfterShrinking
    locusStableUnderGeneralization

/-- **Stacks Project, Tag 057K.** A morphism locally of finite type is, in elementary étale
neighbourhoods of a point and of its image, finite over a smooth morphism of relative dimension
the dimension of the fibre at that point, with geometrically integral fibres and purely
transcendental residue field extension; and the finite morphism is of finite presentation as
soon as the original one is. -/
@[stacks 057K]
theorem exists_finite_over_smooth : Statement057K.{u} :=
  statement057K_of_geometricallyIrreducibleAfterShrinking geometricallyIrreducibleAfterShrinking
    locusStableUnderGeneralization

end AlgebraicGeometry

end
