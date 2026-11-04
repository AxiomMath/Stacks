module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicFiniteTypeCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyComposition
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalProperties

/-!
# Composition of a local property of morphisms of locally adic\* formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. **Remark 87.21.13 (Stacks 0GBJ)** has two
halves. The first defines what it means for a local property `P` of morphisms of
`WAdm^{adic*}`, in the sense of Remark 0ANH, to be *stable under composition*: for `B → A` and
`C → B` in that category, `P (B → A)` and `P (C → B)` should force `P (C → A)`. The second
asserts that the analogue of **Lemma 87.21.12 (Stacks 0GBI)** then holds for morphisms between
locally adic\* formal algebraic spaces over `S`.

The first half, at the class of rings the source names, is
`TopologicalRing.PropertyIsStableUnderCompositionAdicStar`. This file is the second half.

## Each conclusion is an instantiation

Nothing in the covering argument of Stacks 0GBI depends on the class of rings. That argument is
carried out once at an arbitrary class `C` of linearly topologized rings in
`StacksFrontier/AlgebraicGeometry/FormalSpace/LocalPropertyComposition.lean`, as
`AlgebraicGeometry.FormalSpace.hasPropertyAfterSourceCover_comp` and
`AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_comp`, and the statements
below instantiate it at `C := TopologicalRing.IsAdicStar`. So, exactly as for the two chart
criteria of the second half of Stacks 0ANH in
`StacksFrontier/AlgebraicGeometry/FormalSpace/AdicStarChartCriteria.lean`, no new mathematics is
needed: the adic\* reading is a choice of `C`, and
`AlgebraicGeometry.FormalSpace.HasPropertyOnAffineChartMap` and the three conditions of Stacks
0ANG built from it mention no other class.

## The class of rings, and the hypothesis on `P`

The source's class is `WAdm^{adic*}`: the adic topological rings — hence, by the conventions of
Stacks 0AMV and 07E8(8), complete and separated — possessing a finitely generated ideal of
definition. It is `TopologicalRing.IsAdicStar`, and the source's notion of stability under
composition for that class is `TopologicalRing.PropertyIsStableUnderCompositionAdicStar`, whose
locality clause is `TopologicalRing.PropertyIsLocalAdicStar`, that is
`TopologicalRing.PropertyIsLocal` read at the same class. Both the conditions and the hypothesis
on `P` below are therefore the source's.

`TopologicalRing.AdicStarPropertyIsStableUnderComposition` spells the class as
`∃ I : Ideal R, I.FG ∧ _root_.IsAdic I`; the two conditions on `P` are equivalent, by
`TopologicalRing.adicStarPropertyIsStableUnderComposition_iff`. The hypothesis is not
vacuous: `TopologicalRing.adicAndFiniteType_propertyIsStableUnderCompositionAdicStar` exhibits
adic morphisms of topologically finite type as an inhabitant.

## The inputs that remain explicit hypotheses

* `hchart`, the composition axiom of the first half read on morphisms of affine formal algebraic
  spaces, `AlgebraicGeometry.FormalSpace.ChartPropertyIsStableUnderComposition`. Condition (1)
  of Stacks 0ANG quantifies over *presentations* of a chart map by rings of the class, so passing
  from a condition on ring maps to a condition on chart maps needs the anti-equivalence of
  **Stacks 0AN0** in a shape this library does not carry — it has that anti-equivalence only for
  charts already presented as formal spectra, and transporting it along the isomorphisms of
  condition (1) is not available. The hypothesis is shaped
  `TopologicalRing.PropertyIsStableUnderCompositionAdicStar P → _`, as `hchart` is in
  `AdicStarChartCriteria.lean`, so that the source's hypothesis on `P` stays visible as `hP` and
  the missing translation is isolated. It is not a statement about the class of rings, so the
  adic\* reading does not remove it; it stands to the first half of Stacks 0GBJ as
  `AlgebraicGeometry.FormalSpace.ChartPropertyAscendsAlongAffineEtale` stands to axiom (1) of
  Situation 0CBA.
* `h31`, the implication (3) ⟹ (1) of Stacks 0ANG, of which the library carries only (1) ⟹ (2).
  This is the same hypothesis the base-change transfer of Stacks 0GBE carries, for the same
  reason.
* `hpbf`, `hpbg` and, for condition (2), `hpbfg`: **Stacks 0AJ3** for the fibre products of a
  morphism with the affine étale charts of its target, in the shape
  `AlgebraicGeometry.FormalSpace.HasFormalAlgebraicSpaceChartPullbacks` in which the covering
  argument and the implication (1) ⟹ (2) of Stacks 0ANG consume it.

The hypotheses that `X`, `Y` and `Z` be locally adic\* are not imposed: the covering argument
asks only that `Z` be a formal algebraic space, which is the first conjunct of its being locally
adic\*, so the statements below hold for arbitrary fppf sheaves `X` and `Y` and are stronger
than the variant the remark asserts. Nothing else is asked of `X` or of `Y`.

In each statement the hypothesis on `f` and on `g` is condition (1) of Stacks 0ANG, the
strongest of the three under the implications this library carries unconditionally; in the
source, where the equivalence of Stacks 0ANG is available, that is the same hypothesis as
"satisfies the equivalent conditions".

## Main results

* `AlgebraicGeometry.FormalSpace.hasPropertyAfterSourceCover_comp_adicStar`,
  `AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_comp_adicStar` and
  `AlgebraicGeometry.FormalSpace.hasPropertyAfterTargetCover_comp_adicStar`: **the second half
  of Stacks 0GBJ**, conditions (3), (1) and (2) of Stacks 0ANG for the composite `g ∘ f` at the
  class `WAdm^{adic*}`. Lemma 0GBI concludes that the composite satisfies *the equivalent
  conditions* of Stacks 0ANG, so all three are part of what the variant asserts; the
  *equivalence* itself is `AlgebraicGeometry.FormalSpace.hasProperty_tfae`, whose adic\* reading
  is `AdicStarChartCriteria.lean` and which carries two further inputs this library does not
  have.

None of the three carries a `@[stacks]` registration: each takes as hypotheses inputs the
source proves (`hchart`, `hpbf`, `hpbg`, and for conditions (1) and (2) also `h31`, `hpbfg`),
so none is the second half of Stacks 0GBJ under the source's hypotheses alone.

## References

* [Stacks Project, Tag 0GBJ](https://stacks.math.columbia.edu/tag/0GBJ)
* [Stacks Project, Tag 0GBI](https://stacks.math.columbia.edu/tag/0GBI)
* [Stacks Project, Tag 0GBK](https://stacks.math.columbia.edu/tag/0GBK)
* [Stacks Project, Tag 0GBE](https://stacks.math.columbia.edu/tag/0GBE)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0ANH](https://stacks.math.columbia.edu/tag/0ANH)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AKY](https://stacks.math.columbia.edu/tag/0AKY)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-- **Stacks 0GBJ, second half**, in the form of condition (3) of Stacks 0ANG for the composite.
Let `P` be a local property of morphisms of `WAdm^{adic*}` stable under composition in the sense
of the first half of the remark. If `f : X ⟶ Y` and `g : Y ⟶ Z` satisfy condition (1) of Stacks
0ANG for `P` at the class `WAdm^{adic*}`, then the composite `g ∘ f` satisfies condition (3).

This is the covering argument of Stacks 0GBI, carried out once at an arbitrary class of rings in
`hasPropertyAfterSourceCover_comp` and instantiated here; the chart reading `hchart` of the
remark's own composition axiom and the fibre products `hpbf`, `hpbg` of Stacks 0AJ3 are the
inputs this library does not carry. See the module docstring. -/
theorem hasPropertyAfterSourceCover_comp_adicStar
    (hP : TopologicalRing.PropertyIsStableUnderCompositionAdicStar.{u} P)
    (hchart : TopologicalRing.PropertyIsStableUnderCompositionAdicStar.{u} P →
      ChartPropertyIsStableUnderComposition B S hS TopologicalRing.IsAdicStar P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hZ : IsFormalAlgebraicSpace B S hS Z)
    (hpbg : HasFormalAlgebraicSpaceChartPullbacks B S hS g)
    (hpbf : HasFormalAlgebraicSpaceChartPullbacks B S hS f)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P f)
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P g) :
    HasPropertyAfterSourceCover B S hS TopologicalRing.IsAdicStar P (f ≫ g) :=
  hasPropertyAfterSourceCover_comp B S hS TopologicalRing.IsAdicStar P (hchart hP) f g hZ hpbg
    hpbf hf hg

/-- **Stacks 0GBJ, second half**: the analogue of Lemma 0GBI for morphisms between locally
adic\* formal algebraic spaces, in the form of condition (1) of Stacks 0ANG for the composite.
Let `P` be a local property of morphisms of `WAdm^{adic*}` stable under composition in the sense
of the first half of the remark. If `f : X ⟶ Y` and `g : Y ⟶ Z` satisfy condition (1) of Stacks
0ANG for `P` at the class `WAdm^{adic*}`, then so does the composite `g ∘ f`.

Condition (3) is what the covering argument of Stacks 0GBI gives; the passage back to condition
(1) is the implication (3) ⟹ (1) of Stacks 0ANG, carried as `h31` as in the base-change transfer
of Stacks 0GBE. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_comp_adicStar
    (hP : TopologicalRing.PropertyIsStableUnderCompositionAdicStar.{u} P)
    (hchart : TopologicalRing.PropertyIsStableUnderCompositionAdicStar.{u} P →
      ChartPropertyIsStableUnderComposition B S hS TopologicalRing.IsAdicStar P)
    (h31 : SourceCoverImpliesEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hZ : IsFormalAlgebraicSpace B S hS Z)
    (hpbg : HasFormalAlgebraicSpaceChartPullbacks B S hS g)
    (hpbf : HasFormalAlgebraicSpaceChartPullbacks B S hS f)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P f)
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P g) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P (f ≫ g) :=
  h31 _ (hasPropertyAfterSourceCover_comp_adicStar B S hS P hP hchart f g hZ hpbg hpbf hf hg)

/-- **Stacks 0GBJ, second half**, in the form of condition (2) of Stacks 0ANG for the composite.
Lemma 0GBI concludes that the composite satisfies *the equivalent conditions* of Stacks 0ANG, so
the adic\* variant of it asserts all three of them for `g ∘ f`; conditions (3) and (1) are
`hasPropertyAfterSourceCover_comp_adicStar` and
`hasPropertyOnEveryAffineEtaleDiagram_comp_adicStar` above, and this is the remaining one.

The route is condition (1) for the composite, which is the declaration above, followed by the
implication (1) ⟹ (2) of Stacks 0ANG,
`hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram`. Beyond the hypotheses that condition
(1) already carries, that implication asks for the fibre products of the composite with the
affine étale charts of `Z` to be formal algebraic spaces, which is Stacks 0AJ3 again and is
`hpbfg`, exactly the shape in which the implication consumes it.

The *equivalence* of the three conditions for the composite is not asserted here; it is
`AlgebraicGeometry.FormalSpace.hasProperty_tfae`, read at the class `WAdm^{adic*}` in
`StacksFrontier/AlgebraicGeometry/FormalSpace/AdicStarChartCriteria.lean`, which carries two
further inputs this library does not have. -/
theorem hasPropertyAfterTargetCover_comp_adicStar
    (hP : TopologicalRing.PropertyIsStableUnderCompositionAdicStar.{u} P)
    (hchart : TopologicalRing.PropertyIsStableUnderCompositionAdicStar.{u} P →
      ChartPropertyIsStableUnderComposition B S hS TopologicalRing.IsAdicStar P)
    (h31 : SourceCoverImpliesEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hZ : IsFormalAlgebraicSpace B S hS Z)
    (hpbg : HasFormalAlgebraicSpaceChartPullbacks B S hS g)
    (hpbf : HasFormalAlgebraicSpaceChartPullbacks B S hS f)
    (hpbfg : HasFormalAlgebraicSpaceChartPullbacks B S hS (f ≫ g))
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P f)
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P g) :
    HasPropertyAfterTargetCover B S hS TopologicalRing.IsAdicStar P (f ≫ g) :=
  hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P
    (f ≫ g) hZ hpbfg
    (hasPropertyOnEveryAffineEtaleDiagram_comp_adicStar B S hS P hP hchart h31 f g hZ hpbg hpbf
      hf hg)

end AlgebraicGeometry.FormalSpace

end
