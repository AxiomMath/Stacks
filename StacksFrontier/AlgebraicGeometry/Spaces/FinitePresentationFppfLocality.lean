module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSource.Fppf
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFppfSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback

/-!
# Local finite presentation of morphisms of algebraic spaces is fppf local on source and target

Let `S` be a scheme contained in a big fppf site `B`. A morphism of algebraic spaces over `S`
is locally of finite presentation when the chart condition
`AlgebraicGeometry.Space.IsLocallyOfFinitePresentation` of **Stacks 03XP**, part (1), holds. That
condition is local on the source for the fppf topology of **Stacks 03YH** (**Stacks 06EV**), and
it is local on the target for that topology.

Source locality is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/LocalOnSource/Fppf.lean`, which this module
re-exports; it is the fppf case of **Stacks 06ER** applied to local finite presentation of
morphisms of schemes, which is étale local on the source and target (**Stacks 04R3**, the locally
of finite presentation case) and fppf local on the source (**Stacks 036N**).

Target locality is the argument the tree already makes for flatness in
`StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality`, transposed from fpqc to fppf covering
families. In one direction, local finite presentation is stable under base change
(**Stacks 03XR**). In the other, the base changes of the given morphism along the members of the
covering form an fppf covering of its source (**Stacks 03Y9**), so by source locality it suffices
that each composite `X ×_Y Yᵢ ⟶ X ⟶ Y` be locally of finite presentation; that composite is the
other projection followed by `Yᵢ ⟶ Y`, and both of those are locally of finite presentation, so
composition (**Stacks 03XQ**) applies.

## Main results

* `AlgebraicGeometry.Space.isFppfCovering_pullback_fst`: **Stacks 03Y9**, base change read
  against the chosen pullbacks of the category of algebraic spaces.
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_isLocalAtTarget_fppf`: target locality
  for the fppf topology.

## Implementation notes

The step which does *not* transpose from the flat argument is the last one. An fpqc covering
family has flat members only, so for flatness the composite `X ×_Y Yᵢ ⟶ X ⟶ Y` is flat after
flat, which is flat; for local finite presentation the same composite would be locally of finite
presentation after flat, which is not locally of finite presentation. An **fppf** covering family
has members which are flat *and* locally of finite presentation, and that is what makes the
composite come out right. This is the reason the statement is about the fppf topology, and the
reason it does not follow from the fpqc form in the way flatness and smoothness do.

Target locality is **deliberately untagged**. The corresponding tag is **Stacks 041T**, which
asserts that local finite presentation is fpqc local on the base — a strictly stronger statement,
whose proof in the source goes through the affine criterion of **Stacks 041J** and the ring-level
descent of **Stacks 02KY** rather than through covering families. Tagging the fppf form with 041T
would record a weaker statement as though that tag were proved. The fppf form is nonetheless the
one the relative properties of **Stacks 03YK** ask for, and it is registered as an instance for
them.

Both localities are registered as instances, which is the form the relative properties of
Chapters 100 and 101 consume them in, and which lets
`AlgebraicGeometry.Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation` discharge its
source-locality hypothesis.

## References

* [Stacks Project, Tag 036N](https://stacks.math.columbia.edu/tag/036N)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 03XQ](https://stacks.math.columbia.edu/tag/03XQ)
* [Stacks Project, Tag 03XR](https://stacks.math.columbia.edu/tag/03XR)
* [Stacks Project, Tag 03Y9](https://stacks.math.columbia.edu/tag/03Y9)
* [Stacks Project, Tag 041T](https://stacks.math.columbia.edu/tag/041T)
* [Stacks Project, Tag 06ER](https://stacks.math.columbia.edu/tag/06ER)
* [Stacks Project, Tag 06EV](https://stacks.math.columbia.edu/tag/06EV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

/-- **Stacks 03Y9**, base change, read against the chosen pullbacks of the category of algebraic
spaces over `S`: the base change of an fppf covering family along a morphism of algebraic
spaces, taken as the family of *first* projections out of the chosen pullbacks, is an fppf
covering of the new base.

Flatness and local finite presentation of each projection are the base-change stabilities of
Stacks 03MO and Stacks 03XR; joint surjectivity holds because a point of the new base and a
point of a member lying over the same point of the old base are the images of a point of the
pullback. -/
theorem isFppfCovering_pullback_fst
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {Y : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
    (g : ∀ i, Yi i ⟶ Y)
    (hcover : IsFppfCovering B S hS (fun i => (Yi i).1) (fun i => (g i).hom))
    (X : AlgebraicSpaces B S hS) (f : X ⟶ Y) :
    IsFppfCovering B S hS (fun i => (pullback f (g i)).1)
      (fun i => (pullback.fst f (g i)).hom) := by
  let Pflat : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun ⦃A C⦄ (q : A ⟶ C) => IsFlat B S hS q.hom
  let Pfp : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun ⦃A C⦄ (q : A ⟶ C) => IsLocallyOfFinitePresentation B S hS q.hom
  have : Pflat.IsStableUnderBaseChange := isFlat_isStableUnderBaseChange B S hS
  have : Pfp.IsStableUnderBaseChange := isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  refine ⟨X.property, fun i => (pullback f (g i)).property,
    fun i => MorphismProperty.pullback_fst (P := Pflat) f (g i) (hcover.flat i),
    fun i => MorphismProperty.pullback_fst (P := Pfp) f (g i)
      (hcover.locallyOfFinitePresentation i), Set.eq_univ_of_forall fun x => ?_⟩
  have hmem : pointsMap B S hS X.1 f.hom x ∈
      ⋃ i, Set.range (pointsMap B S hS (Yi i).1 (g i).hom) :=
    hcover.jointly_surjective ▸ Set.mem_univ _
  obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hmem
  obtain ⟨w, hwx, -⟩ := exists_point_of_isPullback B S hS
    (IsPullback.of_hasPullback f (g i)) x y hy.symm
  exact Set.mem_iUnion.mpr ⟨i, w, hwx⟩

end AlgebraicGeometry.Space

end
