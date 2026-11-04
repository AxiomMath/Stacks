module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.FiniteLocallyFreeDescent
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.FppfLocalAtSource

/-!
# Pseudo-coherence is local on the source for the fppf topology

Pseudo-coherence of morphisms of schemes is local on the source for the fppf topology, which is
Tag 0699. The reduction of that statement to descent along a surjective finite locally free
morphism is `AlgebraicGeometry.pseudoCoherent_isLocalAtSource_fppf_of_finiteLocallyFree_descent`,
and that descent is
`AlgebraicGeometry.pseudoCoherent_of_comp_surjective_finiteLocallyFree`; what is added here is
the composition of the two.

Tag 0699 strengthens Tag 0698, source locality for the syntomic topology
(`AlgebraicGeometry.PseudoCoherent.isLocalAtSource_syntomicPrecoverage`). It is a genuine
strengthening and not a formal consequence: a syntomic covering is an fppf covering, so source
locality for the fppf topology implies it for the syntomic one and not conversely.

## Main results

* `AlgebraicGeometry.PseudoCoherent.isLocalAtSource_fppfPrecoverage`: **Tag 0699**.

## Implementation notes

Both inputs are stated for arbitrary schemes, so nothing has to be localized here and the proof
is the composition. The refinement of an fppf covering by Zariski open coverings and surjective
finite locally free morphisms, Tag 05WN, is used inside the first input rather than here.

## References

* [The Stacks Project, Lemma 37.60.14 (0699)](https://stacks.math.columbia.edu/tag/0699)
* [The Stacks Project, Lemma 37.60.13 (0698)](https://stacks.math.columbia.edu/tag/0698)
* [The Stacks Project, Lemma 35.35.1 (05WN)](https://stacks.math.columbia.edu/tag/05WN)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks 0699.** Pseudo-coherence of morphisms of schemes is local on the source for the
fppf topology: a morphism is pseudo-coherent exactly when its composites with the members of an
fppf covering of its source are.

This is `AlgebraicGeometry.pseudoCoherent_isLocalAtSource_fppf_of_finiteLocallyFree_descent`,
the reduction of the source's statement to descent along a surjective finite locally free
morphism, with that descent discharged by
`AlgebraicGeometry.pseudoCoherent_of_comp_surjective_finiteLocallyFree`. -/
@[stacks 0699]
instance PseudoCoherent.isLocalAtSource_fppfPrecoverage :
    MorphismProperty.IsLocalAtSource (@PseudoCoherent.{u} : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  pseudoCoherent_isLocalAtSource_fppf_of_finiteLocallyFree_descent
    fun h f hsurj hh hcomp =>
      pseudoCoherent_of_comp_surjective_finiteLocallyFree h f hsurj hh hcomp

end AlgebraicGeometry

end
