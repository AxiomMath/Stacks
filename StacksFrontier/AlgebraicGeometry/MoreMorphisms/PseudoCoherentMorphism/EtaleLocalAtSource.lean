module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.SyntomicDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Etale

/-!
# Source locality of pseudo-coherence for the étale topology

Pseudo-coherence of a morphism of schemes can be tested on an étale covering of its source. This
is weaker than source locality for the syntomic topology, Tag 0698, and follows from it because
an étale morphism is syntomic (Tag 02GQ), so an étale covering family is a syntomic covering
family.

## Main results

* `AlgebraicGeometry.PseudoCoherent.isLocalAtSource_etalePrecoverage`: pseudo-coherence of
  morphisms of schemes is local on the source for the étale topology.

## Implementation notes

The statement is not a numbered result of the source. The comparison of covering families it
rests on, `AlgebraicGeometry.Scheme.etalePrecoverage_le_syntomicPrecoverage`, is the
covering-family form of Tag 02GQ and lives beside `AlgebraicGeometry.syntomic_of_etale`, which
carries that tag. Source locality for a coarser topology is a formal
consequence of source locality for a finer one,
`CategoryTheory.MorphismProperty.IsLocalAtSource.of_le`, and the source states only the syntomic
and fppf cases (Tags 0698 and 0699); the étale case is what the chart criterion of Tag 04R2
consumes, so it is recorded here rather than inferred at each use.

## References

* [The Stacks Project, Lemma 29.36.3 (02GQ)](https://stacks.math.columbia.edu/tag/02GQ)
* [The Stacks Project, Lemma 37.60.13 (0698)](https://stacks.math.columbia.edu/tag/0698)
* [The Stacks Project, Lemma 35.33.1 (04R2)](https://stacks.math.columbia.edu/tag/04R2)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Pseudo-coherence of morphisms of schemes is local on the source for the étale topology: a
morphism is pseudo-coherent exactly when its composites with the members of an étale covering of
its source are.

Pseudo-coherence is local on the source for the syntomic topology by Tag 0698, and an étale
covering family is a syntomic covering family. -/
instance PseudoCoherent.isLocalAtSource_etalePrecoverage :
    MorphismProperty.IsLocalAtSource (@PseudoCoherent.{u} : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage :=
  MorphismProperty.IsLocalAtSource.of_le Scheme.etalePrecoverage_le_syntomicPrecoverage

end AlgebraicGeometry

end
