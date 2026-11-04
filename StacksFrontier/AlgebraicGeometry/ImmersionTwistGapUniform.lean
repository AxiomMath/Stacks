module

public import StacksFrontier.AlgebraicGeometry.StalkwiseGeneration.Ample
public import StacksFrontier.AlgebraicGeometry.VeryAmplePowersUniformDegree.Basic

/-!
# Stacks Tag 01VS holds in every situation

`Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform` is Tag 01VS quantified over the
situation, which is the form Tag 01VU's proof needs: it applies Tag 01VT to the restriction of a
morphism over each member of an affine covering of the base, a different situation each time.
It is a theorem, not a hypothesis, because an ample invertible module generates a twist gap at
every stalk.

## Main results

* `Stacks.VeryAmplePowersUniformDegree.immersionTwistGapUniform`: the uniform twist-gap
  statement holds, with no hypothesis.

## Implementation notes

Three modules of the ample cluster each proved this, in their own namespaces and from the same
one-line application of `Stacks.StalkwiseGeneration.immersionTwistGap_of_isAmple`. It lives here
instead, in the namespace of the predicate it discharges, in a module importing only the
predicate and that lemma -- which every one of those modules already reaches, so the merge costs
no module in any of their closures.
-/

@[expose] public section

universe u

namespace Stacks.VeryAmplePowersUniformDegree

/-- **Stacks Tag 01VS, in every situation.** An ample invertible module generates a twist gap at
every stalk, so the uniform statement holds with no hypothesis. -/
public theorem immersionTwistGapUniform : ImmersionTwistGapUniform.{u} :=
  fun _ _ g N _ hN hg =>
    Stacks.StalkwiseGeneration.immersionTwistGap_of_isAmple g N hN hN hg

end Stacks.VeryAmplePowersUniformDegree

end
