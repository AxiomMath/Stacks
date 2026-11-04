module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinBivariantClass.BivariantClass
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinBivariantClass.Cap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinBivariantClass.Composite
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinBivariantClass.GysinComm

/-!
# Stacks 0ERP: the Gysin map of a triple is a bivariant class of degree 1

In Situation 0EDT let `X/B` be good and `(ℒ, σ, i : E → X)` a triple as in Definition 0ER1.
Stacks 0ERP asserts that the rule `(g : X' ⟶ X) ↦ (i')^* : CH_k(X') ⟶ CH_{k-1}(E')`,
`E' = E ×_X X'`, is a bivariant class of degree 1; its proof cites Lemmas 0ERA, 0ER5, 0ER6 and
0ERC.  This module proves it over the constructed Chow groups
(`AlgebraicGeometry.Space.exists_bivariantClassCanonical_gysin`, against
`AlgebraicGeometry.Space.BivariantClassCanonical` of Stacks 0ERJ).

* **Inverse images of sections along composites.**  The inverse image `f^*s` of a global section
  along a composite is the iterated inverse image, through the comparison `f^*g^*M ≅ (f ≫ g)^*M`
  of Stacks 03LU, and the Weil divisors of Stacks 0EQE of the two agree.
* **Stacks 0ER3: `Z(g^*σ) = g^{-1}(E) = X' ×_X E`**, from
  `AlgebraicGeometry.Space.zeroScheme_modulePullback_eq_preimage`.
* **The cap operation** `gysinBivariantCap` of the class of Stacks 0ERP on a test space: the
  Gysin homomorphism of Stacks 0ERA of the pulled-back triple, carried to `E ×_X X'`.
* **The three axioms of Stacks 0ERJ** for it: (1) from Stacks 0ER5, (2) from Stacks 0ER6, and
  (3) from Stacks 0ERC on the test space, with Stacks 0ER5 into the vanishing locus `Z(t')` of
  the axiom.  Over the constructed Chow groups these are
  `AlgebraicGeometry.Space.chowClassCanonical_sectionGysin_properPushforward_eq`,
  `AlgebraicGeometry.Space.chowClassCanonical_gysinCycleMap_flatPullbackMap` and
  `AlgebraicGeometry.Space.chowClassCanonical_gysinCycleMap_gysinCycleMap_comm`.
* **Proper pushforward along a closed immersion** is the pushforward of the localization
  sequence, which identifies the transport of Chow groups along `Z(g^*σ) ≅ E ×_X X'` with proper
  pushforward.

## Implementation notes

The same closed subspace is written in two ways in the inputs of axiom (3): as the vanishing
locus spelled out, and through the abbreviations of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.BivariantCanonical`, with the structure morphism of
`D' = Z(t)` as `(ι ≫ g) ≫ p` or as `ι ≫ g ≫ p`.  Each change of spelling is made once, in a lemma
over abstract objects (`exists_chowClassCanonical_gysinCycleMap_properCyclePushforward_bivariant`,
`exists_properCyclePushforward_gysinCycleMap_structure_eq`), so that no unification between two
spellings is left to the elaborator.

## References

* [Stacks Project, Tag 0ERP](https://stacks.math.columbia.edu/tag/0ERP)
* [Stacks Project, Tag 0ERA](https://stacks.math.columbia.edu/tag/0ERA)
* [Stacks Project, Tag 0ERC](https://stacks.math.columbia.edu/tag/0ERC)
* [Stacks Project, Tag 0ERJ](https://stacks.math.columbia.edu/tag/0ERJ)
* [Stacks Project, Tag 0ER3](https://stacks.math.columbia.edu/tag/0ER3)
* [Stacks Project, Tag 0ER5](https://stacks.math.columbia.edu/tag/0ER5)
* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/
