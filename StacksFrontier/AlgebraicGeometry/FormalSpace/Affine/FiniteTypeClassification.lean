module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.FiniteTypeClassification.IdealBasis
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.FiniteTypeClassification.SystemStages
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.FiniteTypeClassification.ColimitFunctor
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.FiniteTypeClassification.AntiEquivalence

/-!
# Finite type affine formal algebraic spaces over a McQuillan affine formal algebraic space

Let `S` be a scheme and let `X` be a McQuillan affine formal algebraic space over `S`, presented
as the formal spectrum of a weakly admissible topological ring `A`. Fix a fundamental system
`(I_i)` of weak ideals of definition of `A`. **Stacks 0AL1** says that the category of inverse
systems `(B_i)` of finite type `A / I_i`-algebras whose transitions induce isomorphisms
`B_j / I_i B_j \cong B_i` is anti-equivalent to the category of finite type morphisms
`Y \to X` of affine formal algebraic spaces.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IdealBasis`: a fundamental system of weak ideals of definition
  of a topological ring, indexed by a preorder.
* `AlgebraicGeometry.FormalSpace.FiniteTypeAlgebraSystem`: the category `C` of the source — an
  inverse system of finite type algebras over the quotients of an ideal basis, each transition
  being reduction modulo the earlier ideal.
* `AlgebraicGeometry.FormalSpace.AffineFiniteTypeOver`: the category of finite type morphisms to
  `X` from affine formal algebraic spaces.

## Main results

* `AlgebraicGeometry.FormalSpace.finiteTypeAlgebraSystemAntiEquivalence`: **Stacks 0AL1**, the
  anti-equivalence of the two categories.
* `AlgebraicGeometry.FormalSpace.finiteTypeAlgebraSystemAntiEquivalence_functor_obj_hom`: the
  anti-equivalence sends an inverse system to the colimit of the spectra of its terms.

## Implementation notes

An inverse system is a functor `I ^op => CommRingCat` together with the structure
homomorphisms from the quotients of `A`; condition (2) of the source — that `B_j => B_i`
induces an isomorphism `B_j / I_i B_j => B_i` — is recorded as surjectivity of the transition
together with the computation of its kernel, which is the form the proof uses. Morphisms are
natural transformations commuting with the structure homomorphisms, which is what "compatible
systems of homomorphisms" means.

The geometric side is a full subcategory of the slice category `Over X` of fppf sheaves, cut out
by the conditions that the source is an affine formal algebraic space and the structure morphism
is of finite type; since the ambient category of fppf sheaves is already the one in which formal
algebraic spaces live, no intermediate category of formal algebraic spaces is needed.

The functor from inverse systems is the colimit of the spectra of the terms, formed over the
index of the ideal basis; the ideal basis is reindexed by its image in the weak ideals of
definition of `A` so that the index lands in `Type (u + 1)`, where the colimit of sheaves is
taken. The anti-equivalence is obtained from fullness and faithfulness of that functor together
with the identification of its essential image, which is the content of the source's two
mutually quasi-inverse constructions.

## References

* [Stacks Project, Tag 0AL1](https://stacks.math.columbia.edu/tag/0AL1)
-/
