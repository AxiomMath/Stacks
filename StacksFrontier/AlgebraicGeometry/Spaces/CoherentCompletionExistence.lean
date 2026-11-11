module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.CoherentCompletionExistence

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionFormalPullbackCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionLeftExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAffineComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageChartSections

/-!
# Algebraizing a map to a completion on an algebraic space: existence

This module declares nothing.  It collects, through its imports, the existence half of Stacks
08BB and the modules it is proved from.

Let `F` be a Noetherian algebraic space over a scheme `S`, let `𝓘 ⊆ 𝒪_F` be a quasi-coherent
sheaf of ideals on its small étale site, let `G` be a coherent `𝒪_F`-module, let `E` be a
coherent `𝓘`-adic system and let `α : E ⟶ G^∧` be a map whose levelwise kernels and cokernels
are annihilated by a power of `𝓘`.  The **existence** half of Stacks 08BB says that there are a
coherent module `M`, a map `a : M ⟶ G` whose kernel and cokernel are annihilated by a power of
`𝓘`, and an isomorphism `β : E ≅ M^∧` with `α = a^∧ ∘ β`.  Together with the uniqueness half
`AlgebraicGeometry.Space.existsUnique_iso_of_algebraization_of_isNoetherian` this is the whole
of Stacks 08BB, which is stated and registered as
`AlgebraicGeometry.Space.exists_algebraization_and_existsUnique_iso`.

The existence half is `AlgebraicGeometry.Space.C1573.exists_algebraization`, proved in the
first import of this module, where `M` is the formal pullback `G ×_{lim G / 𝓘 ⁿ⁺¹ G} lim E` of
`AlgebraicGeometry.Space.formalPullback` and `a` is its projection to `G`; on the affine étale
charts this is the module of the formal glueing of Stacks 0889.

## References

* [Stacks Project, Tag 08BB](https://stacks.math.columbia.edu/tag/08BB)
* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
-/
