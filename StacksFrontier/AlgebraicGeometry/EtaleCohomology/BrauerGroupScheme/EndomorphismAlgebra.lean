module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.EndomorphismAlgebra.ModuleConjugation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.EndomorphismAlgebra.IntertwinerSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.EndomorphismAlgebra.LocalIntertwiner
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.EndomorphismAlgebra.InvertibleTwist

/-!
# Endomorphism algebras determine a vector bundle up to invertible twist

Let `S` be a scheme and let `F` and `G` be finite locally free sheaves of `𝒪_S`-modules of
positive rank. An isomorphism of their endomorphism algebra sheaves forces `F` and `G` to differ
only by an invertible sheaf: there is an invertible `L` and an isomorphism `F ⊗ L ≅ G`, and that
isomorphism realizes the given algebra isomorphism by conjugation.

## Main results

* `Stacks.EtaleCohomology.exists_invertible_tensor_iso_of_endomorphism_algebra_iso` gives the
  invertible twist and its compatibility with the prescribed algebra isomorphism.

## Implementation notes

The given isomorphism of endomorphism algebra sheaves is an isomorphism of the underlying module
sheaves preserving identity and composition on every open. The conclusion characterizes
conjugation on pure local tensors; these generate the tensor-product sheaf locally. Positive rank
is expressed by a finite locally free presentation whose local basis index types are inhabited.

The twist is constructed, not guessed: `L` is the subsheaf of `SheafHom(F, G)` of sections that
intertwine the two endomorphism sheaves along the given isomorphism, and the comparison map
`F ⊗ L ⟶ G` is evaluation. The work is to show that `L` is locally free of rank one and that
evaluation is locally bijective. Both are checked over an open on which `F` and `G` are
simultaneously free of positive finite rank and on which a chosen matrix coefficient of a
rank-one projection has become a unit; over such an open the local linear algebra produces a
linear equivalence conjugating the algebra isomorphism, and the finite basis of the endomorphism
module of sections is what makes that identity descend to every smaller open. Invertibility of
`L` is then `Stacks.SheafOfModules.isInvertible_of_coversTop_iso_unit`: the local basis section
gives a scalar-multiplication map that trivializes `L` on that neighbourhood, and the
neighbourhoods cover.

`TopCat.Sheaf` is a semireducible definition, so the sheaf of rings `structureSheaf Rc` of a
sheaf of commutative rings is not accepted where instance search expects a sheaf on the site of
opens, and the ring of sections over an open has several spellings that only full unfolding
identifies. Three devices keep the proofs inside the default transparency. The linear algebra of
a section basis is isolated in `basis_coord_map_of_apply` and `basis_smulRight_map`, stated over
bare types where the spellings cannot arise. `sectionLinearEquivOfIso` fixes the scalar ring of
the comparison isomorphism on sections, so that transporting a basis along it is an equality the
simplifier can use. Elsewhere the offending scalar ring is written out as a type ascription, and
the instances that identify two spellings of one action are recorded as instances, here for a
ringed space and in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafHomLeftExact.lean` for the
`SheafHom` API.

## References

* [Stacks Project, Tag 0A2K](https://stacks.math.columbia.edu/tag/0A2K)
-/
