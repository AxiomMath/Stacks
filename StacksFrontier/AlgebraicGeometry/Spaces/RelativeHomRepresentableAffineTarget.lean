module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeHomRepresentableAffineTarget.HomEquivalences
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeHomRepresentableAffineTarget.SliceRepresentability
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeHomRepresentableAffineTarget.AlgebraicSpace

/-!
# The relative morphism functor of a coproduct-of-affines target

Let `S` be a scheme contained in a big fppf site `B`, and let `z : Z ⟶ Q` and `x : X ⟶ Q` be
morphisms of objects of the big fppf site over `S`. If the scheme underlying `z` is finite locally
free, the scheme underlying `Q` is separated, and the scheme underlying `X` is a disjoint union of
affine schemes, then the relative morphism functor `Mor_Q(Z, X)` of Stacks 05Y2 is represented by
an object of the site, hence an algebraic space over `S`.

That is the case of Stacks 05Y7 in which everything in sight is an object of the site, and it is
what the reductions of Stacks 05Y7 reduce *to*. This file also carries those reductions out, so
that Stacks 05Y7 is proved here for arbitrary algebraic spaces, with only the input from
Stacks 05XR carried as a hypothesis — that input is no longer an open assumption, it is the
theorem `AlgebraicGeometry.Space.isFibreSectionsAlgebraicEtale`, whose proof is downstream of
this file.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_of_coproductAffine`: the relative morphism
  functor of objects of the site, with a coproduct-of-affines target, is an algebraic space — it
  is represented by an object of the site.
* `AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_of_isFiniteLocallyFree_of_fibreSections`:
  **Stacks 05Y7** for arbitrary algebraic spaces, with the input from Stacks 05XR carried.
* `AlgebraicGeometry.isSeparated_of_coproduct_affine`: a disjoint union of affine schemes is
  separated, which is how the separatedness hypothesis is discharged in practice — the covering of
  Stacks 03FX produces charts of exactly that shape.
* `AlgebraicGeometry.Space.RelativeHomConstruction.ofSourceIso`: a realization of the relative
  morphism functor transported along an isomorphism of the source, which is what identifies the
  base change of `Z` along a chart of `Q` with the object of the site representing it.

## Implementation notes

Representability of `Mor_Q(Z, X)` **as a functor on the slice `Over Q` of all schemes** is
Stacks 0BL4, `Stacks.Morphisms.homFromFiniteLocallyFree_isRepresentable`: a finite set of points
of a disjoint union of affine schemes meets only finitely many summands, and a finite disjoint
union of affine schemes is affine, so the hypothesis of Stacks 0BL4 holds for a
coproduct-of-affines target.

Two things stand between that and the statement proved here.

* **The representing scheme must lie in the site.** The site consists of the schemes whose
  `AlgebraicGeometry.Scheme.size` is below a cutoff, so the representing scheme has to be given a
  size bound in terms of `Q` and `X`. It is obtained by covering the representing scheme by the
  representing schemes of the relative morphism functors of the affine opens of `X`, each of which
  is affine with a bound on the cardinality of its ring of global sections: the universal algebra
  of Stacks 05Y6 is a quotient of a polynomial algebra on `Γ(X) × ι` for `ι` a basis of `Γ(Z)`.
  `AlgebraicGeometry.RelativeHomAffineTarget.exists_bounded_universal_tensor_hom` is the
  construction of Stacks 05Y6 carrying that bound; separatedness of `Q` is what makes the
  restriction of `x` to an affine open of `X` an affine morphism, so that the bound applies.
* **The two spellings of the relative morphism functor must be identified.** The functor on the
  slice sends `T` to the `Q`-morphisms `T ⨯_Q Z ⟶ X`; the functor of Stacks 05Y2 sends an object of
  the site to a pair `(a, b)` of `AlgebraicGeometry.Space.RelativeMorphism`. The identification is
  `AlgebraicGeometry.RelativeHomAffineTarget.relativeHomRepresentableByOfOver`.

The reductions to that case are the source's own. A surjective étale chart `h_V ⟶ Q` with the
scheme underlying `V` a disjoint union of affine schemes (Stacks 03FX) makes the base separated;
Stacks 05Y4 identifies the relative morphism functor of the base-changed data with the base change
of `Mor_Q(Z, X)` along the chart, so Stacks 03Y3 reduces algebraicity to the base `h_V`. Over that
base the source is represented by an object of the site, because a finite locally free morphism is
affine and hence relatively representable, and the target is reduced to a disjoint union of affine
schemes by Stacks 03FX again and the reduction on the target of Stacks 05Y5.

## References

* [Stacks Project, Tag 05Y7](https://stacks.math.columbia.edu/tag/05Y7)
* [Stacks Project, Tag 05Y6](https://stacks.math.columbia.edu/tag/05Y6)
* [Stacks Project, Tag 0BL4](https://stacks.math.columbia.edu/tag/0BL4)

## Parts

* `StacksFrontier.AlgebraicGeometry.Spaces.RelativeHomRepresentableAffineTarget.HomEquivalences`
* `StacksFrontier.AlgebraicGeometry.Spaces.RelativeHomRepresentableAffineTarget.SliceRepresentability`
* `StacksFrontier.AlgebraicGeometry.Spaces.RelativeHomRepresentableAffineTarget.AlgebraicSpace`
-/
