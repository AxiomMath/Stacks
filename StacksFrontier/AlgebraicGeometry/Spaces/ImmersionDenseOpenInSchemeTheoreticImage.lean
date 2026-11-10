module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ImmersionSchemeTheoreticallyDenseOpen

/-!
# An immersion is a scheme-theoretically dense open subspace of its scheme-theoretic image

Let `S` be a scheme contained in a big fppf site `B` and let `h : Z ⟶ X` be an immersion of
algebraic spaces over `S` which is either quasi-compact or has reduced source.  Write `Z̄` for
the scheme-theoretic image of `h` of Stacks 082X, which is a closed subspace of `X`.  This file
states the whole of **Stacks 088G** as a single result: the morphism `Z ⟶ Z̄` is an open
immersion, it identifies `Z` with its range, that range is an open subspace of `Z̄`, that open
subspace is scheme-theoretically dense in `Z̄` in the sense of Stacks 0834, and the points of
`Z` are topologically dense in the points of `Z̄`.

The source's hypothesis "`Z` is reduced" is `AlgebraicGeometry.Space.HasEtaleLocalProperty` for
reducedness of schemes, which is how an étale-local property of the charts of an algebraic space
is expressed throughout this development, and is the hypothesis part (1) of Stacks 0830 carries.
The identification of `Z` with its range is `CategoryTheory.Subfunctor.toRange` being an
isomorphism; it follows from the first assertion, an open immersion of presheaves on the big
fppf site being a monomorphism.

The five assertions are proved one at a time in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/ImmersionSchemeTheoreticallyDenseOpen.lean`,
all of them from the one property shared by the two hypotheses: under either of them the
formation of the scheme-theoretic image commutes with étale localization of the target, which
is part (3) of Stacks 082Z in the quasi-compact case and part (2) of Stacks 0830 in the reduced
case.  This file only assembles them under the source's hypotheses.

## Main results

* `AlgebraicGeometry.Space.isOpenImmersion_and_dense_toSchemeTheoreticImage_of_qc_or_reduced`:
  the whole of Stacks 088G, all of its assertions together, for an immersion of algebraic spaces
  over a scheme which is quasi-compact or has reduced source.

## References

* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 0830](https://stacks.math.columbia.edu/tag/0830)
* [Stacks Project, Tag 0834](https://stacks.math.columbia.edu/tag/0834)
* [Stacks Project, Tag 088G](https://stacks.math.columbia.edu/tag/088G)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- **Stacks 088G.** Let `S` be a scheme and let `h : Z ⟶ X` be an immersion of algebraic
spaces over `S`.  Assume either that `h` is quasi-compact or that `Z` is reduced, and let
`Z̄ ⊆ X` be the scheme-theoretic image of `h`.  Then the morphism `Z ⟶ Z̄` is an open immersion
which identifies `Z` with a scheme-theoretically dense open subspace of `Z̄`; moreover `Z` is
topologically dense in `Z̄`.

Spelled out, the five assertions are: the morphism onto the scheme-theoretic image is an open
immersion; it is an isomorphism onto its range, which is the identification of `Z` with a
subspace of `Z̄`; that range is an open subspace of `Z̄`; it is scheme-theoretically dense in
`Z̄`; and the induced map on points has dense range.

Each is proved separately in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/ImmersionSchemeTheoreticallyDenseOpen.lean`,
the identification being the only one not stated there: it is
`CategoryTheory.Subfunctor.toRange` of the morphism onto the image, which is an isomorphism
because that morphism is an open immersion and hence a monomorphism. -/
@[stacks 088G]
theorem isOpenImmersion_and_dense_toSchemeTheoreticImage_of_qc_or_reduced
    {Z X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    (hX : IsAlgebraicSpace B S hS X) (h : Z ⟶ X) (hh : IsImmersion B S hS h)
    (hq_or_hr : IsQuasiCompact B S hS h ∨
      HasEtaleLocalProperty B S hS Z (fun W : Scheme.{u} => IsReduced W)) :
    IsOpenImmersion B S hS (toSchemeTheoreticImage B S hS h) ∧
      IsIso (Subfunctor.toRange (toSchemeTheoreticImage B S hS h)) ∧
      IsOpenSubspace B S hS (Subfunctor.range (toSchemeTheoreticImage B S hS h)) ∧
      IsSchemeTheoreticallyDense B S hS (Subfunctor.range (toSchemeTheoreticImage B S hS h)) ∧
      DenseRange (pointsMap B S hS Z (toSchemeTheoreticImage B S hS h)) := by
  have hopen := isOpenImmersion_toSchemeTheoreticImage_of_qc_or_reduced B S hS hZ hX h hh hq_or_hr
  have : Mono (toSchemeTheoreticImage B S hS h) := mono_of_isOpenImmersion B S hS _ hopen
  exact ⟨hopen, inferInstance,
    isOpenSubspace_range_toSchemeTheoreticImage_of_qc_or_reduced B S hS hZ hX h hh hq_or_hr,
    isSchemeTheoreticallyDense_range_toSchemeTheoreticImage_of_qc_or_reduced B S hS hZ hX h hh
      hq_or_hr,
    denseRange_pointsMap_toSchemeTheoreticImage_of_qc_or_reduced B S hS hZ hX h hq_or_hr⟩

end AlgebraicGeometry.Space

end
