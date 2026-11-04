module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineQuasiInverse

/-!
# The comparison functor over an affine base is an equivalence

[Stacks, Tag 06ZJ] says that for `S = Spec A` affine the category of adequate `𝒪`-modules on
`(Sch/S)_τ` is equivalent to the category of adequate module-valued functors on the
`A`-algebras of the site. This module states that equivalence for the source's own comparison
functor `𝓕 ↦ F_{𝓕, A}`.

## Main results

* `Stacks.Adequate.isEquivalence_adequateComparison` — [Stacks, Tag 06ZJ]: the comparison
  functor `Stacks.Adequate.adequateComparison` is an equivalence of categories, with no
  hypothesis.

## Implementation notes

Both halves of the equivalence are already proved, in two modules neither of which imports the
other, which is why this one exists. The comparison functor and the identification of it with
the affine-section functor are `Stacks.Adequate.adequateComparison` and
`Stacks.Adequate.adequateComparison_ι` of
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AffineComparison.lean`; that any
functor carrying such an identification is an equivalence is
`Stacks.Adequate.isEquivalence_of_affineSectionsFunctor` of
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AffineQuasiInverse.lean`, whose two
halves are full faithfulness of the affine-section functor over an affine base and the
quasi-inverse `Stacks.Adequate.exists_isAdequate_affineSectionsFunctor_iso`. All this module
does is feed the one to the other.

`Stacks.Adequate.adequateComparison_ι` is an equality of functors, proved by `rfl`, so the
isomorphism the hypothesis asks for is its `CategoryTheory.eqToIso`, in that direction.

The statement is at the value universe `u` of the site, which is where
`Stacks.Adequate.isEquivalence_of_affineSectionsFunctor` is stated: its essential surjectivity
produces the adequate `𝒪`-module as a kernel `Ker(M^a → N^a)` of associated modules, and the
associated-module construction runs through `AlgebraicGeometry.tilde`, which takes a
`ModuleCat.{u} A`. The comparison functor itself is available at every value universe
`max u m`, so it is instantiated here at `m = u`.

## References

* [Stacks Project, Tag 06ZJ](https://stacks.math.columbia.edu/tag/06ZJ)
* [Stacks Project, Tag 06VI](https://stacks.math.columbia.edu/tag/06VI)
* [Stacks Project, Tag 06UT](https://stacks.math.columbia.edu/tag/06UT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Adequate

/-- **[Stacks, Tag 06ZJ].** For `S = Spec A` affine, the comparison functor
`𝓕 ↦ F_{𝓕, A}` from the category `Adeq(𝒪)` of adequate `𝒪`-modules on `(Sch/S)_τ` to the
category of adequate module-valued functors on the `A`-algebras of the site is an equivalence
of categories. So the two categories are equivalent, by the source's own comparison.

Full faithfulness is full faithfulness of the affine-section functor over an affine base and
essential surjectivity is the quasi-inverse
`Stacks.Adequate.exists_isAdequate_affineSectionsFunctor_iso`, which builds the adequate
`𝒪`-module from an exact sequence `0 → F → M̲ → N̲` as `Ker(M^a → N^a)`; both are packaged in
`Stacks.Adequate.isEquivalence_of_affineSectionsFunctor`, and
`Stacks.Adequate.adequateComparison_ι` is the identification that theorem asks for. -/
@[stacks 06ZJ "the equivalence itself: the comparison functor 𝓕 ↦ F_{𝓕, A} from adequate
𝒪-modules on (Sch/Spec A)_τ to adequate module-valued functors on the A-algebras of the site is
an equivalence of categories, with no hypothesis, at the value universe u of the site. The
functor is `Stacks.Adequate.adequateComparison`, which carries the tag for the functor alone;
full faithfulness and essential surjectivity are
`Stacks.Adequate.fullyFaithful_of_affineSectionsFunctor` and
`Stacks.Adequate.essSurj_of_affineSectionsFunctor`, the latter being the quasi-inverse the
source builds from an exact sequence 0 → F → M̲ → N̲"]
public theorem isEquivalence_adequateComparison {τ : CoveringTopology} {A : CommRingCat.{u}}
    (B : BigSite τ (Spec A)) : (adequateComparison.{u, u} B).IsEquivalence :=
  isEquivalence_of_affineSectionsFunctor B (eqToIso (adequateComparison_ι.{u, u} B))

end Stacks.Adequate

end
