module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineLocalUnconditional
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSections

/-!
# Adequate modules over an affine base and adequate module-valued functors

Let `S = Spec(A)` be affine. [Stacks, Tag 06ZJ] says that the category of adequate
`𝒪`-modules on `(Sch/S)_τ` is equivalent to the category of adequate module-valued functors on
`Alg_A`. The comparison in one direction is `𝓕 ↦ F_{𝓕, A}`, the affine-section functor, and
[Stacks, Tag 06VI] is what makes it land in adequate functors.

This module packages that comparison as a functor of categories. The affine-section functor
`Stacks.Adequate.affineSectionFunctor` is defined on objects only; it is upgraded to a functor
`Stacks.Adequate.affineSectionsFunctor` on all sheaves of modules in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AffineSections.lean`, and here it is
restricted to the two full subcategories cut out by adequacy.

## Main definitions

* `Stacks.Adequate.adequateComparison` — the comparison functor of [Stacks, Tag 06ZJ] from
  adequate `𝒪`-modules on `(Sch/Spec A)_τ` to adequate module-valued functors on the
  `A`-algebras of the site.

## Main results

* `Stacks.Adequate.adequateComparison_ι` — the comparison functor is the affine-section functor:
  composing it with the two subcategory inclusions returns `affineSectionsFunctor`.

## Implementation notes

The step the source's proof cites verbatim — "given an adequate module `𝓕` the functor
`F_{𝓕, A}` is adequate by Lemma 06VI" — is discharged here outright by
[Stacks, Tag 06VI], `Stacks.Adequate.isAdequate_affineSectionFunctor`, which is unconditional:
all three steps of its proof are theorems, `Stacks.Adequate.standardAffineRefinement`,
`Stacks.Adequate.affineSectionRestriction` and `Stacks.Adequate.standardAffineDescent`. The
membership of the base in the site, which Tag 06VI also asks for, is the field `base_mem` of
`Stacks.Adequate.BigSite`.

That the affine-section functor itself is in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AffineSections.lean` and not here is
what lets this module apply Tag 06VI at all: the Čech machinery proving Tag 06VI's third step
uses the functor, so it sits between that module and this one, and a comparison functor
declared beside the affine-section functor would be inside Tag 06VI's own import closure.

The value universe of the sheaves of modules is `max u m` rather than an independent `m`,
matching [Stacks, Tag 06VQ] in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/Abelian.lean` and the library's Tag 06VI
itself. It is not a choice: the second step of Tag 06VI's proof goes through
[Stacks, Tag 06V9], `AdequateFunctor.IsAdequate.restrictBaseOn`, which raises the values of a
module-valued functor to include the universe of the source ring when it restricts the base
ring, so Tag 06VI is available exactly at the value universes that contain `u`.

The quasi-inverse is not constructed as a functor, and deliberately so. The source builds it
from an adequate functor `F` by choosing an exact sequence `0 → F → M → N` and taking
`𝓕 = Ker(M^a → N^a)`, and then omits the proof that the two constructions are mutually
inverse. A construction that chooses the exact sequence does not define a functor without a
proof that the result is independent of the choice, which the source does not give; the
choice-free route is to prove the comparison functor fully faithful and essentially surjective,
where the exact sequence is chosen only inside the proof of an existence statement. That is the
route the library takes. The associated module `M^a` on a `Stacks.Adequate.BigSite` and the
adequacy of a kernel `Ker(M^a → N^a)`, which is [Stacks, Tag 06VK], are
`Stacks.Adequate.associatedTilde` and `Stacks.Adequate.isAdequate_kernel_associatedTilde`, and
the existence statement is `Stacks.Adequate.exists_isAdequate_affineSectionsFunctor_iso`, all
in `StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AffineQuasiInverse.lean`. That the
comparison functor defined here is therefore an equivalence is
`Stacks.Adequate.isEquivalence_adequateComparison` of
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AffineEquivalence.lean`, which is where
the tag for the equivalence sits: neither this module nor `AffineQuasiInverse.lean` imports the
other, so the two halves meet only there.

## References

* [Stacks Project, Tag 06ZJ](https://stacks.math.columbia.edu/tag/06ZJ)
* [Stacks Project, Tag 06VI](https://stacks.math.columbia.edu/tag/06VI)
* [Stacks Project, Tag 06UT](https://stacks.math.columbia.edu/tag/06UT)
* [Stacks Project, Tag 07AH](https://stacks.math.columbia.edu/tag/07AH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u m

namespace Stacks.Adequate

/-- **[Stacks, Tag 06ZJ], the comparison functor.** For `S = Spec A` affine, the affine-section
construction `𝓕 ↦ F_{𝓕, A}` is a functor from the category `Adeq(𝒪)` of adequate `𝒪`-modules on
`(Sch/Spec A)_τ` to the category of adequate module-valued functors on the `A`-algebras of the
site.

That the construction lands in adequate functors is [Stacks, Tag 06VI], which the source cites
here and which the library proves outright. -/
public noncomputable def adequateComparison {τ : CoveringTopology} {A : CommRingCat.{u}}
    (B : BigSite τ (Spec A)) :
    (adequate.{u, max u m} B).FullSubcategory ⥤
      (adequateOn.{u, max u m} A (schemeSizeBelow B.cutoff)).FullSubcategory :=
  ObjectProperty.lift _
    ((adequate.{u, max u m} B).ι ⋙ affineSectionsFunctor B A (𝟙 (Spec A)))
    fun F ↦ isAdequate_affineSectionFunctor.{u, m} B F.obj F.property A (𝟙 (Spec A)) B.base_mem

/-- The comparison functor of [Stacks, Tag 06ZJ] is the affine-section functor: composing it
with the two subcategory inclusions returns `Stacks.Adequate.affineSectionsFunctor`. -/
public theorem adequateComparison_ι {τ : CoveringTopology} {A : CommRingCat.{u}}
    (B : BigSite τ (Spec A)) :
    adequateComparison.{u, m} B ⋙ (adequateOn.{u, max u m} A (schemeSizeBelow B.cutoff)).ι =
      (adequate.{u, max u m} B).ι ⋙ affineSectionsFunctor B A (𝟙 (Spec A)) := rfl

end Stacks.Adequate

end
