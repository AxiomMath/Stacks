module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ConstructibleQuasiCompact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactConstructibleSets
import StacksCore.Tactic.StacksAttribute

/-!
# Constructible sheaves of sets on the small étale site are compact

Let `X` be a quasi-compact and quasi-separated scheme. Morphisms out of a constructible sheaf of
sets on `X_étale` commute with filtered colimits: for a filtered colimit `G = colim G_i` of
sheaves of sets, `Mor(F, G) = colim Mor(F, G_i)`. This is the sheaves-of-sets case of
Stacks 09Z4.

The proof is the one of the source. Stacks 09Y9 presents a constructible sheaf of sets as a
coequalizer of two maps between finite coproducts of sheaves represented by quasi-compact and
quasi-separated étale objects, and such a presentation forces compactness because each
representable is compact (part (4) of Stacks 0738) and finite colimits of compact objects are
compact.

Both halves are theorems in the namespace `AlgebraicGeometry`: the presentation is
`isConstructibleSetSheaf_iff_hasFiniteQCSRepresentableCoequalizerPresentation_unconditional`
and the passage from a presentation to compactness is
`AlgebraicGeometry.isFinitelyPresentable_of_hasFiniteQCSRepresentableCoequalizerPresentation`,
whose cofinality input on the representing objects is
`AlgebraicGeometry.SmallEtale.hasFiniteQuasiCompactCoverings`.

## Main results

* `AlgebraicGeometry.IsConstructibleSetSheaf.isFinitelyPresentable` — **the sheaves-of-sets case
  of Stacks 09Z4**: a constructible sheaf of sets on the small étale site of a quasi-compact and
  quasi-separated scheme is a compact object.

## Implementation notes

Compactness is `CategoryTheory.IsFinitelyPresentable`, which says that the covariant Hom functor
preserves filtered colimits; that is exactly the assertion that the canonical map
`colim Mor(F, G_i) → Mor(F, colim G_i)` is a bijection.

## References

* [Stacks Project, Tag 09Z4](https://stacks.math.columbia.edu/tag/09Z4)
* [Stacks Project, Tag 09Y9](https://stacks.math.columbia.edu/tag/09Y9)
* [Stacks Project, Tag 0738](https://stacks.math.columbia.edu/tag/0738)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Let `X` be a quasi-compact and quasi-separated scheme and let `F` be a constructible sheaf of
sets on `X_étale`. Then morphisms out of `F` commute with filtered colimits of sheaves of sets:
`Mor(F, colim G_i) = colim Mor(F, G_i)`. -/
@[stacks 09Z4 "sheaves of sets"]
public theorem IsConstructibleSetSheaf.isFinitelyPresentable
    (B : BigEtaleSite.{u}) (X : B.Scheme) [CompactSpace X.1] [QuasiSeparatedSpace X.1]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B X F) :
    IsFinitelyPresentable.{u + 1} F :=
  isFinitelyPresentable_of_hasFiniteQCSRepresentableCoequalizerPresentation B X
    (fun W hc hqs ↦ SmallEtale.hasFiniteQuasiCompactCoverings B X W hc hqs)
    ((isConstructibleSetSheaf_iff_hasFiniteQCSRepresentableCoequalizerPresentation_unconditional
      B X F).1 hF)

end AlgebraicGeometry

end
