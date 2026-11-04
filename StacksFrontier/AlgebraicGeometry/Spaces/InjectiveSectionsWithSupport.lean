module

public import StacksFrontier.AlgebraicGeometry.Spaces.ComplexesWithSupport

/-!
# Sections with support in a closed subspace of an injective abelian sheaf

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S` and let `I` be an
injective abelian sheaf on the small étale site of `X`. Then the sheaf `H_Z(I)` of sections
with support in `|Z|`, viewed on the small étale site of `Z`, is an injective abelian sheaf
there.

## Main results

* `AlgebraicGeometry.Space.injective_sectionsWithSupportInClosedSubspace_of_isClosedImmersion`
  is **Stacks 0A4M**.
* `…preservesInjectiveObjects_sectionsWithSupportInClosedSubspace_of_isClosedImmersion` is the
  same assertion in functorial form.

## Implementation notes

Both statements are the conditional ones of
`StacksFrontier/AlgebraicGeometry/Spaces/SectionsWithSupportInjective.lean` with their hypothesis
discharged: the adjunction `i_* ⊣ H_Z` is
`AlgebraicGeometry.Space.pushforwardSectionsWithSupportAdjunctionOfIsClosedImmersion`, whose
one ingredient beyond that file — the essential-image clause of Stacks 04E5, part (2) — is
proved in `StacksFrontier/AlgebraicGeometry/Spaces/ComplexesWithSupport.lean`. They are separated
from the conditional forms only because that file consumes them.

The proof is the source's. A morphism `i_*G ⟶ I` has image in the sections with support in
`|Z|`, because every section of `i_*G` has support there, and the direct image is fully
faithful, so `Hom_Z(G, H_Z(I)) = Hom_X(i_*G, I)`; the direct image is moreover exact, so
Stacks 015Z turns that adjunction into preservation of injective objects. The exactness used is
not that of Stacks 0A4K, which this development proves only under a surjectivity hypothesis: it
is right-adjointness of the direct image in the adjunction with the inverse image together with
its left-adjointness in the adjunction with `H_Z`.

## References

* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 0A4L](https://stacks.math.columbia.edu/tag/0A4L)
* [Stacks Project, Tag 0A4M](https://stacks.math.columbia.edu/tag/0A4M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS} (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)

/-- **Stacks 0A4M.** Let `S` be a scheme, let `i : Z ⟶ X` be a closed immersion of algebraic
spaces over `S` and let `I` be an injective abelian sheaf on the small étale site of `X`. Then
the sections of `I` with support in `|Z|` form an injective abelian sheaf on the small étale
site of `Z`. -/
@[stacks 0A4M]
theorem injective_sectionsWithSupportInClosedSubspace_of_isClosedImmersion
    (I : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}) [Injective I] :
    Injective ((sectionsWithSupportInClosedSubspace B S hS i hi).obj I) :=
  injective_sectionsWithSupportInClosedSubspace B S hS i hi
    (pushforwardSectionsWithSupportAdjunctionOfIsClosedImmersion B S hS i hi) I

/-- **Stacks 0A4M** in functorial form: the sections with support in `|Z|` preserve injective
objects. -/
theorem preservesInjectiveObjects_sectionsWithSupportInClosedSubspace_of_isClosedImmersion :
    (sectionsWithSupportInClosedSubspace B S hS i hi).PreservesInjectiveObjects :=
  preservesInjectiveObjects_sectionsWithSupportInClosedSubspace B S hS i hi
    (pushforwardSectionsWithSupportAdjunctionOfIsClosedImmersion B S hS i hi)

end AlgebraicGeometry.Space

end
