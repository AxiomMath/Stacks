module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceDifferentialsEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsImmersion
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness at the right term of the conormal sequence, for an immersion

Let `B` be an algebraic space over a scheme `S` and let `i : Z ⟶ X` be an immersion of algebraic
spaces over `B`, with structure morphism `b : X ⟶ B`.  Stacks 05ZA asserts that the sequence
```
  𝒞_{Z/X} ⟶ i^*Ω_{X/B} ⟶ Ω_{Z/B} ⟶ 0
```
is exact; exactness at the right term is the assertion that its second arrow is an epimorphism.

`AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_of_isLocallySurjective` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDifferentialsEpi.lean` proves that clause
from local surjectivity of `i♯ : i⁻¹𝒪_X ⟶ 𝒪_Z`, which it carries as the hypothesis `hsharp`.
**This file discharges that hypothesis for an immersion**, so that the clause holds with no
hypothesis beyond the one Stacks 05ZA makes.  The discharge is
`AlgebraicGeometry.Space.isLocallySurjective_structureSharpInverseImage_of_isImmersion`, proved
for Stacks 05Z9 in `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsImmersion.lean` from
Stacks 04E5, Stacks 03MB, the factorization of Stacks 04CE and the étale-base step of
Stacks 04CU; the two statements are the same hypothesis, so nothing is left to do but compose
them.

## Main results

* `AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_of_isImmersion`: **Stacks 05ZA**,
  exactness at the right term, carrying nothing beyond the immersion.

## Implementation notes

**Why this is a module of its own.**  Neither of the two files it joins imports the other, and
the hypothesis-carrying form is wanted in its own right: it is what
`AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_of_isLocallySurjective` is stated at,
because local surjectivity of `i♯` is the only property of an immersion that the source's proof
of this clause uses.

## References

* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA)
* [Stacks Project, Tag 05Z9](https://stacks.math.columbia.edu/tag/05Z9), whose proof supplies the
  local surjectivity discharged here.
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the surjectivity clause
  of which local surjectivity of `i♯` is the inverse-image form.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Bb : AlgebraicSpaces B S hS}

/-- **Stacks 05ZA, exactness at the right term, for an immersion.**  For an immersion
`i : X ⟶ Y` of algebraic spaces over `B` and a structure morphism `b : Y ⟶ B`, the second arrow
`i^*Ω_{Y/B} ⟶ Ω_{X/B}` of the conormal sequence — the comparison map of Stacks 04CX for the
square over the identity of `B` — is an epimorphism.

This is `AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_of_isLocallySurjective` with its
hypothesis `hsharp` discharged by
`AlgebraicGeometry.Space.isLocallySurjective_structureSharpInverseImage_of_isImmersion`. -/
@[stacks 05ZA "exactness at the right term: the second arrow `i^*Ω_{X/B} ⟶ Ω_{Z/B}` is an \
epimorphism for an immersion, with no hypothesis beyond the immersion"]
theorem epi_pullbackDifferentialsMap_of_isImmersion (i : X ⟶ Y) (b : Y ⟶ Bb)
    (hi : IsImmersion B S hS i.hom) :
    Epi (pullbackDifferentialsMap B S hS i b) :=
  epi_pullbackDifferentialsMap_of_isLocallySurjective B S hS i b
    (isLocallySurjective_structureSharpInverseImage_of_isImmersion B S hS i hi)

end AlgebraicGeometry.Space

end
