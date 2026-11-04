module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctorAlgebraicFromExistence
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatIsomPresheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.FlatAlgebraizationExists

/-!
# The diagonal of the stack of algebraic spaces, without hypotheses (the argument of Stacks 0D1F)

Stacks 0D1F says that the diagonal of the stack `Spaces'_{fp, flat, proper}` of Stacks 0D1D is
representable by algebraic spaces. The library has the source's argument as
`AlgebraicGeometry.Space.hasRepresentableDiagonal_properFlatSpacesStack_of_hilb`, which takes as
its one hypothesis `AlgebraicGeometry.Space.HasHilbertModels`: Stacks 0D01, the algebraicity of
the Hilbert functor of a finitely presented separated morphism, over every algebraic space base.

This file discharges that hypothesis. Stacks 0D01 is the source's deduction from Stacks 0D00 and
Stacks 09TU, and Stacks 09TU is proved from the algebraicity of the stack of coherent sheaves,
Stacks 09DS, whose openness of versality comes from Stacks 0CXU fed with Grothendieck's existence
theorem for algebraic spaces, Stacks 0CXB.
`AlgebraicGeometry.Space.exists_hilbertPresheafModel_isAlgebraicSpace_of_existence` is that
whole chain with the conclusion of Stacks 0CXB as its only hypothesis, and
`AlgebraicGeometry.Space.InverseSystemExistenceSituation.exists_flat_algebraization` is that
conclusion, proved.

## Main results

* `AlgebraicGeometry.Space.hasHilbertModels`: Stacks 0D01 over every algebraic space base, in the
  packaged form `AlgebraicGeometry.Space.HasHilbertModels`. No hypotheses.
* `AlgebraicGeometry.Space.properFlatSpacesStack_hasRepresentableDiagonal`: the diagonal of
  `Spaces'_{fp, flat, proper}` is representable by algebraic spaces. No hypotheses.

## References

* [Stacks Project, Tag 0D1F](https://stacks.math.columbia.edu/tag/0D1F)
* [Stacks Project, Tag 0D01](https://stacks.math.columbia.edu/tag/0D01)
* [Stacks Project, Tag 09TU](https://stacks.math.columbia.edu/tag/09TU)
* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
* [Stacks Project, Tag 0CXB](https://stacks.math.columbia.edu/tag/0CXB)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0D01 over every base.** For every algebraic space `Q` over `S` and every morphism
`W ⟶ Q` of algebraic spaces which is of finite presentation and separated, the Hilbert functor
of `W` over `Q` has a model in the universe of the site which is an algebraic space and whose
canonical morphism to `Q` is locally of finite presentation. -/
theorem hasHilbertModels : HasHilbertModels B S hS := fun _ _ _ f hfp hsep =>
  exists_hilbertPresheafModel_isAlgebraicSpace_of_existence f hfp hsep fun s =>
    s.exists_flat_algebraization

/-- **The diagonal of `Spaces'_{fp, flat, proper}` is representable by algebraic spaces.** The
diagonal

```text
  Spaces'_{fp, flat, proper} ⟶ Spaces'_{fp, flat, proper} × Spaces'_{fp, flat, proper}
```

of the stack of Stacks 0D1D over the big fppf site of `S` is representable by algebraic spaces. -/
@[stacks 0D1F "the diagonal is representable by algebraic spaces; Stacks 0D01 is proved, \
`AlgebraicGeometry.Space.hasHilbertModels`"]
theorem properFlatSpacesStack_hasRepresentableDiagonal :
    Stack.HasRepresentableDiagonal B S hS (properFlatSpacesStack B S hS) :=
  hasRepresentableDiagonal_properFlatSpacesStack_of_hilb B S hS (hasHilbertModels B S hS)

end AlgebraicGeometry.Space

end
