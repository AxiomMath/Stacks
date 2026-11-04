module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.DualizingHomothetyIso

/-!
# `R𝓗om_{𝒪_X}(ω, ω) ≅ 𝒪_X[0]` for a dualizing complex on a scheme

Let `X` be a locally Noetherian scheme and let `ω` be a dualizing complex on `X` in the sense of
[Stacks, Tag 0A87] — an object of `D(𝒪_X)` which over every affine open `U ⊆ X` is the complex
associated to a dualizing complex over `Γ(X, U)`. That the homothety of [Stacks, Tag 08DI]

`𝒪_X[0] ⟶ R𝓗om_{𝒪_X}(ω, ω)`

is an isomorphism is `Stacks.Duality.isIso_derivedSheafHomothety_of_isDualizingComplex` of
`Duality/DerivedTilde/DualizingHomothetyIso.lean`, proved there by checking invertibility on the
affine opens, where the derived endomorphisms of `ω|_U` on the slice site are the tensor unit
(`Stacks.Duality.restrictDDerivedSheafHomSelfUnitIso`).

This file records the resulting isomorphism of *objects*, which is that map inverted. Nothing
here is new mathematics: it is `asIso` of a morphism already known to be invertible, kept
separate only because the consumers of the self-duality half of being dualizing want an
isomorphism of objects rather than an `IsIso` instance.

## Main definitions

* `Stacks.Duality.derivedSheafHomSelfUnitIso` — the inverse of the homothety, i.e. the
  isomorphism `R𝓗om_{𝒪_X}(ω, ω) ≅ 𝒪_X[0]` in `D(𝒪_X)`.

## References

* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite
open Stacks.SheafOfModules

/-! Everything below is at `CategoryTheory.HasDerivedCategory.standard`, which is the model the
homothety and the derived internal hom of [Stacks, Tag 08DI] exist at, and the model
`Stacks.Duality.isIso_derivedSheafHomothety_of_isDualizingComplex` is stated at. So the choice is
forced by the input and no model comparison enters anywhere.

The locally small instances of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` are
*global*, so they outrank a file-level local instance; they are erased here rather than
outweighed, which keeps a single model in force for the whole file and makes the choice visible.
Nothing in this file needs direct sums or Brown representability, the two things those instances
exist for. -/

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Duality

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- **`R𝓗om_{𝒪_X}(ω, ω) ≅ 𝒪_X[0]` for a dualizing complex `ω` on a locally Noetherian scheme.**
The object form of `Stacks.Duality.isIso_derivedSheafHomothety_of_isDualizingComplex`: the
inverse of the homothety is the isomorphism, so this is compatible with the evaluation morphism —
unlike the affine object isomorphism `Stacks.Duality.derivedTildeDerivedSheafHomSelfUnitIso`,
which is built from the comparison of [Stacks, Tag 0A6H] (3)(a) and is not. -/
def derivedSheafHomSelfUnitIso (ω : DerivedCategory X.Modules) (hω : IsDualizingComplex ω) :
    letI := derivedMonoidalStructure X.sheaf
    ((derivedSheafHom X.sheaf).obj (op ω)).obj ω ≅
      𝟙_ (DerivedCategory (StructureSheafModules X.sheaf)) :=
  letI := derivedMonoidalStructure X.sheaf
  haveI := isIso_derivedSheafHomothety_of_isDualizingComplex ω hω
  (asIso (derivedSheafHomothety X.sheaf ω)).symm

end Stacks.Duality

end
