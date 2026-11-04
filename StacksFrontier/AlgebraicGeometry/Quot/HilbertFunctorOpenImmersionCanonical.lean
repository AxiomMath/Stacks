module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctorOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertPresheafCanonicalModel

/-!
# The open immersion of Hilbert functors, on the canonical models (Stacks 0DPE)

Let `A` be an algebraic space over a scheme `S` of a big fppf site and let `π : X ⟶ Y` be an open
immersion of algebraic spaces over `A`, with `Y` separated over `A`. Stacks 0DPE says that `π`
induces an open immersion `Hilb_{X/A} ⟶ Hilb_{Y/A}`.

The Hilbert presheaf `AlgebraicGeometry.Space.hilbertPresheaf` takes values one universe above
the site, and being an open immersion is a property of morphisms of presheaves in the universe of
the site, so the statement is about the morphism read in models of the two Hilbert functors. This
file states it for the canonical models `AlgebraicGeometry.Space.HilbertPresheafModel.canonical`,
which exist for every morphism of algebraic spaces, so that nothing beyond the source's
hypotheses is assumed.

## Main results

* `AlgebraicGeometry.Space.isOpenImmersion_hilbertModelMap_canonical`: **Stacks 0DPE**, the
  morphism of the canonical models of the Hilbert functors induced by `π` is an open immersion.

## Implementation notes

The source's hypotheses that `X` and `Y` are of finite presentation over `A`, and that `X` is
separated over `A`, are not imposed: they make the two Hilbert functors algebraic spaces
(Stacks 0D01), which the open immersion property does not need. Only separatedness of `Y` over `A`
enters, through the closedness in `Y_T` of the image of a family of `X_T`.

## References

* [Stacks Project, Tag 0DPE](https://stacks.math.columbia.edu/tag/0DPE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y A : AlgebraicSpaces B S hS} {π : X ⟶ Y} {bX : X ⟶ A} {bY : Y ⟶ A}

/-- **Stacks 0DPE.** Let `π : X ⟶ Y` be an open immersion of algebraic spaces over an algebraic
space `A`, with `Y` separated over `A`. Then `π` induces an open immersion
`Hilb_{X/A} ⟶ Hilb_{Y/A}` of Hilbert functors: the morphism
`AlgebraicGeometry.Space.hilbertPresheafMap`, sending a family `Z ⊆ X_T` to its image in `Y_T`,
read in the canonical models `AlgebraicGeometry.Space.HilbertPresheafModel.canonical` of the two
Hilbert functors, is an open immersion. Nothing is assumed about the models: they exist for every
morphism of algebraic spaces. -/
@[stacks 0DPE "the induced morphism of the canonical Hilbert functors is an open immersion"]
theorem isOpenImmersion_hilbertModelMap_canonical (hπ : π ≫ bY = bX)
    (hopen : IsOpenImmersion B S hS π.hom) (hsep : IsSeparated B S hS bY.hom) :
    IsOpenImmersion B S hS (hilbertModelMap hπ hopen hsep (HilbertPresheafModel.canonical bX)
      (HilbertPresheafModel.canonical bY)) :=
  isOpenImmersion_hilbertModelMap hπ hopen hsep _ _

end AlgebraicGeometry.Space

end
