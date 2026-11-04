module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQuasicoherentEquivalence

/-!
# Stacks 04CL: the right adjoint `i^!` of direct image along a closed immersion of spaces

Let `S` be a scheme contained in a big fppf site `B` and let `i : Z ⟶ X` be a closed immersion
of algebraic spaces over `S`.  [Stacks, Tag 04CL] says that the direct image

`i_* : QCoh(𝒪_Z) ⥤ QCoh(𝒪_X)`

has a right adjoint, the functor the source writes `i^!`.  This file states and proves that for
a closed immersion with no further hypothesis, and names the functor and the adjunction.

## Main definitions

* `AlgebraicGeometry.Space.quasicoherentRightAdjointOfClosedImmersion`: **Stacks 04CL**, the
  functor `i^!`.

## Main results

* `AlgebraicGeometry.Space.isLeftAdjoint_quasicoherentDirectImage`: **Stacks 04CL**, the direct
  image of quasi-coherent modules along a closed immersion of algebraic spaces has a right
  adjoint.
* `AlgebraicGeometry.Space.quasicoherentDirectImageAdjunction`: **Stacks 04CL**, the adjunction
  `i_* ⊣ i^!`.

## Implementation notes

The direct image here is `AlgebraicGeometry.Space.quasicoherentDirectImageOfClosedImmersion`, the
functor of Stacks 04CJ, part (3).

## References

* [Stacks Project, Lemma 67.14.3 (Tag 04CL)](https://stacks.math.columbia.edu/tag/04CL)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 04CK](https://stacks.math.columbia.edu/tag/04CK)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS}

/-- **Stacks 04CL.**  Let `S` be a scheme and let `i : Z ⟶ X` be a closed immersion of algebraic
spaces over `S`.  Then the direct image `i_* : QCoh(𝒪_Z) ⥤ QCoh(𝒪_X)` has a right adjoint, the
functor `i^!` of the source. -/
@[stacks 04CL]
theorem isLeftAdjoint_quasicoherentDirectImage (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    (quasicoherentDirectImageOfClosedImmersion B S hS i hi).IsLeftAdjoint :=
  isLeftAdjoint_quasicoherentPushforward B S hS i hi
    (quasicoherentDirectImageEquivalence B S hS i hi)

/-- **Stacks 04CL**, the functor `i^!`: the right adjoint of the direct image
`i_* : QCoh(𝒪_Z) ⥤ QCoh(𝒪_X)` along a closed immersion `i : Z ⟶ X` of algebraic spaces. For a
quasi-coherent `𝒪_X`-module `𝓖`, the direct image of `i^! 𝓖` is the largest quasi-coherent
submodule of `𝓖` annihilated by the ideal cutting out `Z`. -/
@[stacks 04CL "the functor `i^!`"]
def quasicoherentRightAdjointOfClosedImmersion (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    QuasicoherentSheaves.{u, u} B S hS X.1 X.2 ⥤ QuasicoherentSheaves.{u, u} B S hS Z.1 Z.2 :=
  quasicoherentRightAdjoint B S hS i hi (quasicoherentDirectImageEquivalence B S hS i hi)

/-- **Stacks 04CL**, the adjunction `i_* ⊣ i^!` exhibiting
`AlgebraicGeometry.Space.quasicoherentRightAdjointOfClosedImmersion` as a right adjoint of the
direct image of quasi-coherent modules along a closed immersion of algebraic spaces. -/
@[stacks 04CL "the adjunction `i_* ⊣ i^!`"]
def quasicoherentDirectImageAdjunction (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) :
    quasicoherentDirectImageOfClosedImmersion B S hS i hi ⊣
      quasicoherentRightAdjointOfClosedImmersion B S hS i hi :=
  quasicoherentPushforwardAdjunction B S hS i hi (quasicoherentDirectImageEquivalence B S hS i hi)

end AlgebraicGeometry.Space

end
