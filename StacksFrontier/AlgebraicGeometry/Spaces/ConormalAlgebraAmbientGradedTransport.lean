module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraAmbientUnitSection
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraPullbackComp

/-!
# The ambient factor of the canonical map of conormal algebras, as a graded algebra map

Let
```
Z --i--→ X
         |
         g
         ↓
         X'
```
be a morphism `i : Z ⟶ X` of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, followed by a morphism `g : X ⟶ X'`.  Write `𝓘 = Ker(i^♯) ⊆ 𝒪_X` and
`𝓙 = Ker((i ≫ g)^♯) ⊆ 𝒪_{X'}`.  The ambient factor of the canonical map of
[Stacks Project, Tag 09RS] is the second of the two factors

`f^*𝒞_{Z'/X',*}  ⟶  𝒞_{Z/X',*}  ⟶  𝒞_{Z/X,*}`,

and `StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraAmbient.lean` carries it degreewise, as
the family `AlgebraicGeometry.Space.conormalAlgebraAmbientPieceMap` of morphisms of sheaves of
modules obtained from `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap : g^*(𝓙ⁿ) ⟶ 𝓘ⁿ`.

This file observes that the passage from `X` down to `Z` costs nothing once the map upstairs is
multiplicative: a homomorphism of sheaves of graded `𝒪_X`-algebras `g^*(⨁ 𝓙ⁿ) ⟶ ⨁ 𝓘ⁿ` gives the
ambient factor as a homomorphism of sheaves of graded `𝒪_Z`-algebras

`𝒞_{Z/X',*} = (i ≫ g)^*(⨁ 𝓙ⁿ) ⟶ i^*(⨁ 𝓘ⁿ) = 𝒞_{Z/X,*}`,

because the pullback of sheaves of graded algebras along `i` is a functor and the Stacks 03LU
composition comparison is available multiplicatively, as
`AlgebraicGeometry.Space.gradedAlgebraPullbackCompIso`.  So the ambient factor of Stacks 09RS
needs exactly one input which is not yet available: that one homomorphism on `X`.

## Main definitions

* `AlgebraicGeometry.Space.gradedPullCompMap`: the inverse image along `i` of a homomorphism of
  sheaves of graded algebras out of an inverse image along `g`, with its source rewritten as an
  inverse image along the composite `i ≫ g`.
* `AlgebraicGeometry.Space.conormalAlgebraAmbientMapOfPullbackHom`: **the ambient factor of
  [Stacks Project, Tag 09RS] as a homomorphism of sheaves of graded `𝒪_Z`-algebras, given a
  homomorphism of sheaves of graded `𝒪_X`-algebras `g^*(⨁ 𝓙ⁿ) ⟶ ⨁ 𝓘ⁿ`.**

## Main results

* `AlgebraicGeometry.Space.gradedPullCompMap_app` and
  `AlgebraicGeometry.Space.conormalAlgebraAmbientMapOfPullbackHom_app`: the degreewise components
  are the composition comparison followed by the inverse image along `i` of the given
  homomorphism in that degree.

## Implementation notes

**Why the hypothesis is a homomorphism on `X` and not on `Z`.**  The multiplicativity criterion
`Stacks.Sheaves.GradedAlgebraPullback.homOfMulUnitGeneratorSectionOfLocal` tests a degreewise
family out of a pullback of sheaves of graded algebras on the generator sections of the pure
tensors `1 ⊗ x`, and the equation it asks for lives in the target.  Applying it to the degreewise
family `AlgebraicGeometry.Space.conormalAlgebraAmbientPieceMap` on `Z` puts the equation in
`i^*(𝓘^{n})`, a pullback, where nothing but a generator section can be evaluated, and the family
itself is a composite of the Stacks 03LU comparison with an inverse image along `i`; applying it
upstairs on `X` instead puts the equation in `𝓘^{n}`, a sheaf of ideals, where the
multiplication is multiplication of sections of `𝒪_X` and the family is
`AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap` itself.  That is why the hypothesis is
taken on `X`: the descent to `Z` is the functoriality below, which needs no further input.

**No degreewise comparison with the existing family.**  That the components of
`AlgebraicGeometry.Space.conormalAlgebraAmbientMapOfPullbackHom` agree with
`AlgebraicGeometry.Space.conormalAlgebraAmbientPieceMap` when the given homomorphism has
`AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap` for its components is *not* proved: it
asks for the components of the multiplicative composition comparison
`AlgebraicGeometry.Space.gradedAlgebraPullbackCompIso` to be identified with the components of
the comparison of sheaves of modules `AlgebraicGeometry.Space.modulePullbackCompIso`, and no
such identification is available.  The two constructions are the two factorisations of the same
map; which one carries the Stacks 09RS statement is settled by whichever gets a multiplicative
degreewise family first.

**Why the statement is for arbitrary morphisms and not for immersions.**  As in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraAmbient.lean`, nothing below uses any
property of `i` or `g`; it specialises to the immersions of Stacks 09RS.

## What is not proved

* **No homomorphism `g^*(⨁ 𝓙ⁿ) ⟶ ⨁ 𝓘ⁿ` of sheaves of graded algebras is constructed**, so the
  ambient factor of Stacks 09RS is still not available unconditionally.  The degreewise family is
  `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap`, its multiplicativity on the unit
  sections of a chart diagram is
  `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap_mul_modulePullbackUnitSection`, and
  what the criterion
  `Stacks.Sheaves.GradedAlgebraPullback.homOfMulUnitGeneratorSectionOfLocal` needs in addition is
  the identification of the generator section of a pure tensor `1 ⊗ x` with such a unit section,
  locally in `x`.  The `What is not proved` section of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraAmbientUnitSection.lean` records what that
  identification is now waiting for.
* **No `@[stacks 09RS]` attribute.**  Stacks 09RS asserts a homomorphism
  `f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*}` of sheaves of graded `𝒪_Z`-algebras for a commutative square whose
  two vertical arrows are immersions; the ambient factor alone is not that statement, and the
  factor below is conditional on its hypothesis.

## References

* [Stacks Project, Tag 09RS](https://stacks.math.columbia.edu/tag/09RS)
* [Stacks Project, Tag 09RN](https://stacks.math.columbia.edu/tag/09RN)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {Z X X' : AlgebraicSpaces B S hS}

/-! ### Pulling a homomorphism out of an inverse image back along a further morphism -/

/-- **The inverse image along `i` of a homomorphism of sheaves of graded algebras out of an
inverse image along `g`, with its source rewritten as an inverse image along the composite.**
For `Ψ : g^*B' ⟶ A` of sheaves of graded `𝒪_X`-algebras this is a homomorphism
`(i ≫ g)^*B' ⟶ i^*A` of sheaves of graded `𝒪_Z`-algebras.

It is the multiplicative form `AlgebraicGeometry.Space.gradedAlgebraPullbackCompIso` of the
Stacks 03LU composition comparison, which rewrites `(i ≫ g)^*B'` as `i^*(g^*B')`, followed by the
inverse image along `i` of `Ψ`.  Both factors are morphisms of sheaves of graded algebras, so no
multiplicativity is left to check. -/
noncomputable def gradedPullCompMap (i : Z ⟶ X) (g : X ⟶ X')
    (B' : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X'))
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (Ψ : (gradedPull (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS g)).obj B' ⟶ A) :
    (gradedPull (X := smallEtaleRingedTopos B S hS Z)
        (Y := smallEtaleRingedTopos B S hS X')
        (smallEtaleRingedToposHom B S hS (i ≫ g))).obj B' ⟶
      (gradedPull (X := smallEtaleRingedTopos B S hS Z)
        (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS i)).obj A :=
  ((gradedAlgebraPullbackCompIso B S hS i g).app B').hom ≫
    (gradedPull (X := smallEtaleRingedTopos B S hS Z)
      (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS i)).map Ψ

/-- The degree-`n` component of `AlgebraicGeometry.Space.gradedPullCompMap` is the degree-`n`
component of the composition comparison followed by the inverse image along `i` of the degree-`n`
component of the given homomorphism. -/
theorem gradedPullCompMap_app (i : Z ⟶ X) (g : X ⟶ X')
    (B' : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X'))
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (Ψ : (gradedPull (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS g)).obj B' ⟶ A)
    (n : ℤ) :
    (gradedPullCompMap B S hS i g B' A Ψ).app n =
      ((gradedAlgebraPullbackCompIso B S hS i g).app B').hom.app n ≫
        (modulePullback B S hS i).map (Ψ.app n) :=
  rfl

/-! ### The ambient factor of Stacks 09RS from a homomorphism on the ambient space -/

/-- **The ambient factor of [Stacks Project, Tag 09RS], as a homomorphism of sheaves of graded
`𝒪_Z`-algebras, given one on the ambient space.**  A homomorphism
`Ψ : g^*(⨁_{n ≥ 0} 𝓙ⁿ) ⟶ ⨁_{n ≥ 0} 𝓘ⁿ` of sheaves of graded `𝒪_X`-algebras gives

`𝒞_{Z/X',*} ⟶ 𝒞_{Z/X,*}`,

the factor of the canonical map of Stacks 09RS which replaces the ambient space `X'` by `X`.

This is `AlgebraicGeometry.Space.gradedPullCompMap` at the graded algebras of the powers of the
two kernel ideal sheaves: the conormal algebra of `i ≫ g` is the inverse image along `i ≫ g` of
the graded algebra of the powers of `𝓙`, and the conormal algebra of `i` is the inverse image
along `i` of the graded algebra of the powers of `𝓘`.

The module documentation records that no such `Ψ` is constructed, and that its degreewise family
is `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap`. -/
noncomputable def conormalAlgebraAmbientMapOfPullbackHom (i : Z ⟶ X) (g : X ⟶ X')
    (Ψ : (gradedPull (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS g)).obj
        (kernelIdealGradedAlgebra B S hS (i ≫ g)) ⟶ kernelIdealGradedAlgebra B S hS i) :
    conormalAlgebra B S hS (i ≫ g) ⟶ conormalAlgebra B S hS i :=
  gradedPullCompMap B S hS i g (kernelIdealGradedAlgebra B S hS (i ≫ g))
    (kernelIdealGradedAlgebra B S hS i) Ψ

/-- The degree-`n` component of the ambient factor built from a homomorphism on the ambient
space: the composition comparison followed by the inverse image along `i` of the degree-`n`
component.  Compare `AlgebraicGeometry.Space.conormalAlgebraAmbientPieceMap_eq`, which is the
same shape for the degreewise family, with the comparison of sheaves of modules in place of the
multiplicative one; the module documentation records that the two are not identified. -/
theorem conormalAlgebraAmbientMapOfPullbackHom_app (i : Z ⟶ X) (g : X ⟶ X')
    (Ψ : (gradedPull (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS g)).obj
        (kernelIdealGradedAlgebra B S hS (i ≫ g)) ⟶ kernelIdealGradedAlgebra B S hS i)
    (n : ℤ) :
    (conormalAlgebraAmbientMapOfPullbackHom B S hS i g Ψ).app n =
      ((gradedAlgebraPullbackCompIso B S hS i g).app
            (kernelIdealGradedAlgebra B S hS (i ≫ g))).hom.app n ≫
        (modulePullback B S hS i).map (Ψ.app n) :=
  gradedPullCompMap_app B S hS i g (kernelIdealGradedAlgebra B S hS (i ≫ g))
    (kernelIdealGradedAlgebra B S hS i) Ψ n

end AlgebraicGeometry.Space

end
