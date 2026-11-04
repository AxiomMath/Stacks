module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleGradedAlgebraPullbackComp

/-!
# The source of the canonical map of conormal algebras, as an inverse image of a conormal algebra

Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```
be a commutative square of algebraic spaces over a scheme `S` contained in a big fppf site `B`.
The canonical map of [Stacks Project, Tag 09RS] factors as

`f^*𝒞_{Z'/X',*}  ⟶  𝒞_{Z/X',*}  ⟶  𝒞_{Z/X,*}`,

and `AlgebraicGeometry.Space.conormalAlgebraCompMap` carries the first factor — but with its
source spelled as the inverse image along the composite `i ≫ g = f ≫ i'` of the graded algebra
of the powers of `𝓘' = Ker((i')^♯)`, not as `f^*𝒞_{Z'/X',*}`.  The `What is not proved` section
of `StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraFunctorial.lean` records the reason: the
source of Stacks 09RS is `f^*(i')^*(⨁ (𝓘')ⁿ)`, an inverse image along `f` of an inverse image
along `i'`, and rewriting that as an inverse image along the composite asks for the Stacks 03LU
composition comparison to be an isomorphism of sheaves of **graded algebras**.

That comparison is now available, as
`AlgebraicGeometry.Space.gradedAlgebraPullbackCompIso`, so this file states the first factor of
Stacks 09RS with its source as Stacks 09RS spells it:

`f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X',*}`.

## Main definitions

* `AlgebraicGeometry.Space.conormalAlgebraPullbackCompMap`: **the first factor of the canonical
  map of [Stacks Project, Tag 09RS], with its source identified with `f^*𝒞_{Z'/X',*}`.**  For
  `f : Z ⟶ Z'` and `i' : Z' ⟶ X'` it is a homomorphism of sheaves of graded `𝒪_Z`-algebras
  `f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X',*}`, the target being the conormal algebra of the composite
  `f ≫ i' : Z ⟶ X'`.

## Main results

* `AlgebraicGeometry.Space.conormalAlgebraPullbackCompMap_eq`: the map is the inverse of the
  composition comparison followed by
  `AlgebraicGeometry.Space.conormalAlgebraCompMap`, which is what fixes it.

## Implementation notes

**Why no commutative square appears in the statement.**  For a commutative square as above the
composite `Z ⟶ X'` is `i ≫ g = f ≫ i'`, and the only data the first factor uses is `f` and
`i'`: `AlgebraicGeometry.Space.conormalAlgebraCompMap` is built from the containment of kernel
ideal sheaves `AlgebraicGeometry.Space.kernelIdealSheaf_le_comp`, which for the square
`f ≫ i' = f ≫ i'` — the square of `f` and `i'` with `i := f` and `g := i'`, whose commutativity
is a reflexivity — is the containment `𝓘' ⊆ Ker((f ≫ i')^♯)`.  So the statement below needs no
square hypothesis, and specialises to a given square by rewriting `f ≫ i'` to `i ≫ g`.  This is
also what keeps the kernel out of trouble: transporting a homomorphism of sheaves of graded
algebras along an equality of morphisms of algebraic spaces would put an `eqToHom` between two
conormal algebras into the term, and the cost of reducing one at these types is recorded in the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackComp.lean`.

**What is still missing for Stacks 09RS itself.**  The second factor, which replaces the ambient
space `X'` by `X`, is carried degreewise by
`AlgebraicGeometry.Space.conormalAlgebraAmbientPieceMap` and is not known to be multiplicative:
the `What is not proved` section of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraAmbient.lean` lists its two missing inputs,
of which the multiplicativity of the composition comparison is now
`AlgebraicGeometry.Space.gradedAlgebraPullbackCompIso` while the other — the value of
`AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap` on a generator section of the pullback
of graded algebras — is still absent.  So no `@[stacks 09RS]` attribute is claimed here either:
Stacks 09RS asserts a homomorphism `f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*}` of sheaves of graded
`𝒪_Z`-algebras, and only its first factor is below.

## References

* [Stacks Project, Tag 09RS](https://stacks.math.columbia.edu/tag/09RS)
* [Stacks Project, Tag 09RN](https://stacks.math.columbia.edu/tag/09RN)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z Z' X' : AlgebraicSpaces B S hS}

/-- **The first factor of the canonical map of [Stacks Project, Tag 09RS], with its source
identified with `f^*𝒞_{Z'/X',*}`.**  For `f : Z ⟶ Z'` and `i' : Z' ⟶ X'`, the inverse image
along `f` of the conormal algebra of `i'` maps canonically to the conormal algebra of the
composite `f ≫ i'`:

`f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X',*}`.

It is the inverse of the Stacks 03LU composition comparison of sheaves of graded algebras,
`AlgebraicGeometry.Space.gradedAlgebraPullbackCompIso`, which rewrites `f^*(i')^*(⨁ (𝓘')ⁿ)` as
`(f ≫ i')^*(⨁ (𝓘')ⁿ)`, followed by
`AlgebraicGeometry.Space.conormalAlgebraCompMap` for the commutative square
`f ≫ i' = f ≫ i'`.

For a commutative square `i ≫ g = f ≫ i'` the composite `f ≫ i'` is `i ≫ g`, so this is the
first factor of the canonical map of Stacks 09RS with the source spelled as the source
describes it; the module documentation records why no square hypothesis is needed. -/
noncomputable def conormalAlgebraPullbackCompMap (f : Z ⟶ Z') (i' : Z' ⟶ X') :
    (gradedPull (X := smallEtaleRingedTopos B S hS Z) (Y := smallEtaleRingedTopos B S hS Z')
        (smallEtaleRingedToposHom B S hS f)).obj (conormalAlgebra B S hS i') ⟶
      conormalAlgebra B S hS (f ≫ i') :=
  ((gradedAlgebraPullbackCompIso B S hS f i').app
      (kernelIdealGradedAlgebra B S hS i')).inv ≫
    conormalAlgebraCompMap B S hS f i' f i' rfl

/-- The first factor of Stacks 09RS is the inverse of the Stacks 03LU composition comparison of
sheaves of graded algebras followed by `AlgebraicGeometry.Space.conormalAlgebraCompMap`. -/
theorem conormalAlgebraPullbackCompMap_eq (f : Z ⟶ Z') (i' : Z' ⟶ X') :
    conormalAlgebraPullbackCompMap B S hS f i' =
      ((gradedAlgebraPullbackCompIso B S hS f i').app
          (kernelIdealGradedAlgebra B S hS i')).inv ≫
        conormalAlgebraCompMap B S hS f i' f i' rfl :=
  rfl

end AlgebraicGeometry.Space

end
