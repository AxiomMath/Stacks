module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraAmbientGradedTransport

/-!
# The canonical map of conormal algebras of a commutative square

Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```
be a commutative square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
so `i ≫ g = f ≫ i'`.  Write `𝓘 = Ker(i^♯) ⊆ 𝒪_X`, `𝓘' = Ker((i')^♯) ⊆ 𝒪_{X'}` and
`𝓙 = Ker((f ≫ i')^♯) ⊆ 𝒪_{X'}` for the kernel ideal sheaf of the diagonal.
[Stacks Project, Tag 09RS] asserts a canonical homomorphism of sheaves of graded
`𝒪_Z`-algebras

`f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*}`,

and this file assembles it out of the two factors

`f^*𝒞_{Z'/X',*}  ⟶  𝒞_{Z/X',*}  ⟶  𝒞_{Z/X,*}`

already available: the first is `AlgebraicGeometry.Space.conormalAlgebraPullbackCompMap`, which
is unconditional, and the second is the ambient factor of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraAmbientGradedTransport.lean`, which is
conditional on a homomorphism of sheaves of graded `𝒪_X`-algebras `g^*(⨁ 𝓙ⁿ) ⟶ ⨁ 𝓘ⁿ` on the
ambient space.  So the composite below carries that homomorphism as an explicit hypothesis, and
the `@[stacks 09RS]` attribute says so.

## The two spellings of the diagonal, and why no `eqToHom` appears

The obstacle to composing the two factors is that they are spelled over the two diagonals of the
square.  The first factor's target is the conormal algebra of `f ≫ i'`, because
`AlgebraicGeometry.Space.conormalAlgebraPullbackCompMap` is built from `f` and `i'` alone; the
ambient factor of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraAmbientGradedTransport.lean` has for its
source the conormal algebra of `i ≫ g`, because
`AlgebraicGeometry.Space.gradedPullCompMap` is built from `i` and `g` alone.  For the square
these are the same morphism, but not the same term, and transporting a homomorphism of sheaves
of graded algebras along the equality would put an `eqToHom` between two conormal algebras into
the statement — the shape whose cost at these types is recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackComp.lean`.

No such transport is needed.  The multiplicative composition comparison
`Stacks.Sheaves.GradedAlgebraEssentiallySmall.gradedPullbackCompIso` takes an **arbitrary**
morphism of ringed topoi in the role of the composite, together with a comparison `τ` of the
direct images; so the ambient factor can be re-derived with the role of the composite played by
the *other* diagonal `f ≫ i'`, and then its source is the conormal algebra of `f ≫ i'` on the
nose.  The square enters only in building `τ`, that is, on the direct-image side, where the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleGradedAlgebraPullbackComp.lean` record that the
direct image "enters here only as the right adjoint used to compare the two left adjoints, never
in a statement".  Every statement below is therefore free of casts between conormal algebras.

That the re-derivation is a genuine generalisation and not a second construction is
`AlgebraicGeometry.Space.gradedAlgebraPullbackCompIsoOfEq_rfl` and
`AlgebraicGeometry.Space.gradedPullCompMapOfEq_rfl`: for the diagonal spelled `i ≫ g` and the
reflexivity proof, the comparison and the map below are the existing ones.

## Main definitions

* `AlgebraicGeometry.Space.gradedAlgebraPushforwardCompIsoOfEq`: the comparison
  `i_* ∘ g_* ≅ j_*` of direct images of sheaves of graded algebras, for any `j` equal to the
  composite `i ≫ g`.
* `AlgebraicGeometry.Space.gradedAlgebraPullbackCompIsoOfEq`: the comparison
  `j^* ≅ g^* ∘ i^*` of pullbacks of sheaves of graded algebras, for any `j` equal to `i ≫ g`.
* `AlgebraicGeometry.Space.gradedPullCompMapOfEq`: the inverse image along `i` of a homomorphism
  of sheaves of graded algebras out of an inverse image along `g`, with its source an inverse
  image along any `j` equal to `i ≫ g`.
* `AlgebraicGeometry.Space.conormalAlgebraAmbientSquareMapOfPullbackHom`: the ambient factor of
  [Stacks Project, Tag 09RS] for a commutative square, with its source the conormal algebra of
  the diagonal spelled `f ≫ i'`.
* `AlgebraicGeometry.Space.conormalAlgebraSquareMapOfPullbackHom`: **the canonical map of
  [Stacks Project, Tag 09RS], given the ambient homomorphism `g^*(⨁ 𝓙ⁿ) ⟶ ⨁ 𝓘ⁿ`.**

## Main results

* `AlgebraicGeometry.Space.gradedAlgebraPullbackCompIsoOfEq_rfl` and
  `AlgebraicGeometry.Space.gradedPullCompMapOfEq_rfl`: at the diagonal `i ≫ g` and the
  reflexivity proof, the two constructions above are the existing unparametrised ones.
* `AlgebraicGeometry.Space.conormalAlgebraSquareMapOfPullbackHom_app`: the degreewise components
  are those of the first factor followed by those of the ambient factor.

## Implementation notes

**What the hypothesis is, and what it is not.**  The hypothesis is a homomorphism of sheaves of
graded `𝒪_X`-algebras upstairs on the ambient space `X`,

`Ψ : g^*(⨁_{n ≥ 0} 𝓙ⁿ) ⟶ ⨁_{n ≥ 0} 𝓘ⁿ`,

whose degreewise family is `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap` and whose
missing input is recorded in the `What is not proved` section of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraAmbientGradedTransport.lean`.  It is not the
conclusion: the conclusion is a homomorphism downstairs on `Z`, between the conormal algebras of
the two vertical arrows, and getting there from `Ψ` is the Stacks 03LU composition comparison
`AlgebraicGeometry.Space.gradedAlgebraPullbackCompIsoOfEq`, the inverse image along `i`, and the
unconditional first factor `AlgebraicGeometry.Space.conormalAlgebraPullbackCompMap`, which is
itself built from the containment of kernel ideal sheaves
`AlgebraicGeometry.Space.kernelIdealSheaf_le_comp`.

**No degreewise lemma specialised to the ambient factor.**  The degreewise description of the
ambient factor is `AlgebraicGeometry.Space.gradedPullCompMapOfEq_app`, which holds at an
arbitrary graded algebra in each variable and is proved by reflexivity there.  Restating it with
the two kernel-ideal graded algebras substituted in, and the diagonal spelled `f ≫ i'`, exhausts
the kernel's reduction budget — a deterministic timeout — even when the proof
is the general lemma instantiated rather than a fresh `rfl`, because it is the *statement* at the
concrete graded algebras that the kernel must then decide.  So no such specialisation is stated:
a consumer instantiates `AlgebraicGeometry.Space.gradedPullCompMapOfEq_app` itself.  The
degreewise description of the whole map,
`AlgebraicGeometry.Space.conormalAlgebraSquareMapOfPullbackHom_app`, is affordable because it
only splits a composite into its two factors' components and leaves those components abstract.

**Why `𝓙` is the kernel ideal sheaf of `f ≫ i'` and not of `i ≫ g`.**  These are the same ideal
sheaf, the square's two spellings of its diagonal; `f ≫ i'` is the spelling the first factor's
target uses, so taking `Ψ` at that spelling is what makes the composite typecheck without a
cast.  The source's `𝒞_{Z/X',*}` is the conormal algebra of the diagonal either way.

**Why the statement is for arbitrary morphisms and not for immersions.**  As in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraAmbient.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraAmbientGradedTransport.lean`, nothing below
uses any property of `i` or `i'`, so the statement is strictly more general than Stacks 09RS,
which takes both vertical arrows to be immersions; it specialises to them.  The conormal algebra
`AlgebraicGeometry.Space.conormalAlgebra` is defined for an arbitrary morphism by the same
formula, so the generalisation changes no instance of the statement.

## References

* [Stacks Project, Tag 09RS](https://stacks.math.columbia.edu/tag/09RS)
* [Stacks Project, Tag 09RN](https://stacks.math.columbia.edu/tag/09RN)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull gradedPush gradedPullbackCompIso)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {Z X X' Z' : AlgebraicSpaces B S hS}

/-! ### The composition comparisons at an arbitrary spelling of the composite -/

/-- **The comparison `i_* ∘ g_* ≅ j_*` of direct images of sheaves of graded algebras, for any
`j` equal to the composite `i ≫ g`.**  It is
`AlgebraicGeometry.Space.gradedAlgebraPushforwardCompIso` followed by the transport along the
equality of morphisms of ringed topoi induced by `hj`.

The cast lives on the direct-image side only, and the direct image enters the comparison of
pullbacks below purely as the right adjoint used to compare two left adjoints; the module
documentation records why that keeps every statement cast-free. -/
noncomputable def gradedAlgebraPushforwardCompIsoOfEq (i : Z ⟶ X) (g : X ⟶ X') (j : Z ⟶ X')
    (hj : j = i ≫ g) :
    gradedPush (X := smallEtaleRingedTopos B S hS Z) (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS i) ⋙
      gradedPush (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS X')
        (smallEtaleRingedToposHom B S hS g) ≅
      gradedPush (X := smallEtaleRingedTopos B S hS Z) (Y := smallEtaleRingedTopos B S hS X')
        (smallEtaleRingedToposHom B S hS j) :=
  gradedAlgebraPushforwardCompIso B S hS i g ≪≫ eqToIso (by subst hj; rfl)

/-- At the diagonal spelled `i ≫ g` and the reflexivity proof, the comparison of direct images
is `AlgebraicGeometry.Space.gradedAlgebraPushforwardCompIso`. -/
theorem gradedAlgebraPushforwardCompIsoOfEq_rfl (i : Z ⟶ X) (g : X ⟶ X') :
    gradedAlgebraPushforwardCompIsoOfEq B S hS i g (i ≫ g) rfl =
      gradedAlgebraPushforwardCompIso B S hS i g :=
  Iso.ext (by simp [gradedAlgebraPushforwardCompIsoOfEq])

/-- **The comparison `j^* ≅ g^* ∘ i^*` of pullbacks of sheaves of graded algebras, for any `j`
equal to the composite `i ≫ g`**: part (2) of [Stacks Project, Tag 0FQX] with the composite
played by an arbitrary morphism, and the multiplicative form of the Stacks 03LU comparison.

This is `Stacks.Sheaves.GradedAlgebraEssentiallySmall.gradedPullbackCompIso`, which takes the
morphism in the role of the composite as a parameter, fed the comparison of direct images
`AlgebraicGeometry.Space.gradedAlgebraPushforwardCompIsoOfEq`.  Being an isomorphism of sheaves
of **graded algebras**, each of its degreewise components preserves products of homogeneous
local sections. -/
noncomputable def gradedAlgebraPullbackCompIsoOfEq (i : Z ⟶ X) (g : X ⟶ X') (j : Z ⟶ X')
    (hj : j = i ≫ g) :
    gradedPull (X := smallEtaleRingedTopos B S hS Z) (Y := smallEtaleRingedTopos B S hS X')
        (smallEtaleRingedToposHom B S hS j) ≅
      gradedPull (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS X')
          (smallEtaleRingedToposHom B S hS g) ⋙
        gradedPull (X := smallEtaleRingedTopos B S hS Z)
          (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS i) :=
  gradedPullbackCompIso (smallEtaleRingedToposHom B S hS i)
    (smallEtaleRingedToposHom B S hS g) (smallEtaleRingedToposHom B S hS j)
    (gradedAlgebraPushforwardCompIsoOfEq B S hS i g j hj)

/-- At the diagonal spelled `i ≫ g` and the reflexivity proof, the comparison of pullbacks is
`AlgebraicGeometry.Space.gradedAlgebraPullbackCompIso`: the construction above is a
generalisation of the existing one, not a second one. -/
theorem gradedAlgebraPullbackCompIsoOfEq_rfl (i : Z ⟶ X) (g : X ⟶ X') :
    gradedAlgebraPullbackCompIsoOfEq B S hS i g (i ≫ g) rfl =
      gradedAlgebraPullbackCompIso B S hS i g := by
  rw [gradedAlgebraPullbackCompIsoOfEq, gradedAlgebraPullbackCompIso,
    gradedAlgebraPushforwardCompIsoOfEq_rfl]

/-! ### Pulling a homomorphism back along an arbitrary spelling of the composite -/

/-- **The inverse image along `i` of a homomorphism of sheaves of graded algebras out of an
inverse image along `g`, with its source an inverse image along any `j` equal to `i ≫ g`.**  For
`Ψ : g^*B' ⟶ A` of sheaves of graded `𝒪_X`-algebras this is a homomorphism `j^*B' ⟶ i^*A` of
sheaves of graded `𝒪_Z`-algebras.

It is `AlgebraicGeometry.Space.gradedPullCompMap` with the spelling of the composite taken as a
parameter: the comparison `AlgebraicGeometry.Space.gradedAlgebraPullbackCompIsoOfEq`, which
rewrites `j^*B'` as `i^*(g^*B')`, followed by the inverse image along `i` of `Ψ`.  Both factors
are morphisms of sheaves of graded algebras, so no multiplicativity is left to check. -/
noncomputable def gradedPullCompMapOfEq (i : Z ⟶ X) (g : X ⟶ X') (j : Z ⟶ X') (hj : j = i ≫ g)
    (B' : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X'))
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (Ψ : (gradedPull (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS g)).obj B' ⟶ A) :
    (gradedPull (X := smallEtaleRingedTopos B S hS Z)
        (Y := smallEtaleRingedTopos B S hS X')
        (smallEtaleRingedToposHom B S hS j)).obj B' ⟶
      (gradedPull (X := smallEtaleRingedTopos B S hS Z)
        (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS i)).obj A :=
  ((gradedAlgebraPullbackCompIsoOfEq B S hS i g j hj).app B').hom ≫
    (gradedPull (X := smallEtaleRingedTopos B S hS Z)
      (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS i)).map Ψ

/-- The degree-`n` component of `AlgebraicGeometry.Space.gradedPullCompMapOfEq` is the degree-`n`
component of the composition comparison followed by the inverse image along `i` of the degree-`n`
component of the given homomorphism. -/
theorem gradedPullCompMapOfEq_app (i : Z ⟶ X) (g : X ⟶ X') (j : Z ⟶ X') (hj : j = i ≫ g)
    (B' : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X'))
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (Ψ : (gradedPull (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS g)).obj B' ⟶ A)
    (n : ℤ) :
    (gradedPullCompMapOfEq B S hS i g j hj B' A Ψ).app n =
      ((gradedAlgebraPullbackCompIsoOfEq B S hS i g j hj).app B').hom.app n ≫
        (modulePullback B S hS i).map (Ψ.app n) :=
  rfl

/-- At the diagonal spelled `i ≫ g` and the reflexivity proof, the map above is
`AlgebraicGeometry.Space.gradedPullCompMap`. -/
theorem gradedPullCompMapOfEq_rfl (i : Z ⟶ X) (g : X ⟶ X')
    (B' : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X'))
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (Ψ : (gradedPull (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS g)).obj B' ⟶ A) :
    gradedPullCompMapOfEq B S hS i g (i ≫ g) rfl B' A Ψ = gradedPullCompMap B S hS i g B' A Ψ := by
  rw [gradedPullCompMapOfEq, gradedPullCompMap, gradedAlgebraPullbackCompIsoOfEq_rfl]

/-! ### The canonical map of Stacks 09RS for a commutative square -/

/-- **The ambient factor of [Stacks Project, Tag 09RS] for a commutative square, given a
homomorphism on the ambient space.**  For a commutative square `i ≫ g = f ≫ i'` a homomorphism
`Ψ : g^*(⨁_{n ≥ 0} 𝓙ⁿ) ⟶ ⨁_{n ≥ 0} 𝓘ⁿ` of sheaves of graded `𝒪_X`-algebras, where
`𝓙 = Ker((f ≫ i')^♯)` and `𝓘 = Ker(i^♯)`, gives

`𝒞_{Z/X',*} ⟶ 𝒞_{Z/X,*}`,

the factor of the canonical map of Stacks 09RS which replaces the ambient space `X'` by `X`.

This is `AlgebraicGeometry.Space.conormalAlgebraAmbientMapOfPullbackHom` with the square's
diagonal spelled `f ≫ i'` instead of `i ≫ g`, which is what lets it compose with the first
factor `AlgebraicGeometry.Space.conormalAlgebraPullbackCompMap` with no cast between conormal
algebras; the module documentation records why.  The module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraAmbientGradedTransport.lean` records that no
such `Ψ` is constructed, and that its degreewise family is
`AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap`. -/
noncomputable def conormalAlgebraAmbientSquareMapOfPullbackHom (i : Z ⟶ X) (i' : Z' ⟶ X')
    (f : Z ⟶ Z') (g : X ⟶ X') (hsq : i ≫ g = f ≫ i')
    (Ψ : (gradedPull (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS g)).obj
        (kernelIdealGradedAlgebra B S hS (f ≫ i')) ⟶ kernelIdealGradedAlgebra B S hS i) :
    conormalAlgebra B S hS (f ≫ i') ⟶ conormalAlgebra B S hS i :=
  gradedPullCompMapOfEq B S hS i g (f ≫ i') hsq.symm
    (kernelIdealGradedAlgebra B S hS (f ≫ i')) (kernelIdealGradedAlgebra B S hS i) Ψ

/-- **The canonical map of conormal algebras of [Stacks Project, Tag 09RS], given the ambient
graded homomorphism.**  Let

```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```

be a commutative square of algebraic spaces, `hsq : i ≫ g = f ≫ i'`.  Write
`𝓘 = Ker(i^♯) ⊆ 𝒪_X` and `𝓙 = Ker((f ≫ i')^♯) ⊆ 𝒪_{X'}` for the kernel ideal sheaf of the
diagonal.  Given a homomorphism of sheaves of graded `𝒪_X`-algebras

`Ψ : g^*(⨁_{n ≥ 0} 𝓙ⁿ) ⟶ ⨁_{n ≥ 0} 𝓘ⁿ`

on the ambient space, there is a canonical homomorphism of sheaves of graded `𝒪_Z`-algebras

`f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*}`.

It is the composite of the two factors of the source's proof: the unconditional first factor
`AlgebraicGeometry.Space.conormalAlgebraPullbackCompMap`, which carries `f^*𝒞_{Z'/X',*}` into the
conormal algebra `𝒞_{Z/X',*}` of the diagonal and rests on the containment of kernel ideal
sheaves `AlgebraicGeometry.Space.kernelIdealSheaf_le_comp`, followed by the ambient factor
`AlgebraicGeometry.Space.conormalAlgebraAmbientSquareMapOfPullbackHom`, which descends `Ψ` from
`X` to `Z` along the Stacks 03LU composition comparison.

`Ψ` is a hypothesis and not the conclusion: it is a homomorphism upstairs on the ambient space
`X` between the graded algebras of the powers of the two kernel ideal sheaves, whereas the
conclusion is a homomorphism downstairs on `Z` between the conormal algebras of the two vertical
arrows.  The module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraAmbientGradedTransport.lean` records that no
such `Ψ` is constructed yet and what its construction is waiting for.

The statement takes `i` and `i'` to be arbitrary morphisms, where Stacks 09RS takes them to be
immersions; nothing here uses any property of them, so this is strictly more general and
specialises to the source's statement. -/
@[stacks 09RS "the canonical map, given the ambient homomorphism g^*(⨁ 𝓙ⁿ) ⟶ ⨁ 𝓘ⁿ"]
noncomputable def conormalAlgebraSquareMapOfPullbackHom (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z')
    (g : X ⟶ X') (hsq : i ≫ g = f ≫ i')
    (Ψ : (gradedPull (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS g)).obj
        (kernelIdealGradedAlgebra B S hS (f ≫ i')) ⟶ kernelIdealGradedAlgebra B S hS i) :
    (gradedPull (X := smallEtaleRingedTopos B S hS Z)
        (Y := smallEtaleRingedTopos B S hS Z')
        (smallEtaleRingedToposHom B S hS f)).obj (conormalAlgebra B S hS i') ⟶
      conormalAlgebra B S hS i :=
  conormalAlgebraPullbackCompMap B S hS f i' ≫
    conormalAlgebraAmbientSquareMapOfPullbackHom B S hS i i' f g hsq Ψ

/-- The canonical map of Stacks 09RS is the first factor followed by the ambient factor. -/
theorem conormalAlgebraSquareMapOfPullbackHom_eq (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z')
    (g : X ⟶ X') (hsq : i ≫ g = f ≫ i')
    (Ψ : (gradedPull (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS g)).obj
        (kernelIdealGradedAlgebra B S hS (f ≫ i')) ⟶ kernelIdealGradedAlgebra B S hS i) :
    conormalAlgebraSquareMapOfPullbackHom B S hS i i' f g hsq Ψ =
      conormalAlgebraPullbackCompMap B S hS f i' ≫
        conormalAlgebraAmbientSquareMapOfPullbackHom B S hS i i' f g hsq Ψ :=
  rfl

/-- **The degree-`n` component of the canonical map of Stacks 09RS** is the degree-`n` component
of the first factor followed by the degree-`n` component of the ambient factor. -/
theorem conormalAlgebraSquareMapOfPullbackHom_app (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z')
    (g : X ⟶ X') (hsq : i ≫ g = f ≫ i')
    (Ψ : (gradedPull (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS g)).obj
        (kernelIdealGradedAlgebra B S hS (f ≫ i')) ⟶ kernelIdealGradedAlgebra B S hS i)
    (n : ℤ) :
    (conormalAlgebraSquareMapOfPullbackHom B S hS i i' f g hsq Ψ).app n =
      (conormalAlgebraPullbackCompMap B S hS f i').app n ≫
        (conormalAlgebraAmbientSquareMapOfPullbackHom B S hS i i' f g hsq Ψ).app n :=
  SheafOfModules.GradedAlgebra.categoryStruct_comp_app _ _ n

end AlgebraicGeometry.Space

end
