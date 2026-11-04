module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardDescent.Stack
public import StacksCore.Tactic.StacksAttribute

/-!
# The Picard stack is a stack in groupoids (Stacks 04WN)

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` of a big fppf site, the
standing data of Stacks 0D25, and let `p : Picardstack_{X/B} ⟶ (Sch/S)_fppf` be the functor of
Section 0372 sending a triple `(U, b, L)` to its test scheme `U`.  Stacks 04WN asserts that, up to
the replacement of Stacks 03ZZ, `p` is a stack in groupoids.  This file states it, for the
category of Section 0372 built from the pseudofunctoriality of the direct images of Stacks 03LU
(`AlgebraicGeometry.Space.modulePushforwardCoherence`), with all three conditions of Stacks 02ZI.

## Main results

* `AlgebraicGeometry.Space.picardBasedCategory_isStackInGroupoids`: **Stacks 04WN.**

## Implementation notes

The proof is the one of the source: condition (1) is
`AlgebraicGeometry.Space.picardBasedCategory_isFiberedInGroupoids`, and conditions (2) and (3)
follow from the stack condition of Stacks 026F,
`AlgebraicGeometry.Space.picardBasedCategory_isStack`, by Stacks 02ZJ
(`CategoryTheory.Functor.IsStack.isStackInGroupoids`).  The stack condition is checked on the
fppf covering families, which generate the topology: the structure morphisms `b_i` glue to a
morphism `b : U ⟶ B` because `B` is a sheaf, the family `{X_{U_i} ⟶ X_U}` is an fpqc covering,
the invertible modules and their comparisons glue along it by Stacks 04W8
(`AlgebraicGeometry.Space.PicardHom.exists_picardObject_of_isFpqcCovering` and
`AlgebraicGeometry.Space.PicardHom.exists_comp_eq_of_isFpqcCovering`), and the module obtained
is invertible because its inverse images are
(`AlgebraicGeometry.Space.isInvertibleModule_of_pullback_isFpqcCovering`).

**The replacement of Stacks 03ZZ.**  In the source the objects of `Picardstack_{X/B}` form a
proper class, and `p` is replaced by its restriction to a full subcategory with set-sized fibres
before it can be a stack.  Here `AlgebraicGeometry.Space.PicardObject` is a type and the
predicates of Stacks 02ZI and 026F apply to `p` itself, so the statement below is made for `p`
with no replacement; it is the stronger form.  The replacement of the source is available on top
of it: `CategoryTheory.Functor.IsStack.fibreRepresentatives` carries the stack condition to the
cutdown of Stacks 03ZZ, whose inclusion is an equivalence by
`CategoryTheory.Functor.isEquivalence_ι_fibreRepresentatives`.

## References

* [Stacks Project, Tag 04WN](https://stacks.math.columbia.edu/tag/04WN)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
* [Stacks Project, Tag 03ZZ](https://stacks.math.columbia.edu/tag/03ZZ)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
-/

@[expose] public section

open CategoryTheory

universe w u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 04WN.**  In Situation 0D25, the functor `p : Picardstack_{X/B} ⟶ (Sch/S)_fppf` of
Section 0372, sending `(U, b, L)` to `U`, is a stack in groupoids over the big fppf site of `S`:
it is fibred in groupoids, its `Isom` presheaves are sheaves, and every descent datum relative to
an fppf covering is effective.

The statement is made for `p` itself rather than for the cutdown of Stacks 03ZZ, the objects of
`Picardstack_{X/B}` forming a type. -/
@[stacks 04WN "the functor Picardstack_{X/B} ⟶ (Sch/S)_fppf is a stack in groupoids: all three \
conditions of Stacks 02ZI"]
theorem picardBasedCategory_isStackInGroupoids (s : PicardSituation B S hS) :
    Functor.IsStackInGroupoids.{w} (picardBasedCategory (modulePushforwardCoherence B S hS) s).p
      (BigFppfOver.topology B S hS) :=
  Functor.IsStack.isStackInGroupoids (picardBasedCategory_isStack s)
    (picardBasedCategory_isFiberedInGroupoids (modulePushforwardCoherence B S hS) s)

end AlgebraicGeometry.Space

end
