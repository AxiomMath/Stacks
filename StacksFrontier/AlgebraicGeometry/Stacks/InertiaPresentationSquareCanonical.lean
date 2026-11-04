module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaQuotientStackSquareFibred

/-!
# Stacks 06PR for the canonical input

`StacksFrontier/AlgebraicGeometry/Stacks/InertiaPresentationSquare.lean` proves Stacks 06PR for an
arbitrary `AlgebraicGeometry.Stack.InertiaQuotientStackInput`, a record of six data about the
presenting groupoid of a presentation `[U/R] ⟶ 𝒳`. This file builds that record, for every
presentation, out of the theorems the library already has, and so states Stacks 06PR with no input
beyond the presentation itself.

## Main definitions

* `AlgebraicGeometry.Stack.inertiaQuotientStackInput`: the canonical input of a presentation.
* `AlgebraicGeometry.Stack.presentationInertiaSquare`: the diagram of Stacks 06PR of a
  presentation.

## Main results

* `AlgebraicGeometry.Stack.isTwoFibreProduct_presentationInertiaSquare` and
  `AlgebraicGeometry.Stack.nonempty_isTwoFibreProduct_presentationInertiaSquare`: **Stacks 06PR**.

## Implementation notes

The six fields come from two places. The first three are the square of Stacks 06PC with `[G/R']`
in the lower-left corner, read in the 2-category of categories fibred in groupoids, which is
`AlgebraicGeometry.Stack.inertiaQuotientStackSquareFibred` and
`AlgebraicGeometry.Stack.isTwoFibreProduct_inertiaQuotientStackSquareFibred`; the last three are
the second assertion of Stacks 06PB, which is
`AlgebraicGeometry.Stack.inertiaQuotientStackCompare`,
`AlgebraicGeometry.Stack.inertiaQuotientStackCompareOver` and
`AlgebraicGeometry.Stack.isEquivalence_inertiaQuotientStackCompare`.

Each field is taken on the nose. `AlgebraicGeometry.Stack.presentationStabilizerStack` and
`AlgebraicGeometry.Stack.liftedSpaceStack` of the stabilizer are the same object — they wrap the
same category over the site with different proofs that its structure functor is fibred in
groupoids, and `CategoryTheory.CatFiberedInGroupoids` is a subtype, so the two proofs are
irrelevant to it; the same holds for the object space, and
`AlgebraicGeometry.Stack.presentationQuotientStack` is
`AlgebraicGeometry.Stack.quotientStackCFG` of the presenting groupoid by definition. So the three
legs and the filler of `AlgebraicGeometry.Stack.inertiaQuotientStackSquareFibred` typecheck
directly as the first three fields, and structure eta makes the square the `cartesian` field asks
about the square that is already proved 2-cartesian.

Only the presenting groupoid enters, never `𝒳` or its inertia, so nothing here is an instance of
the conclusion.

## References

* [Stacks Project, Tag 06PB](https://stacks.math.columbia.edu/tag/06PB)
* [Stacks Project, Tag 06PC](https://stacks.math.columbia.edu/tag/06PC)
* [Stacks Project, Tag 06PR](https://stacks.math.columbia.edu/tag/06PR)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS)}
  (P : GroupoidPresentation B S hS 𝒳.val)

/-- **The canonical input of Stacks 06PR.** The six data
`AlgebraicGeometry.Stack.InertiaQuotientStackInput` records about the presenting groupoid of a
presentation `[U/R] ⟶ 𝒳`, supplied by the library: the square of Stacks 06PC with `[G/R']` in its
lower-left corner together with its universal property, and the comparison
`[G/R'] ⟶ ℐ_{[U/R]}` of the second assertion of Stacks 06PB together with its compatibility over
`[U/R]` and the fact that it is an equivalence.

Nothing is assumed: every field is a theorem of this library about the groupoid
`(U, R, s, t, c)` alone. -/
noncomputable def inertiaQuotientStackInput : InertiaQuotientStackInput B S hS P where
  toInertiaGroupoid := (inertiaQuotientStackSquareFibred P.groupoid).fst
  commutes := (inertiaQuotientStackSquareFibred P.groupoid).iso
  cartesian := isTwoFibreProduct_inertiaQuotientStackSquareFibred P.groupoid
  compare := inertiaQuotientStackCompare P.groupoid
  compare_over := inertiaQuotientStackCompareOver P.groupoid
  compare_isEquivalence := isEquivalence_inertiaQuotientStackCompare P.groupoid

/-- **The diagram of Stacks 06PR.** For a presentation `[U/R] ⟶ 𝒳` with presenting groupoid
`(U, R, s, t, c)` and stabilizer group algebraic space `G/U` (Stacks 0448), the 2-commutative
square

```
𝒮_G  ------>  𝒮_U
 |             |
 v             v
ℐ_𝒳  ------>  𝒳
```

of `AlgebraicGeometry.Stack.inertiaPresentationSquare`, built from the canonical input
`AlgebraicGeometry.Stack.inertiaQuotientStackInput` and hence depending on nothing but the
presentation. -/
noncomputable def presentationInertiaSquare :
    Bicategory.TwoCommSq (inertiaCatProjection B S hS 𝒳)
      (presentationObjectProjection B S hS P ≫ presentationMorphism B S hS P) :=
  inertiaPresentationSquare B S hS P (inertiaQuotientStackInput P)

/-- The apex of the diagram of Stacks 06PR is the stack `𝒮_G` of the stabilizer group algebraic
space `G/U` of Stacks 0448. -/
theorem presentationInertiaSquare_pt :
    (presentationInertiaSquare P).pt = presentationStabilizerStack B S hS P := rfl

/-- The second leg of the diagram of Stacks 06PR is the 1-morphism `𝒮_G ⟶ 𝒮_U` induced by the
structure morphism `G ⟶ U` of the stabilizer, on the nose. -/
theorem presentationInertiaSquare_snd :
    (presentationInertiaSquare P).snd = presentationStabilizerProjection B S hS P := rfl

/-- **Stacks 06PR.** Let `𝒳` be a category fibred in groupoids over the big fppf site of `S` — in
particular an algebraic stack — and let `[U/R] ⟶ 𝒳` be a presentation (Stacks 04TI). Let `G/U` be
the stabilizer group algebraic space associated to the groupoid `(U, R, s, t, c)` (Stacks 0448).
Then

```
𝒮_G  ------>  𝒮_U
 |             |
 v             v
ℐ_𝒳  ------>  𝒳
```

is a fibre product diagram, i.e. a 2-fibre product in the sense of Stacks 003Q.

This is `AlgebraicGeometry.Stack.isTwoFibreProduct_inertiaPresentationSquare` at the canonical
input of `AlgebraicGeometry.Stack.inertiaQuotientStackInput`, so the proof is the proof of the
source — immediate from Groupoids in Spaces, Lemma 06PC
(`AlgebraicGeometry.Stack.isTwoFibreProduct_inertiaQuotientStackSquareFibred` together with the
second assertion of Stacks 06PB) pasted onto the inertia square of Stacks 06R5 for the
presentation — and the only datum it consumes is the presentation. -/
@[stacks 06PR "the diagram is 2-cartesian"]
noncomputable def isTwoFibreProduct_presentationInertiaSquare :
    Bicategory.IsTwoFibreProduct (presentationInertiaSquare P) :=
  isTwoFibreProduct_inertiaPresentationSquare B S hS P (inertiaQuotientStackInput P)

/-- **Stacks 06PR**, in propositional form: for a presentation `[U/R] ⟶ 𝒳` the diagram of the
stack of the stabilizer, the stack of the object space, the inertia of `𝒳` and `𝒳` is a fibre
product diagram. -/
@[stacks 06PR "the diagram is a fibre product diagram"]
theorem nonempty_isTwoFibreProduct_presentationInertiaSquare :
    Nonempty (Bicategory.IsTwoFibreProduct (presentationInertiaSquare P)) :=
  ⟨isTwoFibreProduct_presentationInertiaSquare P⟩

end AlgebraicGeometry.Stack

end
