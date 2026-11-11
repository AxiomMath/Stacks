module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget

/-!
# Being an isomorphism is fpqc local on the base

This file shows that the property "`f` is an isomorphism" of morphisms of schemes is local on the
target for the fpqc precoverage: for every fpqc covering `{Yᵢ ⟶ Y}` (of any size) and every
morphism `f : X ⟶ Y`, the morphism `f` is an isomorphism if and only if each base change
`Yᵢ ×_Y X ⟶ Yᵢ` is one.

## Main results

* `Stacks.Descent.isomorphisms_isLocalAtTarget_fpqc`: being an isomorphism is fpqc local on the
  base.

## Implementation notes

The notion "fpqc local on the base" of Stacks Tag 02KO is
`CategoryTheory.MorphismProperty.IsLocalAtTarget P AlgebraicGeometry.Scheme.fpqcPrecoverage`:
its two fields are the two directions of the equivalence, for an arbitrary covering presieve of
the precoverage, with no bound on the size of the covering.

The proof applies the criterion `Stacks.Descent.isLocalAtTarget_fpqcPrecoverage` (Tag 02KP in
the fpqc case). Its inputs are Zariski locality on the target and stability under base change of
isomorphisms, which are Mathlib instances, and descent of isomorphisms along surjective flat
quasi-compact morphisms,
`AlgebraicGeometry.descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact`.

## References

* [Stacks Project, Tag 02L4](https://stacks.math.columbia.edu/tag/02L4)
-/

@[expose] public section

open CategoryTheory MorphismProperty AlgebraicGeometry

universe u

namespace Stacks.Descent

/-- **Stacks Project, Tag 02L4.** Being an isomorphism is fpqc local on the base: for every fpqc
covering `{Yᵢ ⟶ Y}` and every morphism of schemes `f : X ⟶ Y`, the morphism `f` is an
isomorphism if and only if each base change `Yᵢ ×_Y X ⟶ Yᵢ` is an isomorphism. -/
@[stacks 02L4]
instance isomorphisms_isLocalAtTarget_fpqc :
    (MorphismProperty.isomorphisms Scheme.{u}).IsLocalAtTarget Scheme.fpqcPrecoverage :=
  have := isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    (MorphismProperty.isomorphisms Scheme.{u})
  isLocalAtTarget_fpqcPrecoverage _

end Stacks.Descent

end
