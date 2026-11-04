module

public import StacksFrontier.Deformation.RingThickening.CotangentExtComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Solutions of a square-zero extension problem form a torsor under `Ext¹_B(L_{B/A}, N)`

Let `A' → A` be a surjection of rings with square-zero kernel `I`, let `A → B` be a ring map,
let `N` be a `B`-module and `c : I → N` an `A`-linear map. If the resulting extension problem has
a solution, its isomorphism classes of solutions form a principal homogeneous space under
`Ext¹_B(L_{B/A}, N)`. This is part (2) of Tag 08SP: the torsor of Tag 08S7, under
`Ext¹_B(NL_{B/A}, N)`, transported along the identification
`Ext¹_B(NL_{B/A}, N) = Ext¹_B(L_{B/A}, N)` given by `NL_{B/A} = τ_{≥ -1} L_{B/A}` (Tag 08RB).

## Main definitions

* `Stacks.Deformation.SquareZeroExtensionProblem.isomorphismClassesCotangentTorsor`: the
  principal homogeneous space structure.

## Main results

* `Stacks.Deformation.SquareZeroExtensionProblem.isomorphismClassesCotangentTorsor_vsub`: the
  difference `[Y] -ᵥ [X]` is the image in `Ext¹_B(L_{B/A}, N)` of the obstruction class of
  Tag 08S5 to an isomorphism from `X` to `Y`, so the structure is canonical.

## References

* [Stacks Project, Tag 08SP](https://stacks.math.columbia.edu/tag/08SP)
* [Stacks Project, Tag 08S7](https://stacks.math.columbia.edu/tag/08S7)
-/

@[expose] public section

open CategoryTheory

universe u₁ u₂ u₄ v w

namespace Stacks.Deformation.SquareZeroExtensionProblem

variable (S : SquareZeroExtensionProblem.{u₁, u₂, max u₂ v, u₄})

/-- **Stacks 08SP**, part (2). If the square-zero extension problem has a solution, its set of
isomorphism classes of solutions is a principal homogeneous space under `Ext¹_B(L_{B/A}, N)`.

The action is that of Tag 08S7 under `Ext¹_B(NL_{B/A}, N)`, read through the identification
`Ext¹_B(NL_{B/A}, N) = Ext¹_B(L_{B/A}, N)` of `cotangentExtOneEquiv`. -/
@[stacks 08SP "(2): if a solution exists, the isomorphism classes of solutions form a principal \
  homogeneous space under Ext¹_B(L_{B/A}, N)", instance_reducible]
noncomputable def isomorphismClassesCotangentTorsor
    (h : Nonempty (S.CompatibleExtension.{w})) :
    AddTorsor (S.cotangentExt 1)
      (CompatibleExtension.IsomorphismClasses.{u₁, u₂, max u₂ v, u₄, w} S) :=
  letI t := isomorphismClassesTorsor S h
  { vadd := fun g x => (cotangentExtOneEquiv.{u₁, u₂, u₄, v} S).symm g +ᵥ x
    zero_vadd := fun x =>
      (congrArg (· +ᵥ x) (map_zero (cotangentExtOneEquiv.{u₁, u₂, u₄, v} S).symm)).trans
        (zero_vadd _ x)
    add_vadd := fun g g' x =>
      (congrArg (· +ᵥ x) (map_add (cotangentExtOneEquiv.{u₁, u₂, u₄, v} S).symm g g')).trans
        (add_vadd _ _ x)
    vsub := fun x y => cotangentExtOneEquiv.{u₁, u₂, u₄, v} S (x -ᵥ y)
    nonempty := t.nonempty
    vsub_vadd' := fun x y =>
      (congrArg (· +ᵥ y) ((cotangentExtOneEquiv.{u₁, u₂, u₄, v} S).symm_apply_apply
        (x -ᵥ y))).trans (vsub_vadd x y)
    vadd_vsub' := fun g x =>
      (congrArg (cotangentExtOneEquiv.{u₁, u₂, u₄, v} S)
        (vadd_vsub ((cotangentExtOneEquiv.{u₁, u₂, u₄, v} S).symm g) x)).trans
        ((cotangentExtOneEquiv.{u₁, u₂, u₄, v} S).apply_symm_apply g) }

/-- In the principal homogeneous space of `isomorphismClassesCotangentTorsor`, the difference
`[Y] -ᵥ [X]` is the image in `Ext¹_B(L_{B/A}, N)` of the obstruction class `o(X, Y)` of
Tag 08S5 to an isomorphism from `X` to `Y`. -/
theorem isomorphismClassesCotangentTorsor_vsub (h : Nonempty (S.CompatibleExtension.{w}))
    (X Y : S.CompatibleExtension.{w}) :
    @VSub.vsub (S.cotangentExt 1)
        (CompatibleExtension.IsomorphismClasses.{u₁, u₂, max u₂ v, u₄, w} S)
        (isomorphismClassesCotangentTorsor.{u₁, u₂, u₄, v, w} S h).toVSub
        (Quotient.mk (CompatibleExtension.isomorphicSetoid S) Y)
        (Quotient.mk (CompatibleExtension.isomorphicSetoid S) X) =
      cotangentExtOneEquiv.{u₁, u₂, u₄, v} S
        (obstructionClass (comparisonDiagram X Y)).1 :=
  congrArg (cotangentExtOneEquiv.{u₁, u₂, u₄, v} S)
    (isomorphismClasses_vsub_eq_obstructionClass S h X Y)

end Stacks.Deformation.SquareZeroExtensionProblem

end
