module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionSelfIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchLineBundle

/-!
# The self-intersection of the zero section of a branch, in the orientation of Tag 0F98

Clause (6) of [Stacks, Tag 0F96] computes the composite `o^*o_*` of the Gysin map and the
pushforward of the zero section of a line bundle `D : Stacks.LineBundle.Situation` as
`α ↦ -c₁(D.L) ∩ α`: a *minus* sign, against the situation's own module `D.L`.

The proof of [Stacks, Tag 0F98] uses that clause at the branch `D₁` of [Stacks, Tag 0F97], whose
line-bundle structure is `branchSituation Y L₁ L₂ s L₂` by clause (4) of that tag — and the module
of *that* situation is already an inverse, `(L₂^{⊗ -1})|_D`. The source's reading of the step,
"`[W₁ ∩ W₂]_k = p₁^*(c₁(L₂) ∩ [W])` … here we use the fact that `D₁` is the line bundle which is
the relative spectrum of the inverse of `L₂`", therefore wants `+ c₁(L₂|_D) ∩ −`, and the two
negations must cancel rather than be compensated by inserting a sign.

This file works that out: the composite at `branchSituation Y L₁ L₂ s L₂` is
`α ↦ + c₁(L₂|_D) ∩ α`, with **no** sign.

## Main results

* `Stacks.Chow.TensorZeroScheme.firstChernClassCapOfInvertible_branchSituation_eq_neg` — the
  inversion itself: capping with `c₁` of the module of the branch situation is minus capping with
  `c₁(N|_D)`.
* `Stacks.Chow.TensorZeroScheme.zeroSectionGysinChow_zeroSectionChowPushforward_branchSituation` —
  **clause (6) of [Stacks, Tag 0F96] at a branch of [Stacks, Tag 0F97], in the orientation Tag
  0F98 uses**: the sign of the tag is cancelled by the inversion in `branchSituation`.

## Implementation notes

The first sign is that of 0F96 (6) itself,
`Stacks.Chow.zeroSectionGysinChow_zeroSectionChowPushforward_mk`, which is stated against
`D.L`. The second comes from `D.L` for `D = branchSituation Y L₁ L₂ s N` being the restriction
to `D` of the inverse of `N`: `Stacks.Chow.TensorZeroScheme.branchSituationModuleIso` identifies
it with the inverse of the restriction, and
`Stacks.Chow.firstChernClassCapOfInvertible_eq_neg_of_tensorObj_iso_unit`, with the unit
isomorphism `Stacks.Chow.tensorObjTensorPowerNegOneIso`, replaces `c₁` of an inverse by minus `c₁`.

## References

* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.TensorZeroScheme

variable (C : Stacks.Chow.ChowSituation.{u}) (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)) (N : Y.Modules)
  [hN : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property N]

include h₁ h₂ hN in
/-- **Capping with the first Chern class of the module of `branchSituation Y L₁ L₂ s N` is minus
capping with the first Chern class of `N|_D`.** The module of the situation is the restriction
to `D` of the inverse of `N`. -/
theorem firstChernClassCapOfInvertible_branchSituation_eq_neg
    (sD : (branchSituation Y L₁ L₂ s N).X ⟶ C.S) [LocallyOfFiniteType sD]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (branchSituation Y L₁ L₂ s N).X.sheaf.obj
      (branchSituation Y L₁ L₂ s N).X.ringCatSheaf.property
      ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj N)] (k : ℤ)
    (α : Stacks.Chow.CycleGroup C sD (k + 1)) :
    Stacks.Chow.firstChernClassCapOfInvertible C sD k (branchSituation Y L₁ L₂ s N).L α =
      -Stacks.Chow.firstChernClassCapOfInvertible C sD k
        ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj N) α := by
  let := isInvertible_branchSituationBase Y L₁ L₂ s N
  let := Stacks.Chow.isInvertible_tensorPowerNegOne (branchSituation Y L₁ L₂ s N).X
    ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj N)
  rw [Stacks.Chow.firstChernClassCapOfInvertible_congr C sD k _ _
    (branchSituationModuleIso Y L₁ L₂ s N) α]
  exact Stacks.Chow.firstChernClassCapOfInvertible_eq_neg_of_tensorObj_iso_unit C sD k
    ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj N) _
    (Stacks.Chow.tensorObjTensorPowerNegOneIso (branchSituation Y L₁ L₂ s N).X
      ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj N)) α

include h₁ h₂ hN in
/-- **Clause (6) of [Stacks, Tag 0F96] at a branch of [Stacks, Tag 0F97], in the orientation
[Stacks, Tag 0F98] uses.** For the line bundle `branchSituation Y L₁ L₂ s N` over `D`, whose module
is already the inverse of `N`, the composite `o^*o_*` of the Gysin map and the pushforward of the
zero section is

  `α ↦ + c₁(N|_D) ∩ α`,

with no sign: the minus of 0F96 (6) is cancelled by the inversion in `branchSituation`. -/
theorem zeroSectionGysinChow_zeroSectionChowPushforward_branchSituation
    (sD : (branchSituation Y L₁ L₂ s N).X ⟶ C.S) [LocallyOfFiniteType sD] (k : ℤ)
    (α : Stacks.Chow.CycleGroup C sD (k + 1)) :
    letI : AlgebraicGeometry.SheafOfModules.IsInvertible
        (branchSituation Y L₁ L₂ s N).X.sheaf.obj
        (branchSituation Y L₁ L₂ s N).X.ringCatSheaf.property
        ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj N) :=
      Stacks.Divisors.pullback_isInvertible _ _
    Stacks.Chow.zeroSectionGysinChow C (branchSituation Y L₁ L₂ s N) sD k
        (Stacks.Chow.zeroSectionChowPushforward C (branchSituation Y L₁ L₂ s N) sD (k + 1)
          (QuotientAddGroup.mk' (Stacks.Chow.rationalEquivalences C sD (k + 1)) α)) =
      Stacks.Chow.firstChernClassCapOfInvertible C sD k
        ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj N) α := by
  let : AlgebraicGeometry.SheafOfModules.IsInvertible
      (branchSituation Y L₁ L₂ s N).X.sheaf.obj
      (branchSituation Y L₁ L₂ s N).X.ringCatSheaf.property
      ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj N) :=
    Stacks.Divisors.pullback_isInvertible _ _
  rw [Stacks.Chow.zeroSectionGysinChow_zeroSectionChowPushforward_mk C
    (branchSituation Y L₁ L₂ s N) sD k α,
    firstChernClassCapOfInvertible_branchSituation_eq_neg C Y L₁ L₂ s N sD k α, neg_neg]

end Stacks.Chow.TensorZeroScheme

end
