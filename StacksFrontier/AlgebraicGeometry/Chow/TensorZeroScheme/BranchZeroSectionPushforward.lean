module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionPushforwardCycle
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchZeroSectionChern

/-!
# The pushforward along the zero section of a branch, in the orientation of Tag 0F98

Clause (5) of [Stacks, Tag 0F96] computes the pushforward along the zero section of a line bundle
`D : Stacks.LineBundle.Situation` as

  `o_* α = - p^*(c₁(D.L) ∩ α)`,

a *minus* sign, against the situation's own module `D.L`.

The proof of [Stacks, Tag 0F98] uses that clause at the branch `D₁` of [Stacks, Tag 0F97], whose
line-bundle structure is `branchSituation Y L₁ L₂ s L₂` by clause (4) of that tag — and the module
of *that* situation is already an inverse, `(L₂^{⊗ -1})|_D`. The source's last step in the case
`W ⊆ D`,

  "Since `W₁ ∩ W₂` is the zero section of the line bundle `W₁ → W` we see from Lemma 42.32.4 that
  `[W₁ ∩ W₂]_k = p₁^*(c₁(L₂) ∩ [W])`",

therefore wants `+ p₁^*(c₁(L₂|_D) ∩ −)`, and the two negations must cancel rather than be
compensated by inserting a sign. This file works that out, at the branch and at the level of
cycles: the pushforward along the zero section of `branchSituation Y L₁ L₂ s N` is
`+ p^*(c₁(N|_D) ∩ α)`, with **no** sign.

It is the same cancellation as for clause (6), which
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchZeroSectionChern` records, and the
inversion is the same named lemma,
`Stacks.Chow.TensorZeroScheme.firstChernClassCapOfInvertible_branchSituation_eq_neg`.

## Main results

* `Stacks.Chow.TensorZeroScheme.zeroSectionChowPushforward_branchSituation_mk` — **clause (5) of
  [Stacks, Tag 0F96] at a branch of [Stacks, Tag 0F97], in the orientation Tag 0F98 uses**, with a
  cycle as the argument.
* `Stacks.Chow.TensorZeroScheme.rationallyEquivalent_properPushforward_zeroSection_branchSituation`
  — the same at the level of cycles: the pushforward of `α` along the zero section of the branch
  is rationally equivalent to any cycle representing `p^*(c₁(N|_D) ∩ α)`, with no sign.

## Implementation notes

### Why the invertibility of `N|_D` is an instance argument

Instance search does not find it: the base of `branchSituation Y L₁ L₂ s N` is `D` only after the
situation is unfolded, which instance search will not do. Clause (6) at the branch supplies it by
a `letI` inside the statement, which it can do because its statement is a bare identity. Here the
cycle-level statement carries a hypothesis `hγ` that mentions the cap product, so the instance has
to be in scope before that hypothesis: it is taken as an instance argument, always dischargeable
by `Stacks.Divisors.pullback_isInvertible`.

### No `@[stacks]` attribute here

This is clause (5) of Tag 0F96 instantiated and re-oriented, not a new assertion of it: the
carrier of that clause is
`Stacks.Chow.zeroSectionChowPushforward_eq_neg_flatPullbackChow_firstChernClassCapChow`. Nor does
anything here assert [Stacks, Tag 0F98], which is a single identity of maps and is carried by
`Stacks.Chow.TensorZeroScheme.gysinChowBranch₁_flatPullbackChowProj` of
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionBranchChowIdentity`; see the
convention note in `StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChowMaps`.

## References

* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.TensorZeroScheme

attribute [local instance] Stacks.LineBundle.Situation.flat_totalSpaceToBase

variable (C : Stacks.Chow.ChowSituation.{u}) (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)) (N : Y.Modules)
  [hN : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property N]
  (sD : (branchSituation Y L₁ L₂ s N).X ⟶ C.S) [LocallyOfFiniteType sD]
  [AlgebraicGeometry.SheafOfModules.IsInvertible (branchSituation Y L₁ L₂ s N).X.sheaf.obj
    (branchSituation Y L₁ L₂ s N).X.ringCatSheaf.property
    ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj N)]

include h₁ h₂ hN in
/-- **Clause (5) of [Stacks, Tag 0F96] at a branch of [Stacks, Tag 0F97], in the orientation
[Stacks, Tag 0F98] uses.** For the line bundle `branchSituation Y L₁ L₂ s N` over `D`, whose
module is already the inverse of `N`, the pushforward along the zero section of a cycle
`α ∈ Z_{k+1}(D)` is

  `o_* α = + p^*(c₁(N|_D) ∩ α)`,

with no sign: the minus of 0F96 (5) is cancelled by the inversion in `branchSituation`, which is
`Stacks.Chow.TensorZeroScheme.firstChernClassCapOfInvertible_branchSituation_eq_neg`. At
`N = L₂` this is the step of the proof of Tag 0F98 that identifies `[W₁ ∩ W₂]` with
`p₁^*(c₁(L₂) ∩ [W])`. -/
theorem zeroSectionChowPushforward_branchSituation_mk (k : ℤ)
    (α : Stacks.Chow.CycleGroup C sD (k + 1)) :
    Stacks.Chow.zeroSectionChowPushforward C (branchSituation Y L₁ L₂ s N) sD (k + 1)
        (QuotientAddGroup.mk' (Stacks.Chow.rationalEquivalences C sD (k + 1)) α) =
      Stacks.Chow.chowGroupCast C ((branchSituation Y L₁ L₂ s N).totalSpaceToBase ≫ sD)
        (show k + ((1 : ℕ) : ℤ) = k + 1 from by simp)
        (Stacks.Chow.flatPullbackChowOfRelativeDimension C
          ((branchSituation Y L₁ L₂ s N).totalSpaceToBase ≫ sD) sD
          (branchSituation Y L₁ L₂ s N).totalSpaceToBase rfl 1
          (branchSituation Y L₁ L₂ s N).relativeDimension_totalSpaceToBase k
          (Stacks.Chow.firstChernClassCapOfInvertible C sD k
            ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj N) α)) := by
  rw [zeroSectionChowPushforward_mk_eq_neg_flatPullbackChow_firstChernClassCapOfInvertible
      C (branchSituation Y L₁ L₂ s N) sD k α,
    firstChernClassCapOfInvertible_branchSituation_eq_neg C Y L₁ L₂ s N sD k α, map_neg, map_neg,
    neg_neg]

include h₁ h₂ hN in
/-- **Clause (5) of [Stacks, Tag 0F96] at a branch, at the level of cycles.** Let
`α ∈ Z_{k+1}(D)` be a cycle and let `γ` be any cycle on the total space of
`branchSituation Y L₁ L₂ s N` representing the class `p^*(c₁(N|_D) ∩ α)`. Then the pushforward of
`α` along the zero section of the branch and `γ` are rationally equivalent cycles — with no sign,
the inversion in `branchSituation` having cancelled the one of the clause.

This is the shape the dévissage of [Stacks, Tag 0F98] consumes: pushed into an ambient scheme
along a closed immersion it becomes a cycle rationally equivalent to zero within the image of
that immersion, by
`Stacks.Chow.properPushforward_sub_isRationallyEquivalentToZeroWithin`. Which cycle `γ`
represents the class is the consumer's choice, and every class has a representative. -/
theorem rationallyEquivalent_properPushforward_zeroSection_branchSituation (k : ℤ)
    (α : Stacks.Chow.CycleGroup C sD (k + 1))
    (γ : Stacks.Chow.CycleGroup C
      ((branchSituation Y L₁ L₂ s N).totalSpaceToBase ≫ sD) (k + 1))
    (hγ : QuotientAddGroup.mk' (Stacks.Chow.rationalEquivalences C
        ((branchSituation Y L₁ L₂ s N).totalSpaceToBase ≫ sD) (k + 1)) γ =
      Stacks.Chow.chowGroupCast C ((branchSituation Y L₁ L₂ s N).totalSpaceToBase ≫ sD)
        (show k + ((1 : ℕ) : ℤ) = k + 1 from by simp)
        (Stacks.Chow.flatPullbackChowOfRelativeDimension C
          ((branchSituation Y L₁ L₂ s N).totalSpaceToBase ≫ sD) sD
          (branchSituation Y L₁ L₂ s N).totalSpaceToBase rfl 1
          (branchSituation Y L₁ L₂ s N).relativeDimension_totalSpaceToBase k
          (Stacks.Chow.firstChernClassCapOfInvertible C sD k
            ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj N) α))) :
    Stacks.Chow.RationallyEquivalent C
      ((branchSituation Y L₁ L₂ s N).totalSpaceToBase ≫ sD) (k + 1)
      (Stacks.Chow.properPushforward C sD
        ((branchSituation Y L₁ L₂ s N).totalSpaceToBase ≫ sD)
        (branchSituation Y L₁ L₂ s N).zeroSection
        (Stacks.Chow.zeroSection_comp_totalSpaceToBase_comp C (branchSituation Y L₁ L₂ s N) sD)
        (k + 1) α) γ := by
  have h := zeroSectionChowPushforward_branchSituation_mk C Y L₁ L₂ s N sD k α
  rw [Stacks.Chow.zeroSectionChowPushforward_mk, ← hγ] at h
  exact QuotientAddGroup.eq_iff_sub_mem.1 h

end Stacks.Chow.TensorZeroScheme

end
