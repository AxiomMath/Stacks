module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchComapCartier
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChowPrimeCycleTransverse

/-!
# Tag 0F98, the case `W ⊄ D`, with the source's hypothesis and no other

`Stacks.Chow.TensorZeroScheme.leftRule_cycle_eq_rightRule_cycle_of_cartier` of
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChowPrimeCycleTransverse` proves the case
`W ⊄ D` of [Stacks, Tag 0F98] from two transversality hypotheses, one for each of the two Gysin
steps: that `D ∩ W` is an effective Cartier divisor on `W`, and that `D₁ ∩ p^{-1}(W)` is one on
`p^{-1}(W)`. This file discharges both from the source's own hypothesis, which is that `W` is an
integral closed subscheme of `Y` not contained in `D` — in Lean,
`¬ zeroIdeal Y L₁ L₂ s ≤ W`, the order on ideal sheaf data being the order on ideals and so
opposite to inclusion of subschemes.

The first is `Stacks.Divisors.isEffectiveCartierDivisor_comap_zeroScheme_of_isIntegral`. The
second is `Stacks.Chow.TensorZeroScheme.isEffectiveCartierDivisor_comap_branch₁_of_not_le`, proved
from the first by base-changing the whole diagram of [Stacks, Tag 0F97] to `W` and splitting the
pure tensor `s₁ ⊗ s₂`; see
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchComapCartier`.

With that, the case `W ⊄ D` of the tag carries exactly the hypotheses the source states and no
others.

## Main results

* `Stacks.Chow.TensorZeroScheme.leftRule_cycle_eq_rightRule_cycle_of_not_le` — **the case
  `W ⊄ D` of [Stacks, Tag 0F98], from `W` integral and `W ⊄ D` alone**: the two cycles
  `i₁^*p^*[W]` and `p₁^*i^*[W]` are equal.

## Why no declaration here carries `@[stacks 0F98]`

[Stacks, Tag 0F98] is a single identity of maps `A_{k+1}(Y) ⟶ A_{k+1}(D₁)`, not a
clause-structured statement, so a qualified attribute on one of the two cases of its proof would
misrepresent a proof step as a fragment of the statement, and the bare attribute belongs on the
identity itself. That identity is
`Stacks.Chow.TensorZeroScheme.gysinChowBranch₁_flatPullbackChowProj` of
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionBranchChowIdentity`, which
consumes this case together with the case `W ⊆ D`. The same convention is recorded at
`Stacks.Chow.TensorZeroScheme.gysinChowZeroIdeal` and in the module docstring of
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChowPrimeCycleTransverse`.

## References

* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.TensorZeroScheme

variable (C : Stacks.Chow.ChowSituation.{u}) (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)) (R : Decomposition Y L₁ L₂ s)
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (k : ℤ)

include h₁ h₂ in
/-- **The case `W ⊄ D` of [Stacks, Tag 0F98].** For an integral closed subscheme `W ⊆ Y` of
delta-dimension `k+1` not contained in the divisor `D = Z(s)`, the two cycles `i₁^*p^*[W]` and
`p₁^*i^*[W]` are **equal**, both being the fundamental cycle of the scheme-theoretic inverse image
of `W` in `D₁`.

This is `Stacks.Chow.TensorZeroScheme.leftRule_cycle_eq_rightRule_cycle_of_cartier` with both of
its transversality hypotheses discharged: `D ∩ W` is an effective Cartier divisor on `W` because
`W` is integral and the restriction of `s` to it is nonzero, and `D₁ ∩ p^{-1}(W)` is one on
`p^{-1}(W)` by
`Stacks.Chow.TensorZeroScheme.isEffectiveCartierDivisor_comap_branch₁_of_not_le`. The hypotheses
are now exactly the source's. -/
theorem leftRule_cycle_eq_rightRule_cycle_of_not_le
    (W : Y.IdealSheafData) (hWint : IsIntegral W.subscheme)
    (hDim : Stacks.Chow.schemeDeltaDimension C (W.subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt))
    (hle : ¬ zeroIdeal Y L₁ L₂ s ≤ W) :
    (leftRule C Y L₁ L₂ s R sY k).cycle W hWint hDim =
      (rightRule C Y L₁ L₂ s R sY k).cycle W hWint hDim :=
  leftRule_cycle_eq_rightRule_cycle_of_cartier C Y L₁ L₂ s R sY k W hWint hDim
    (Stacks.Divisors.isEffectiveCartierDivisor_comap_zeroScheme_of_isIntegral
      (Stacks.Divisors.tensorModules L₁ L₂) s W hWint hle)
    (isEffectiveCartierDivisor_comap_branch₁_of_not_le L₁ L₂ s R W hWint hle)

end Stacks.Chow.TensorZeroScheme

end
