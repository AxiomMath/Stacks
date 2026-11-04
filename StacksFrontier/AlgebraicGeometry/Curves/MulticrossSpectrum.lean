module

public import StacksFrontier.AlgebraicGeometry.Curves.MulticrossNormalization
public import StacksFrontier.AlgebraicGeometry.Curves.NodalAlgebra

/-!
# The maximal ideals of the normalization of the two-branch multicross ring

The normalization of the two-branch multicross ring is `k[[t]] × k[[t]]`
(`Stacks.Curves.integralClosureMulticrossAlgEquiv`), which has exactly two maximal ideals
(`Stacks.Curves.encard_maximalSpectrum_pi_powerSeries`). Transporting the count along that
identification, with the bijection on maximal spectra induced by a ring isomorphism
(`Stacks.Curves.maximalSpectrumCongr`), gives the final assertion of Stacks Tag 0C4A for a node
in Case I: the normalization has two maximal ideals.

## Main results

* `Stacks.Curves.encard_maximalSpectrum_integralClosure_multicross` — the normalization of the
  two-branch multicross ring has exactly two maximal ideals.

## Implementation notes

The transport is separated from
`StacksFrontier.AlgebraicGeometry.Curves.MulticrossNormalization` because importing
`StacksFrontier.AlgebraicGeometry.Curves.NodalAlgebra` there puts enough extra instances in scope
that the elaboration of `Stacks.Curves.deltaInvariant_multicross` exceeds the default
instance-synthesis budget.

## References

* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
-/

@[expose] public noncomputable section

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k]

/-- **The normalization of the two-branch multicross ring has exactly two maximal ideals.** This
is the final assertion of Stacks Tag 0C4A — the count of maximal ideals of `A'` — for a node in
Case I of its proof. -/
theorem encard_maximalSpectrum_integralClosure_multicross :
    Set.encard (Set.univ : Set (MaximalSpectrum
      ↥(integralClosure ↥(multicross k 2) (FractionRing ↥(multicross k 2))))) = 2 := by
  rw [Set.encard_univ, ENat.card_congr
    (maximalSpectrumCongr (integralClosureMulticrossAlgEquiv k).toRingEquiv),
    ← Set.encard_univ]
  exact encard_maximalSpectrum_pi_powerSeries

end Stacks.Curves

end
