module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreProjectiveLineInjective
public import
 StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperPushforwardBaseChangeUnconditional
import StacksCore.Tactic.StacksAttribute

/-!
# The proper base change theorem and its inputs, as Stacks tags

The proper base change theorem for étale cohomology and the results leading to it are proved,
with no assumed inputs, in the modules `ClosedFibreProjectiveLineInjective`,
`ProperPushforwardBaseChangeUnconditional` and `ProperBaseChangeTheoremUnconditional` of
`StacksDraft.AlgebraicGeometry.EtaleCohomology.ProperBaseChange`. This file records the Stacks
tags on those declarations.

## Main results

* `Stacks.EtaleCohomology.subsingleton_H_closedFibre_projectiveLine_of_injective` —
  **[Stacks, Tag 0A5H]**: for `A` henselian local, `X = ℙ¹_A` with closed fibre `X₀` and `𝓘` an
  injective sheaf of `ℤ/ℓℤ`-modules on `X_étale`, `H^q(X₀, 𝓘|_{X₀}) = 0` for `q > 0`.
* `Stacks.EtaleCohomology.isIso_properGeometricFibreComparison_of_isProper` —
  **[Stacks, Tag 0A3T]**: for `f` proper, `(f_* F)_x ⟶ Γ(X_x, F_x)` is bijective.
* `Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper` — **[Stacks, Tag 0A3U]**:
  for `f` proper, `g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F` is an isomorphism for every sheaf of sets `F`.
* `Stacks.EtaleCohomology.etaleCohomologyBaseChangeMap_bijective_of_isSepClosed` —
  **[Stacks, Tag 0A5E]**: for separably closed fields `k ⊆ k'`, `X` proper over `k` of dimension
  at most one and `F` torsion, `H^q(X, F) ⟶ H^q(X_{k'}, F|_{X_{k'}})` is bijective.
* `Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_of_isProper` —
  **[Stacks, Tag 095T]**: the proper base change theorem.

## References

* [Stacks Project, Tag 0A5H](https://stacks.math.columbia.edu/tag/0A5H)
* [Stacks Project, Tag 0A3T](https://stacks.math.columbia.edu/tag/0A3T)
* [Stacks Project, Tag 0A3U](https://stacks.math.columbia.edu/tag/0A3U)
* [Stacks Project, Tag 0A5E](https://stacks.math.columbia.edu/tag/0A5E)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
-/

@[expose] public section

add_to_stacks 0A5H Stacks.EtaleCohomology.subsingleton_H_closedFibre_projectiveLine_of_injective

add_to_stacks 0A3T Stacks.EtaleCohomology.isIso_properGeometricFibreComparison_of_isProper

add_to_stacks 0A3U Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper

add_to_stacks 0A5E Stacks.EtaleCohomology.etaleCohomologyBaseChangeMap_bijective_of_isSepClosed

add_to_stacks 095T Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_of_isProper

end
