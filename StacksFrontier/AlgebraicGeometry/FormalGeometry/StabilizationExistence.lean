module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationExistence.DepthLocus
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationExistence.CandidateIdeal
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationExistence.UniformAnnihilation

/-!
# The existence of the stabilizing data of Stacks 0EFI

`Stacks.Algebraization.IsStabilizingData I J s (J₀, n)` is the conclusion of Stacks 0EFI: the
ideal `J₀ ≤ J` has `V(J₀) ∩ V(I) = V(J) ∩ V(I)`, every further ideal `J' ≤ J₀` with the same
intersection has `RΓ_{J₀}(M) → RΓ_{J'}(M)` an isomorphism in degrees `≤ s`, and `(J₀ I) ^ n`
annihilates all of those cohomology modules. `Stacks.Algebraization.stabilizingData` selects such
a pair when one exists; this file proves that one does.

The ideal is the one the source constructs: `J₀ = J ⊓ I(B)` where `B` is the set of primes
`𝔭 ∉ V(I)` lying in `T = {𝔭 : V(𝔭) ∩ V(I) ⊆ V(J) ∩ V(I)}` with `depth(M_𝔭) ≤ s`, so that `V(J₀)`
is the closure of `B ∪ V(J)`; at the end it is shrunk once more to absorb the annihilator ideal.
The three claims of the source are proved as follows.

* Claim I, that `V(J₀) ∩ V(I) = V(J) ∩ V(I)` — that passing to the closure of `B` does not leave
  `T` — rests on the semicontinuity of `depth + δ` for the dimension function `δ` of a dualizing
  complex, which is Stacks 0ECM, clause (4). That clause is available in the library only for
  sheaves on a scheme and under a bundled stalkwise hypothesis, so it is proved here over a ring
  as `isClosed_depth_add_dualizingDimension_sublevel`: the sublevel locus is the union of the
  supports of the finitely many relevant `Ext^j(M, K)`, each a finite module.
* Claim II, the comparison isomorphism, is the criterion Stacks 0DWV together with the vanishing
  of local cohomology below the depth, Stacks 0AVZ.
* Claim III, the uniform annihilation, is Faltings' annihilator theorem Stacks 0EFC. It is
  applied to the *closed* subset `V(J₀) ⊆ T ∪ V(I)` rather than to `T`, which is where the source
  applies it; since `V(J₀)` is the zero locus of an ideal, the local cohomology supported in it is
  `H^i_{J₀}(M)` through the comparison of the two models of Stacks 0955, and no passage to the
  colimit over the ideals cutting out `T` is needed.

For `s ≤ 0` none of the hypotheses of the source is needed: a generic point of `closure B` outside
`B` would have `depth(M_𝔭) < s ≤ 0` by Stacks 0DWY and depth is never negative, so Claim I is
free, and the only module Claim III has to annihilate is `H⁰_{J₀}(M)`, a submodule of `M` and
hence finite. That case is proved separately and unconditionally.

## Main results

* `Stacks.Algebraization.exists_isStabilizingData` — **Stacks 0EFI**, as corrected: a stabilizing
  pair exists, given hypotheses (1)–(4) of the source and `0 ≤ d`.
* `Stacks.Algebraization.exists_isStabilizingData_of_nonpos` — **Stacks 0EFI** for `s ≤ 0`,
  with no hypothesis at all.
* `Stacks.Algebraization.depth_add_dim_gt_of_isStabilizingData` — the conclusion of Stacks 0EFI
  implies the depth-dimension inequality of Faltings' annihilator theorem along `V(J)`.
* `Stacks.Algebraization.exists_isStabilizingData_iff_of_neg` — **Stacks 0EFI for `d < 0`**: under
  (1)–(4) with a negative `d`, a stabilizing pair exists *exactly* when that inequality holds.
* `Stacks.Algebraization.finite_range_dimensionFunction_of_ringKrullDim_lt_top` — a dimension
  function on the spectrum of a Noetherian ring of finite Krull dimension takes only finitely
  many values. This is Claim I's use of Dualizing Complexes, Lemma [Stacks, Tag 0A7Z]; it is
  stated here because it is where the bound on a dimension function is available, and it is
  public because the uniformity paragraph of [Stacks, Tag 0EFX] splits its set of primes into
  the finitely many level sets of a dimension function and needs exactly this finiteness.

## `0 ≤ d` belongs to the statement of 0EFI

The source says "let `s` and `d` be integers", but its proof of Claim III uses `0 ≤ d`: having
reduced to `depth(M_𝔭) < s`, it treats the case `𝔮 ∈ V(I)` by saying that "the inequality holds by
(4)", i.e. it reads the bound `depth + dim > d + s` of (4) as the bound `depth + dim > s` that
Faltings' annihilator theorem needs. That step is false for `d < 0`, and `0 ≤ d` does not follow
from (1)–(4): (4) is a strict lower bound on `d + s`, hence monotone *downward* in `d`, while (3)
only gets weaker as `d` grows.

For `d < 0` the source's assertion is not merely unproved but false, so `0 ≤ d` is part of the
corrected statement of 0EFI rather than a restriction this development imposes; it is recorded as
a Stacks erratum on the strength of the counterexample
`Stacks.Algebraization.not_forall_exists_isStabilizingData_of_neg`
(`StacksFrontier/AlgebraicGeometry/FormalGeometry/StabilizationCounterexample.lean:451`), with
`Stacks.Algebraization.not_forall_exists_isStabilizingData` (`:483`) saying the same of the
source's own unrestricted wording. There `A` is the localization of `ℚ[x]` at the complement of
`(x) ∪ (x - 1)`, a semilocal Dedekind domain whose spectrum is the three primes `0 ⊂ 𝔪₁ = (x)`
and `0 ⊂ 𝔪₂ = (x - 1)`, and `M = A`, `I = (x(x-1))`, `J = 𝔪₁`, `s = 1`, `d = -1`: then
`V(I) = {𝔪₁, 𝔪₂}`, `V(J) ∩ V(I) = {𝔪₁}` and `T = {𝔪₁} ⊆ V(I)`, so (3) holds vacuously, (1) holds
because `A` is essentially of finite type over `ℚ`, and (4) holds at the only prime it
constrains; but at `𝔭 = 0 ∉ T ∪ V(I)` and `𝔮 = 𝔪₁` the inequality below reads `0 + 1 > 1`.
Concretely every admissible `J₀` has `V(J₀) = {𝔪₁}`, hence `H¹_{J₀}(A) = A[1/x]/A`, whose
annihilator is zero, while `J₀ I ≠ 0`: no power of `J₀ I` annihilates it. A *local* ring cannot do
this — there `T ⊆ V(I)` forces `I` to be nilpotent and the conclusion is degenerate — which is why
the companion maximal-ideal statement `exists_isStabilizingData_maximalIdeal` needs no `0 ≤ d`.

Three things are proved here about the region `0 ≤ d` excludes.

* At `d < 0` hypothesis (3) is not a weakened bound but an exclusion: a relative dimension is
  never negative, so (3) says that `T ⊆ V(I)` (`associatedSubset_subset_zeroLocus_of_neg`). The
  set `B` of the source is then empty, the candidate ideal cuts out `V(J)` exactly, and Claims I
  and II hold with nothing assumed.
* What is left is Claim III, and it is equivalent to the inequality Faltings' theorem asks for:
  `exists_isStabilizingData_iff_of_neg`. The `←` direction is Claim III; the `→` direction,
  `depth_add_dim_gt_of_isStabilizingData`, holds for every `d` and shows that the inequality is
  the content of the annihilation clause rather than an artifact of the route taken to it — the
  annihilating ideal `(J₀ I) ^ n` of the conclusion is supported in `T ∪ V(I)`, so the criterion
  Stacks 0EFC, an equivalence, returns the inequality.
* That inequality is what the counterexample refutes, which is how the two are connected: the
  conclusion of 0EFI for the data above would force it, and it fails there.

## Implementation notes

The general statement is for a module in the universe of the ring, because Stacks 0EFC is. The
`s ≤ 0` statement is universe-polymorphic in the module.

This is a separate module rather than an addition to
`StacksFrontier.AlgebraicGeometry.FormalGeometry.Stabilization`, where `IsStabilizingData` and
`localCohomologyComparison` live, because the comparison criterion Stacks 0DWV is stated in terms
of `Stacks.Algebraization.localCohomologyComparison` and therefore lives downstream of that file;
using it from inside it would be circular. That file is reached here through
`StacksFrontier.RingTheory.LocalCohomology.SupportInjectivity.Basic`, which carries Stacks 0DWV.

Four `import all` lines reach declarations that are `private` in the modules that prove them:
the localization of `Ext` and the bridge between the two models of localizing a derived complex
(`StacksFrontier.RingTheory.Dualizing.DualExtSupportDepthCriterion`), the injective-amplitude bounds
(`StacksFrontier.RingTheory.Dualizing.FiniteDimension`), the boundedness of a dimension function and
the Krull dimension of `(A/𝔭)_𝔮` as an interval (`...LocalCohomology.FaltingsAnnihilator`), and
the relative dimension as a height (`...FormalGeometry.StabilizationDepthCollapse`). This is the
pattern that module itself uses to reach `StacksFrontier.RingTheory.Dualizing.FiniteDimension`.

## References

* [Stacks Project, Tag 0EFI](https://stacks.math.columbia.edu/tag/0EFI)
* [Stacks Project, Tag 0EFC](https://stacks.math.columbia.edu/tag/0EFC)
* [Stacks Project, Tag 0ECM](https://stacks.math.columbia.edu/tag/0ECM)
* [Stacks Project, Tag 0DWV](https://stacks.math.columbia.edu/tag/0DWV)
* [Stacks Project, Tag 0DWY](https://stacks.math.columbia.edu/tag/0DWY)
-/
