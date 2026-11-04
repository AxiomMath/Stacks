module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.FittingIdealSheaf

/-!
# Finite stratification of a groupoid scheme

A groupoid scheme with finite source and target admits a decreasing sequence of invariant
closed subschemes whose locally closed rank strata exhaust its object scheme. On the stratum
numbered `r`, source is finite locally free of rank `r`.

## Main definitions

* `Stacks.Groupoids.finiteStratification` is the sequence of Fitting ideal sheaves of the
  direct image of the structure sheaf along source.

## Main results

* `Stacks.Groupoids.finiteStratification_zero` identifies the first term with the whole
  object scheme.
* `Stacks.Groupoids.finiteStratification_mono` gives the decreasing sequence of closed
  subschemes.
* `Stacks.Groupoids.finiteStratification_exhaustive` says their intersection is empty.

## Implementation notes

The closed subschemes are represented by the Fitting ideal sheaves of `s_* 𝒪_R`. Their order
is opposite to inclusion of subschemes, so the increasing chain of ideal sheaves recorded by
`finiteStratification_mono` is the decreasing chain of closed subschemes of the source. The
zeroth term vanishes because the identity arrows give a section of source, which makes
`𝒪_U` a direct summand of `s_* 𝒪_R`; this is the step the source records as
`U = Z_{-1} = Z_0`.

## References

* [Stacks Project, Tag 0AB9](https://stacks.math.columbia.edu/tag/0AB9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids

/-- The canonical Fitting stratification associated to source of a groupoid scheme. -/
@[stacks 0AB9 "the Fitting stratification"]
noncomputable def finiteStratification {S : Scheme.{u}} (G : GroupoidScheme S) (n : ℕ) :
    G.objects.left.IdealSheafData :=
  Fitting.idealSheaf (Morphisms.pushforwardStructureSheaf G.source.left) (n : ℤ)

/-- The identity arrows force the zeroth Fitting closed subscheme to be all objects. -/
@[stacks 0AB9 "the first closed subscheme"]
theorem finiteStratification_zero {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] :
    finiteStratification G 0 = ⊥ := by
  rw [finiteStratification, Nat.cast_zero]
  exact Fitting.idealSheaf_pushforward_zero _ G.identity.left (identity_left_comp_source_left G)

/-- The Fitting closed subschemes form a decreasing sequence. -/
@[stacks 0AB9 "decreasing closed subschemes"]
theorem finiteStratification_mono {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (n : ℕ) :
    finiteStratification G n ≤ finiteStratification G (n + 1) :=
  Fitting.idealSheaf_monotone _ (by push_cast; omega)

/-- No point lies in all Fitting closed subschemes. -/
@[stacks 0AB9 "empty intersection"]
theorem finiteStratification_exhaustive {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (x : G.objects.left) :
    ∃ n, x ∉ (finiteStratification G n).support :=
  Fitting.exists_notMem_support_idealSheaf_pushforward G.source.left x

end Stacks.Groupoids

end
