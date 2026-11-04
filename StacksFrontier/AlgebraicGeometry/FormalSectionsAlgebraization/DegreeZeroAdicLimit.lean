module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiberRank.GenericPoint
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AssociatedPointSplittingConstruction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonShortExactMiddle
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSerreOneAlternativeProof
public import StacksFrontier.RingTheory.Depth.Criteria

/-!
# Formal sections on a punctured spectrum in degree zero: the adic limit at `s = 0`

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let `F` be a coherent module on
`U = Spec(A) ∖ V(𝔞)`, and let `s ≥ 0`. Stacks 0EG4 asserts, under its three numbered
hypotheses, that `H^i(U, F) ⟶ lim H^i(U, F/IⁿF)` is an isomorphism for `i < s`, and that

`colim_V H^s(V, F) ⟶ lim H^s(U, F/IⁿF)`

is an isomorphism, the colimit being over the opens `V ⊆ U` containing `U ∩ V(I)`.

This file proves the proposition **in the case `s = 0`**. There the first assertion is empty —
there is no `i` with `0 ≤ i < 0` — and the second reads

`colim_V H^0(V, F) ⟶ lim H^0(U, F/IⁿF)`,

which is exactly `Stacks.Algebraization.comparisonMap A I 𝔞 F`: its source is the colimit of
the sections of `F` over the opens `V ⊆ U` containing `U ∩ V(I)`, its target is the limit of the
sections of `F / Iⁿ F` over `U`. This is the case the source disposes of by citing Proposition
0EG2 ("we may assume `s > 0` as the case `s = 0` was done in Proposition 0EG2"), and that is the
route here: the library's Stacks 0EG2 is
`Stacks.Algebraization.isIso_comparisonMap`.

## Main definitions

* `Stacks.Algebraization.SourceSheafDepthHypothesis` — hypothesis (2) of Stacks 0EG4, written
  for the coherent module `F` on `U` and in the shape the source states it: at a point of
  `U ∖ V(I)` either the depth of the stalk exceeds `s`, or the depth plus
  `dim(𝒪_{closure {x}, z})` exceeds `cd(A, I) + s + 1` for every `z ∈ V(𝔞) ∩ closure {x}`.

## Main results

* `Stacks.Divisors.depth_stalk_eq_zero_of_isAssociatedPoint` — the stalk of a coherent module at
  an associated point has depth zero over the local ring there.
* `Stacks.Algebraization.associatedPointsClosureDimensionBound_of_sourceSheafDepthHypothesis` —
  hypothesis (2) of Stacks 0EG4 at `s = 0` implies condition (2) of Stacks 0EG2.
* `Stacks.Algebraization.isIso_comparisonMap_of_sourceSheafDepthHypothesis` —
  **Stacks 0EG4 for `s = 0`**.

## What this covers of Stacks 0EG4, and what it does not

Covered: the proposition at `s = 0`, i.e. the `colim`/`lim` assertion in degree `0`, which is
the clause the source takes from Proposition 0EG2.

The proposition in every degree `s`, with both of its assertions, is
`Stacks.Algebraization.adicLimit_allDegrees` of
`StacksFrontier/AlgebraicGeometry/FormalSectionsAlgebraization/AdicLimitTheorem.lean`, which does
not go through Proposition 0EG2.

Of the source's numbered hypotheses this file uses (1) in full and (2) at `s = 0`. Hypothesis
(3) is *not* used and does not appear as a binder: it is the condition Proposition 0EG2 removes
from Stacks 0EIF, and its removal is what the library's Stacks 0EG2 proves. That omission
strengthens the statement rather than weakens it.

## The inputs of Proposition 0EG2

All three hypotheses of the library's Stacks 0EG2 are supplied: the middle clause of Stacks 0H48
is `Stacks.Algebraization.middleComparisonOfShortExact`, the short exact sequence the source of
0EG2 assembles from Stacks 0BK0, 0DX3 and 0AW0 is `Stacks.Algebraization.associatedPointSplitting`,
and Stacks 0EIF is `Stacks.Algebraization.serreOneAlternativeComparison`.

## Implementation notes

Hypothesis (2) is written with `Module.depth` of the stalk rather than with
`AlgebraicGeometry.SheafHasDepthAt`, which is an equality `depth = k` and so cannot carry the
source's strict inequalities; the ring, the ideal and the module are the same three arguments
that `SheafHasDepthAt` supplies to `Module.depth`. The comparisons live in
`Stacks.Algebraization.enatToEInt` and `Stacks.Algebraization.krullDimToEInt`, the idiom
condition (2) of Stacks 0EIF already uses, and `dim(𝒪_{closure {x}, z})` is
`Stacks.Algebraization.closureLocalDimension`, as in that condition.

What turns hypothesis (2) at `s = 0` into condition (2) of Stacks 0EG2 is the depth-zero lemma:
at an associated point the maximal ideal of the local ring is the annihilator of a single
nonzero germ, so no element of it acts regularly on the stalk and
`Stacks.Depth.ModNonzerodivisor.exists_mem_isSMulRegular_of_depth_ne_zero` forces the depth to
vanish. The first alternative of hypothesis (2) is then unavailable at an associated point, and
the second becomes the bound of condition (2) of Stacks 0EG2 because the depth summand is zero.
Finiteness of the stalk, which that lemma needs, is
`AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent`.

Condition (2) of Stacks 0EG2 constrains fewer points than hypothesis (2) of Stacks 0EG4 does: it
speaks only of associated points, and only of those whose closure meets `V(I)` outside `V(𝔞)`.
Both restrictions are discarded here, the hypothesis being the source's.

The dualizing complex of condition (1) lives in the standard model of the derived category,
`CategoryTheory.HasDerivedCategory.standard`, which is made a local instance at a raised
priority. Another `HasDerivedCategory` instance, whose model has its morphisms one universe
lower, is reachable through these imports and wins at the default priority; the raised priority
is what keeps condition (1) in the same model as
`Stacks.Algebraization.BootstrapHypotheses`, which consumes it.

## References

* [Stacks Project, Tag 0EG4](https://stacks.math.columbia.edu/tag/0EG4)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
* [Stacks Project, Tag 00LL](https://stacks.math.columbia.edu/tag/00LL)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)

## Tags

local cohomology, algebraization, formal sections, adic completion, depth, associated points
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Divisors

/-- **The stalk of a coherent module at an associated point has depth zero.** At an associated
point the maximal ideal of the local ring is the annihilator of a single germ, which is then
nonzero because the maximal ideal is proper; so every element of the maximal ideal kills that
germ and none of them acts regularly on the stalk. -/
public theorem depth_stalk_eq_zero_of_isAssociatedPoint {X : Scheme.{u}} (F : X.Modules)
    [F.IsCoherent] (x : X) (hx : IsAssociatedPoint F x) :
    Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (F.presheaf.stalk x) = 0 := by
  have : Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent F x
  obtain ⟨hp, m, hm⟩ := hx
  by_contra hne
  obtain ⟨y, hy, hyreg⟩ :=
    Stacks.Depth.ModNonzerodivisor.exists_mem_isSMulRegular_of_depth_ne_zero _ hne
  rw [← hm] at hy
  have hym : y • m = 0 :=
    (Submodule.mem_bot _).mp (Submodule.mem_colon.mp hy m (Submodule.mem_span_singleton_self m))
  have hm0 : m = 0 := hyreg (show y • m = y • (0 : ToType (F.presheaf.stalk x)) by
    rw [hym, smul_zero]; rfl)
  refine hp.ne_top (hm ▸ eq_top_iff.mpr fun r _ => Submodule.mem_colon.mpr fun p hpm => ?_)
  rw [hm0, Submodule.span_zero_singleton] at hpm
  rw [(Submodule.mem_bot _).mp hpm, smul_zero]
  exact Submodule.zero_mem _

end Stacks.Divisors

namespace Stacks.Algebraization

open Stacks.LocalCohomology

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I a : Ideal A)
  (F : (complementZeroLocus A a : Scheme).Modules)

/-- **Hypothesis (2) of Stacks 0EG4**, for the coherent module `F` on `U = Spec(A) ∖ V(𝔞)` and in
the shape the source states it: for a point `x` of `U` outside `V(I)`, either the depth of the
stalk `F_x` exceeds `s`, or `depth(F_x) + dim(𝒪_{closure {x}, z}) > cd(A, I) + s + 1` for every
`z ∈ V(𝔞) ∩ closure {x}`.

The quantifier over `z` sits inside the disjunction, as in the source. -/
public def SourceSheafDepthHypothesis (s : ℤ) : Prop :=
  ∀ x : (complementZeroLocus A a : Scheme), ¬ I ≤ x.1.asIdeal →
    (enatToEInt (Module.depth ((complementZeroLocus A a : Scheme).presheaf.stalk x)
        (IsLocalRing.maximalIdeal ((complementZeroLocus A a : Scheme).presheaf.stalk x))
        (F.presheaf.stalk x)) > (s : EInt)) ∨
    (∀ z : PrimeSpectrum A, x.1.asIdeal ≤ z.asIdeal → a ≤ z.asIdeal →
      enatToEInt (Module.depth ((complementZeroLocus A a : Scheme).presheaf.stalk x)
            (IsLocalRing.maximalIdeal ((complementZeroLocus A a : Scheme).presheaf.stalk x))
            (F.presheaf.stalk x)) +
          krullDimToEInt (closureLocalDimension A x.1 z) >
        ((Stacks.LocalCohomology.cohomologicalDimension A I I.fg_of_isNoetherianRing + s + 1 :
          ℤ) : EInt))

/-- **Hypothesis (2) of Stacks 0EG4 at `s = 0` gives condition (2) of Stacks 0EG2.** At an
associated point of `F` off `V(I)` the depth of the stalk is zero, so the first alternative of
the hypothesis is unavailable and the second reads `dim(𝒪_{closure {x}, z}) > cd(A, I) + 1`,
which is the bound of `Stacks.Algebraization.AssociatedPointsClosureDimensionBound`. -/
public theorem associatedPointsClosureDimensionBound_of_sourceSheafDepthHypothesis
    [F.IsCoherent] (h : SourceSheafDepthHypothesis A I a F 0) :
    AssociatedPointsClosureDimensionBound A I a F := by
  intro x hxass hxI _ z hxz haz
  have hzero := Stacks.Divisors.depth_stalk_eq_zero_of_isAssociatedPoint F x hxass
  rcases h x hxI with hd | hd
  · rw [hzero] at hd
    exact absurd hd (by change ¬ ((0 : ℤ) : EInt) < ((0 : ℤ) : EInt); exact lt_irrefl _)
  · have hz := hd z hxz haz
    rw [hzero] at hz
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_lt_of_le hz (le_of_eq ?_))
    · exact congrArg (fun n : ℤ => ((n : ℤ) : EInt)) (by ring)
    · exact zero_add _

/-- **Stacks Project, Tag 0EG4 for `s = 0`.** Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A` and
let `F` be a coherent module on `U = Spec(A) ∖ V(𝔞)`. Assume `A` is `I`-adically complete and has
a dualizing complex, and assume hypothesis (2) of the source at `s = 0`. Then

`colim_V H^0(V, F) ⟶ lim H^0(U, F/IⁿF)`

is an isomorphism, the colimit being over the opens `V ⊆ U` containing `U ∩ V(I)`; that map is
`Stacks.Algebraization.comparisonMap A I 𝔞 F`.

This is the proposition's `colim`/`lim` assertion in degree `s = 0`, the first assertion being
empty for `s = 0`. It is the case the source disposes of by citing Proposition 0EG2, and the
proof is that citation: hypothesis (2) at `s = 0` gives condition (2) of 0EG2 because the depth
of a stalk at an associated point is zero. Hypothesis (3) of the source is absent, being the
condition 0EG2 removes. -/
@[stacks 0EG4 "the case s = 0: the first assertion is empty there and the colim/lim assertion \
in degree 0 is IsIso (comparisonMap A I a F), by Proposition 0EG2 as in the source. Hypotheses \
(1) and (2) of the source are present, (2) at s = 0 in the source's shape; hypothesis (3) is \
absent because 0EG2 removes it. Every s, with every conclusion, is \
Stacks.Algebraization.adicLimit_allDegrees in AdicLimitTheorem.lean"]
public theorem isIso_comparisonMap_of_sourceSheafDepthHypothesis [F.IsCoherent] (hIa : I ≤ a)
    (hcomplete : IsAdicComplete I A)
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K)
    (hdepth : SourceSheafDepthHypothesis A I a F 0) :
    IsIso (comparisonMap A I a F) :=
  isIso_comparisonMap A I a F
    ⟨hIa, hcomplete, hdual,
      associatedPointsClosureDimensionBound_of_sourceSheafDepthHypothesis A I a F hdepth⟩
    serreOneAlternativeComparison middleComparisonOfShortExact (associatedPointSplitting A I a)

end Stacks.Algebraization

end
