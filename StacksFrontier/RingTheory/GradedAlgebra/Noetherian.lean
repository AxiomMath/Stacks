module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.GradedAlgebra.Noetherian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Noetherian graded rings

Proof of Stacks Tag 00JW: a graded ring `A = ⨁_{d ≥ 0} 𝒜 d` is Noetherian if and only if its
degree-zero subring `𝒜 0` is Noetherian and its irrelevant ideal `𝒜₊ = ⨁_{d > 0} 𝒜 d` is
finitely generated as an ideal of `A`.

## Main results

* `Stacks.GradedAlgebra.NoetherianCriterion.solution`: the statement of Stacks Tag 00JW.

## Implementation notes

The forward implication is `GradedRing.GradeZero.isNoetherianRing` together with
`Ideal.fg_of_isNoetherianRing`.

For the converse, the source picks generators of `𝒜₊`, replaces them by their homogeneous
components, invokes Tag 07Z4 to see that they generate `A` as an `𝒜 0`-algebra, and concludes
by Tag 00FN. The last step is `Algebra.FiniteType.isNoetherianRing`. The first two are the
private lemmas of this file, none of which is in Mathlib:

* `proj_eq_self_of_mem`: a homogeneous element of degree `i` is its own degree-`i` component.
  Stated for an arbitrary index monoid, since nothing about `ℕ` enters it.
* `exists_finset_isHomogeneousElem_span_eq`: a finitely generated homogeneous ideal is spanned
  by a finite set of homogeneous elements — replace each of finitely many generators by its
  finitely many homogeneous components.
* `exists_pos_mem_of_mem_irrelevant`: a homogeneous element of `𝒜₊` is homogeneous of strictly
  positive degree. This is not vacuous bookkeeping: a homogeneous element of `𝒜₊` of degree `0`
  is `0`, and `0` lies in every `𝒜 n`, so nothing has to be said about the degree of the chosen
  generators beyond their being homogeneous.
* `mem_adjoin_of_irrelevant_le_span`: the strong induction on degree that carries the whole
  content of the half of Tag 07Z4 used here. If the generators have strictly positive degrees
  and their ideal contains `𝒜₊`, then a homogeneous `x` of degree `n > 0` is a combination
  `x = ∑ cₖ gₖ`, and taking degree-`n` components replaces `cₖ` by its component of degree
  `n - deg gₖ < n`. This is the one place where the degrees being `ℕ` rather than an arbitrary
  canonically ordered monoid is used, and it is used twice over: for the well-ordering that
  makes the induction legitimate and for the truncated subtraction `n - deg gₖ`.
* `adjoin_eq_top_of_span_eq_irrelevant`: the half of Tag 07Z4 that is used here, that a set of
  homogeneous elements spanning `𝒜₊` as an ideal of `A` generates `A` as an `𝒜 0`-algebra. It
  is the previous lemma read along the decomposition `A = ⨁_d 𝒜 d`. What Mathlib has nearby,
  `GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero`, is the analogous
  reduction to homogeneous generators for the *algebra* rather than for the irrelevant ideal,
  and so does not give this.

## References

* [Stacks Project, Tag 00JW](https://stacks.math.columbia.edu/tag/00JW)
* [Stacks Project, Tag 07Z4](https://stacks.math.columbia.edu/tag/07Z4)
* [Stacks Project, Tag 00FN](https://stacks.math.columbia.edu/tag/00FN)
-/

namespace Stacks.GradedAlgebra.NoetherianCriterion

open DirectSum

section Proj

variable {ι A σ : Type*} [DecidableEq ι] [AddMonoid ι] [Semiring A] [SetLike σ A]
  [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

/-- A homogeneous element of degree `i` is its own degree-`i` homogeneous component. -/
private theorem proj_eq_self_of_mem {i : ι} {x : A} (hx : x ∈ 𝒜 i) :
    GradedRing.proj 𝒜 i x = x := by
  rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_same 𝒜 hx]

end Proj

section Helpers

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜]

/-- A finitely generated homogeneous ideal of a graded ring is spanned by a finite set of
homogeneous elements: replace each of finitely many generators by its finitely many homogeneous
components. -/
private theorem exists_finset_isHomogeneousElem_span_eq {I : Ideal A}
    (hI : I.IsHomogeneous 𝒜) (hfg : I.FG) :
    ∃ s : Finset A, (∀ x ∈ s, SetLike.IsHomogeneousElem 𝒜 x) ∧
      Ideal.span (s : Set A) = I := by
  classical
  obtain ⟨t, ht⟩ := hfg
  -- the finite set of all homogeneous components of all the given generators
  obtain ⟨s, hmem⟩ : ∃ s : Finset A, ∀ y : A, y ∈ (s : Set A) ↔
      ∃ x ∈ t, ∃ i ∈ (decompose 𝒜 x).support, (decompose 𝒜 x i : A) = y :=
    ⟨t.biUnion fun x ↦ (decompose 𝒜 x).support.image fun i ↦ (decompose 𝒜 x i : A), by simp⟩
  refine ⟨s, ?_, le_antisymm ?_ ?_⟩
  · intro y hy
    obtain ⟨x, -, i, -, rfl⟩ := (hmem y).1 hy
    exact ⟨i, SetLike.coe_mem _⟩
  · rw [Ideal.span_le]
    intro y hy
    obtain ⟨x, hx, i, -, rfl⟩ := (hmem y).1 hy
    exact hI i (ht ▸ Ideal.subset_span hx)
  · rw [← ht, Ideal.span_le]
    intro x hx
    rw [SetLike.mem_coe, ← DirectSum.sum_support_decompose 𝒜 x]
    exact Ideal.sum_mem _ fun i hi ↦ Ideal.subset_span ((hmem _).2 ⟨x, hx, i, hi, rfl⟩)

/-- A homogeneous element of the irrelevant ideal `𝒜₊ = ⨁_{d > 0} 𝒜 d` is homogeneous of
strictly positive degree: a homogeneous element of `𝒜₊` of degree `0` is `0`, and `0` lies in
every `𝒜 n`. -/
@[ega "II 2.1.1" "partial"]
private theorem exists_pos_mem_of_mem_irrelevant {x : A}
    (hx : SetLike.IsHomogeneousElem 𝒜 x) (hirr : x ∈ HomogeneousIdeal.irrelevant 𝒜) :
    ∃ n, 0 < n ∧ x ∈ 𝒜 n := by
  obtain ⟨n, hn⟩ := hx
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [HomogeneousIdeal.mem_irrelevant_iff, proj_eq_self_of_mem 𝒜 hn] at hirr
    exact ⟨1, Nat.one_pos, hirr ▸ zero_mem _⟩
  · exact ⟨n, hpos, hn⟩

/-- The content of Stacks Tag 07Z4: if the elements of `s` are homogeneous of strictly positive
degree and the ideal they generate contains the irrelevant ideal `𝒜₊`, then every homogeneous
element of `A` lies in the `𝒜 0`-subalgebra generated by `s`.

Strong induction on the degree `n`: for `n > 0` the element lies in `𝒜₊`, hence is a
combination `x = ∑ cₖ gₖ` with `gₖ ∈ s`, and taking degree-`n` components replaces each
coefficient `cₖ` by its component of degree `n - deg gₖ`, which is smaller than `n` because
`deg gₖ > 0`. -/
@[ega "II 2.1.3" "necessity"]
private theorem mem_adjoin_of_irrelevant_le_span {s : Set A}
    (hs : ∀ x ∈ s, ∃ n, 0 < n ∧ x ∈ 𝒜 n)
    (hle : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span s)
    (n : ℕ) {x : A} (hx : x ∈ 𝒜 n) :
    x ∈ Algebra.adjoin ↥(𝒜 0) s := by
  induction n using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Subalgebra.algebraMap_mem _ (⟨x, hx⟩ : ↥(𝒜 0))
    · have hxs : x ∈ Ideal.span s :=
        hle (HomogeneousIdeal.mem_iff.mpr (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn hx))
      rw [← Ideal.submodule_span_eq, Submodule.mem_span_set'] at hxs
      obtain ⟨m, c, g, hsum⟩ := hxs
      rw [← proj_eq_self_of_mem 𝒜 hx, ← hsum, map_sum]
      refine Subalgebra.sum_mem _ fun k _ ↦ ?_
      obtain ⟨d, hd, hgd⟩ := hs (g k) (g k).2
      rw [smul_eq_mul, GradedRing.proj_apply, DirectSum.coe_decompose_mul_of_right_mem 𝒜 n hgd]
      split_ifs with hdn
      · exact Subalgebra.mul_mem _ (ih (n - d) (by omega) (SetLike.coe_mem _))
          (Algebra.subset_adjoin (g k).2)
      · exact Subalgebra.zero_mem _

/-- Half of Stacks Tag 07Z4: a set of homogeneous elements spanning the irrelevant ideal
`𝒜₊ = ⨁_{d > 0} 𝒜 d` as an ideal of `A` generates `A` as an algebra over the degree-zero
subring `𝒜 0`. -/
private theorem adjoin_eq_top_of_span_eq_irrelevant {s : Set A}
    (hs : ∀ x ∈ s, SetLike.IsHomogeneousElem 𝒜 x)
    (hspan : Ideal.span s = (HomogeneousIdeal.irrelevant 𝒜).toIdeal) :
    Algebra.adjoin ↥(𝒜 0) s = ⊤ := by
  have hpos : ∀ x ∈ s, ∃ n, 0 < n ∧ x ∈ 𝒜 n := fun x hx ↦
    exists_pos_mem_of_mem_irrelevant 𝒜 (hs x hx)
      (HomogeneousIdeal.mem_iff.mp (hspan ▸ Ideal.subset_span hx))
  rw [eq_top_iff]
  rintro x -
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => exact Subalgebra.zero_mem _
  | homogeneous m => exact mem_adjoin_of_irrelevant_le_span 𝒜 hpos hspan.ge _ m.2
  | add x y hx hy => exact Subalgebra.add_mem _ hx hy

end Helpers

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]

/-- Stacks Tag 00JW: a graded ring `A = ⨁_d 𝒜 d` is Noetherian if and only if `𝒜 0` is a
Noetherian ring and the irrelevant ideal of `A` is finitely generated. -/
@[ega "II 2.1.5" "necessity"]
public theorem solution (𝒜 : ℕ → σ) [GradedRing 𝒜] :
    IsNoetherianRing A ↔
      IsNoetherianRing (𝒜 0) ∧ (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG := by
  refine ⟨fun _ ↦ ⟨inferInstance, Ideal.fg_of_isNoetherianRing _⟩, fun ⟨h0, hfg⟩ ↦ ?_⟩
  obtain ⟨s, hs, hspan⟩ :=
    exists_finset_isHomogeneousElem_span_eq 𝒜 (HomogeneousIdeal.irrelevant 𝒜).isHomogeneous hfg
  have : Algebra.FiniteType ↥(𝒜 0) A :=
    ⟨s, adjoin_eq_top_of_span_eq_irrelevant 𝒜 (by simpa using hs) hspan⟩
  exact Algebra.FiniteType.isNoetherianRing ↥(𝒜 0) A

end Stacks.GradedAlgebra.NoetherianCriterion

/-!
# Noetherian graded rings

Let `S = ⨁_{d ≥ 0} S_d` be a graded ring, `S₀` its degree-zero subring and
`S₊ = ⨁_{d ≥ 1} S_d` its irrelevant ideal. Then `S` is Noetherian if and only if `S₀` is a
Noetherian ring and `S₊` is finitely generated as an ideal of `S`.

Both directions are elementary. If `S` is Noetherian then `S₀ = S/S₊` is Noetherian and every
ideal of `S`, in particular `S₊`, is finitely generated. Conversely, generators of `S₊` may be
replaced by their homogeneous components, so `S₊` is generated by finitely many homogeneous
elements `f₁, …, fₙ` of positive degree; such a family generates `S` as an `S₀`-algebra
[StackProject 07Z4], so `S₀[X₁, …, Xₙ] → S`, `Xᵢ ↦ fᵢ`, is surjective and `S` is Noetherian
because a quotient of a polynomial ring in finitely many variables over a Noetherian ring
is Noetherian [StackProject 00FN].

## Main results

* `GradedRing.isNoetherianRing_iff_isNoetherianRing_gradeZero_and_irrelevant_fg`: a graded ring
  is Noetherian if and only if its degree-zero part is a Noetherian ring and its irrelevant
  ideal is finitely generated.

## Implementation notes

A graded ring is a commutative ring `A` together with an internal `ℕ`-grading `𝒜 : ℕ → σ`
satisfying `GradedRing 𝒜`, following Mathlib and the source's convention that the degrees of a
graded ring are the non-negative integers: `S₀` is the degree-zero subring `↥(𝒜 0)` and `S₊` is
`HomogeneousIdeal.irrelevant 𝒜`, the kernel of the projection onto the degree-zero component,
i.e. `⨁_{d > 0} 𝒜 d`. The grading takes values in additive *subgroups* of `A`; this is no
restriction on the mathematics, since the additive decomposition `A ≃+ ⨁_d 𝒜 d` forces every
`𝒜 d` to be closed under negation, but it is what makes `↥(𝒜 0)` a ring rather than only
a semiring, so that `IsNoetherianRing ↥(𝒜 0)` is the source's condition on `S₀` —
Noetherianness for the honest ideals of `S₀`, not the a priori different condition on its
subsemimodules.

The degrees are `ℕ` rather than an arbitrary canonically ordered monoid `ι`. The implication from
left to right holds for every such `ι` (`GradedRing.GradeZero.isNoetherianRing` together with
`Ideal.fg_of_isNoetherianRing`); the other implication uses that a nonzero degree can be lowered
only finitely often, which is the well-ordering of `ℕ`.

Faithfulness. (1) The only hypothesis is the graded ring structure `GradedRing 𝒜`, and both
sides of the equivalence are about it: it is what makes `𝒜 0` a ring and
`HomogeneousIdeal.irrelevant 𝒜` an ideal. (2) The base is the source's: `𝒜 0` is a subring of
`A` itself, and `S₊` is finitely generated *as an ideal of `A`* (`Ideal.FG`, i.e. generated by
a finite subset under multiplication by all of `A`), not as an `𝒜 0`-module and not in a
quotient of `A`. (3) The source names no map; the two objects it names are pinned rather than
asserted to exist, as `𝒜 0` and as `HomogeneousIdeal.irrelevant 𝒜`. (4) The instantiation is
not degenerate in either direction: for `A = k[X]` graded by degree both sides hold, with
`𝒜 0 = k` and `S₊ = (X)`, while for a polynomial ring on infinitely many variables over a
field the degree-zero part is still the Noetherian ring `k` and both `IsNoetherianRing A` and
finite generation of `S₊` fail.

## References

* [StackProject 00JW](https://stacks.math.columbia.edu/tag/00JW)
-/

namespace GradedRing

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]

/-- A graded ring `A = ⨁_d 𝒜 d` is Noetherian if and only if its degree-zero subring `𝒜 0`
is a Noetherian ring and its irrelevant ideal `⨁_{d > 0} 𝒜 d` is finitely generated as an
ideal of `A`. -/
@[stacks 00JW, ega "II 2.1.5" "necessity"]
public theorem isNoetherianRing_iff_isNoetherianRing_gradeZero_and_irrelevant_fg
    (𝒜 : ℕ → σ) [GradedRing 𝒜] :
    IsNoetherianRing A ↔
      IsNoetherianRing (𝒜 0) ∧ (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG :=
    by apply Stacks.GradedAlgebra.NoetherianCriterion.solution

end GradedRing
