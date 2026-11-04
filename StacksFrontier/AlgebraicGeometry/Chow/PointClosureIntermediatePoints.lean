module

public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureQuotientStalk
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.PointwiseDivisorOrder

/-!
# The intermediate points of a specialization, indexed by relative dimension

Let `(S, δ)` be the base situation of chapter 42, let `p : X ⟶ S` be locally of finite type, let
`x` be a point of `X` of relative dimension `k + 2` and let `y` be a point of `X` of relative
dimension `k` with `x ⇝ y`. Write `W = closure {x}` for the integral closed subscheme spanned by
`x`, so that `x` is the generic point of `W` and `y` is a point `x''` of `W` whose local ring is
two-dimensional.

`Stacks.Chow.heightOnePrimeEquivIntermediatePoint` describes the height-one primes of
`𝒪_{W, x''}` as the points `x'` of `W` with `x ⇝ x' ⇝ x''`, both steps immediate specializations.
That description is in the internal vocabulary of `W`. The sums of Stacks 0GU9, on the other
hand, run over the points of `X` of relative dimension `k + 1`. This file is the translation
between the two indexings: a point of `W` is an immediate specialization of its generic point
exactly when, read in `X`, it has relative dimension `k + 1`; and it then specializes immediately
to `x''` because `𝒪_{W, x''}` is two-dimensional.

Consequently the locally finite sum, over the points of `X` of relative dimension `k + 1`, of the
contributions of the pairs `(x, x')` to the composite of the two differentials of Stacks 0GU9 is a
sum over the intermediate points of `W`, which is the index set of
`Stacks.Chow.sum_intermediatePointMilnorBoundaryOrder_eq_zero`. The case `x` does not specialize
to `y` is handled separately: there no point can be intermediate, and the sum is empty.

## What is carried

No further input is assumed. The δ-dimension computations rest on
`Stacks.Chow.relativeDimension_sub_eq_ringKrullDim_pointClosureStalk`, and so on the universal
catenarity and local Noetherianness of the base; both are part of
`Stacks.Chow.ChowSituation`, so nothing extra is assumed here.

**Nothing here asserts Stacks 0GUA**, and nothing here asserts that the three chain groups of
Stacks 0GU9 form a complex. What is proved is the index translation and the empty case; the
identification of the individual summands, and hence the vanishing of the composite, is not
proved here.

## Main definitions

* `Stacks.Chow.PointClosureIntermediatePoint` — the points of `closure {x}` lying immediately
  below its generic point and immediately above a given point of it.
* `Stacks.Chow.intermediatePointValue` — such a point, read as a point of `X`.
* `Stacks.Chow.intermediatePointOfDimension` — such a point, read as a point of `X` of relative
  dimension `k + 1`.

## Main results

* `Stacks.Chow.ringKrullDim_pointClosureStalk_eq_two_of_relativeDimension_sub_eq_two` — a drop of
  two in the relative dimension makes the local ring of `closure {x}` two-dimensional.
* `Stacks.Chow.coheight_pointClosurePoint_eq_one_of_relativeDimension_sub_eq_one`,
  `Stacks.Chow.coheight_pointClosurePoint_eq_two_of_relativeDimension_sub_eq_two` — the same
  drops read as coheights.
* `Stacks.Chow.relativeDimension_intermediatePoint` — an intermediate point of `closure {x}` has
  relative dimension `k + 1` when `x` has relative dimension `k + 2`.
* `Stacks.Chow.injective_intermediatePointOfDimension` — the translation is injective.
* `Stacks.Chow.exists_intermediatePointOfDimension_eq` — a point of relative dimension `k + 1`
  between `x` and `y` is an intermediate point of `closure {x}`.
* `Stacks.Chow.finsum_pointClosureOrdBoundaryTerm_eq_zero_of_not_specializes` — **the empty
  case**: when `x` does not specialize to `y` the composite contributes nothing at `y`.
* `Stacks.Chow.finsum_pointClosureOrdBoundaryTerm_eq_finsum_intermediatePoint` — **the index
  translation**: the sum over the points of relative dimension `k + 1` is the sum over the
  intermediate points of `closure {x}`.

## References

* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 0GU2](https://stacks.math.columbia.edu/tag/0GU2)
* [Stacks Project, Tag 0GU3](https://stacks.math.columbia.edu/tag/0GU3)
* [Stacks Project, Tag 0GU9](https://stacks.math.columbia.edu/tag/0GU9)
* [Stacks Project, Tag 0GUA](https://stacks.math.columbia.edu/tag/0GUA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]

/-! ### Reading a drop in the relative dimension as a dimension and as a coheight -/

/-- **A drop of two in the relative dimension makes the local ring two-dimensional.** This is
`Stacks.Chow.relativeDimension_sub_eq_ringKrullDim_pointClosureStalk` read in the direction the
proof of Stacks 0GU9 needs at a point of relative dimension `k`: the local ring of
`closure {x}` there is a two-dimensional Noetherian local domain, so the key algebraic lemma of
Stacks 0EAX applies to it. -/
theorem ringKrullDim_pointClosureStalk_eq_two_of_relativeDimension_sub_eq_two {x y : X}
    (hspec : x ⤳ y)
    (hdrop : relativeDimension C.dimensionFunction p x -
      relativeDimension C.dimensionFunction p y = 2) :
    ringKrullDim ((integralComponentAt x).subscheme.presheaf.stalk
      (pointClosurePoint x (specializes_iff_mem_closure.mp hspec))) = 2 := by
  obtain ⟨n, hdrop', hlocal⟩ := relativeDimension_drop_of_specialization
    C.isUniversallyCatenary C.dimensionFunction p hspec
  rw [hdrop] at hdrop'
  have hn : n = 2 := by omega
  rw [hn] at hlocal
  exact hlocal.trans (by norm_num)

/-- The coheight of a point of `closure {x}` is the Krull dimension of its local ring there. -/
private theorem coheight_pointClosurePoint_eq_of_ringKrullDim_stalk_eq {x y : X}
    (hy : y ∈ closure ({x} : Set X)) {n : ℕ∞}
    (h : ringKrullDim ((integralComponentAt x).subscheme.presheaf.stalk
      (pointClosurePoint x hy)) = (n : WithBot ℕ∞)) :
    Order.coheight (pointClosurePoint x hy) = n := by
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight] at h
  exact WithBot.coe_inj.mp h

/-- A drop of one in the relative dimension makes the point coheight one on `closure {x}`: the
Krull dimension of a local ring of a scheme is the coheight of the point (Stacks 02IZ). -/
theorem coheight_pointClosurePoint_eq_one_of_relativeDimension_sub_eq_one {x y : X}
    (hspec : x ⤳ y)
    (hdrop : relativeDimension C.dimensionFunction p x -
      relativeDimension C.dimensionFunction p y = 1) :
    Order.coheight (pointClosurePoint x (specializes_iff_mem_closure.mp hspec)) = 1 :=
  coheight_pointClosurePoint_eq_of_ringKrullDim_stalk_eq _
    ((ringKrullDim_pointClosureStalk_eq_one_of_relativeDimension_sub_eq_one C p hspec hdrop).trans
      (by norm_num))

/-- A drop of two in the relative dimension makes the point coheight two on `closure {x}`. -/
theorem coheight_pointClosurePoint_eq_two_of_relativeDimension_sub_eq_two {x y : X}
    (hspec : x ⤳ y)
    (hdrop : relativeDimension C.dimensionFunction p x -
      relativeDimension C.dimensionFunction p y = 2) :
    Order.coheight (pointClosurePoint x (specializes_iff_mem_closure.mp hspec)) = 2 :=
  coheight_pointClosurePoint_eq_of_ringKrullDim_stalk_eq _
    ((ringKrullDim_pointClosureStalk_eq_two_of_relativeDimension_sub_eq_two C p hspec hdrop).trans
      (by norm_num))

/-! ### The intermediate points of `closure {x}` -/

/-- **The intermediate points of a specialization inside `closure {x}`.** For a point `y` of the
closure of `x`, these are the points `x'` of `closure {x}` with `x ⇝ x' ⇝ y`, both steps
immediate specializations. This is the index set of
`Stacks.Chow.heightOnePrimeEquivIntermediatePoint` at the integral closed subscheme spanned by
`x`. -/
def PointClosureIntermediatePoint (x : X) {y : X} (hy : y ∈ closure ({x} : Set X)) : Type u :=
  {z : (integralComponentAt x).subscheme //
    IsImmediateSpecialization (genericPoint (integralComponentAt x).subscheme) z ∧
    IsImmediateSpecialization z (pointClosurePoint x hy)}

/-- An intermediate point of `closure {x}`, read as a point of `X`. -/
def intermediatePointValue {x : X} {y : X} (hy : y ∈ closure ({x} : Set X))
    (z : PointClosureIntermediatePoint x hy) : X :=
  (integralComponentAt x).subschemeι z.1

/-- An intermediate point of `closure {x}` lies in the closure of `x`: the range of the closed
immersion of `closure {x}` is that closure. -/
theorem intermediatePointValue_mem_closure {x : X} {y : X} (hy : y ∈ closure ({x} : Set X))
    (z : PointClosureIntermediatePoint x hy) :
    intermediatePointValue hy z ∈ closure ({x} : Set X) := by
  have hmem : intermediatePointValue hy z ∈
      Set.range (integralComponentAt x).subschemeι.base := ⟨z.1, rfl⟩
  rwa [(integralComponentAt x).range_subschemeι, coe_support_integralComponentAt x] at hmem

/-- The point `x` specializes to each intermediate point of its closure. -/
theorem specializes_intermediatePointValue {x : X} {y : X} (hy : y ∈ closure ({x} : Set X))
    (z : PointClosureIntermediatePoint x hy) : x ⤳ intermediatePointValue hy z :=
  specializes_iff_mem_closure.mpr (intermediatePointValue_mem_closure hy z)

/-- An intermediate point of `closure {x}` specializes to `y`: the closed immersion of
`closure {x}` is a topological embedding, so it carries the specialization inside the subscheme to
one in `X`. -/
theorem intermediatePointValue_specializes {x : X} {y : X} (hy : y ∈ closure ({x} : Set X))
    (z : PointClosureIntermediatePoint x hy) : intermediatePointValue hy z ⤳ y := by
  have h := (integralComponentAt x).subschemeι.isClosedEmbedding.isInducing.specializes_iff.mpr
    z.2.2.1
  rwa [subschemeι_pointClosurePoint x hy] at h

/-- **An intermediate point of `closure {x}` has relative dimension `k + 1`.** Its local ring on
`closure {x}` is one-dimensional, because it is an immediate specialization of the generic point,
so the relative dimension drops by exactly one from `x`. -/
theorem relativeDimension_intermediatePoint {k : ℤ} {x : X}
    (hx : relativeDimension C.dimensionFunction p x = k + 2) {y : X}
    (hy : y ∈ closure ({x} : Set X)) (z : PointClosureIntermediatePoint x hy) :
    relativeDimension C.dimensionFunction p (intermediatePointValue hy z) = k + 1 := by
  have hspec : x ⤳ intermediatePointValue hy z := specializes_intermediatePointValue hy z
  have hdim : ringKrullDim ((integralComponentAt x).subscheme.presheaf.stalk
      (pointClosurePoint x (specializes_iff_mem_closure.mp hspec))) = ((1 : ℕ) : ℕ∞) := by
    rw [show pointClosurePoint x (specializes_iff_mem_closure.mp hspec) = z.1 from rfl,
      ringKrullDim_stalk_intermediatePoint_eq_one z.2.1]
    norm_num
  have hdrop := relativeDimension_sub_eq_of_ringKrullDim_pointClosureStalk_eq
    C.isUniversallyCatenary C.dimensionFunction p hspec hdim
  rw [hx] at hdrop
  omega

/-- An intermediate point of `closure {x}`, read as a point of `X` of relative dimension
`k + 1`. This is the translation between the index set of
`Stacks.Chow.heightOnePrimeEquivIntermediatePoint` and the index set of the chain groups of
Stacks 0GU9. -/
def intermediatePointOfDimension {k : ℤ} {x : X}
    (hx : relativeDimension C.dimensionFunction p x = k + 2) {y : X}
    (hy : y ∈ closure ({x} : Set X)) (z : PointClosureIntermediatePoint x hy) :
    pointsOfDimension C p (k + 1) :=
  ⟨intermediatePointValue hy z,
    (mem_pointsOfDimension C p).mpr (relativeDimension_intermediatePoint C p hx hy z)⟩

/-- The underlying point of `X` of `intermediatePointOfDimension` is `intermediatePointValue`. -/
@[simp] theorem intermediatePointOfDimension_val {k : ℤ} {x : X}
    (hx : relativeDimension C.dimensionFunction p x = k + 2) {y : X}
    (hy : y ∈ closure ({x} : Set X)) (z : PointClosureIntermediatePoint x hy) :
    ((intermediatePointOfDimension C p hx hy z : pointsOfDimension C p (k + 1)) : X) =
      intermediatePointValue hy z := rfl

/-- **The translation is injective**: the closed immersion of `closure {x}` is injective on
points. -/
theorem injective_intermediatePointOfDimension {k : ℤ} {x : X}
    (hx : relativeDimension C.dimensionFunction p x = k + 2) {y : X}
    (hy : y ∈ closure ({x} : Set X)) :
    Function.Injective (intermediatePointOfDimension C p hx hy) := by
  intro z z' h
  refine Subtype.ext ?_
  have h' : (integralComponentAt x).subschemeι z.1 = (integralComponentAt x).subschemeι z'.1 :=
    congrArg (fun w : pointsOfDimension C p (k + 1) ↦ (w : X)) h
  exact (integralComponentAt x).subschemeι.isClosedEmbedding.injective h'

/-- **A point of relative dimension `k + 1` between `x` and `y` is an intermediate point of
`closure {x}`.** Its local ring on `closure {x}` is one-dimensional because the relative dimension
drops by one, hence it is an immediate specialization of the generic point `x`; and it then
specializes immediately to `y`, because a point strictly between it and the coheight-two point `y`
would give a chain of three generizations above `y`. -/
theorem exists_intermediatePointOfDimension_eq {k : ℤ} {x : X}
    (hx : relativeDimension C.dimensionFunction p x = k + 2) {y : X}
    (hy : y ∈ closure ({x} : Set X))
    (hyd : relativeDimension C.dimensionFunction p y = k)
    (x' : pointsOfDimension C p (k + 1)) (hxx' : x ⤳ (x'.1 : X))
    (hx'y : (x'.1 : X) ⤳ y) :
    ∃ z : PointClosureIntermediatePoint x hy,
      intermediatePointOfDimension C p hx hy z = x' := by
  have hmem : (x'.1 : X) ∈ closure ({x} : Set X) := specializes_iff_mem_closure.mp hxx'
  have hone : Order.coheight (pointClosurePoint x hmem) = 1 :=
    coheight_pointClosurePoint_eq_one_of_relativeDimension_sub_eq_one C p hxx'
      (by rw [hx, (mem_pointsOfDimension C p).mp x'.2]; ring)
  have htwo : Order.coheight (pointClosurePoint x hy) = 2 :=
    coheight_pointClosurePoint_eq_two_of_relativeDimension_sub_eq_two C p
      (specializes_iff_mem_closure.mpr hy) (by rw [hx, hyd]; ring)
  have hspec2 : (integralComponentAt x).subschemeι (pointClosurePoint x hmem) ⤳
      (integralComponentAt x).subschemeι (pointClosurePoint x hy) := by
    rw [subschemeι_pointClosurePoint x hmem, subschemeι_pointClosurePoint x hy]
    exact hx'y
  have hle : pointClosurePoint x hy ≤ pointClosurePoint x hmem :=
    Scheme.le_iff_specializes.mpr
      ((integralComponentAt x).subschemeι.isClosedEmbedding.isInducing.specializes_iff.mp hspec2)
  refine ⟨⟨pointClosurePoint x hmem,
    (coheight_eq_one_iff_isImmediateSpecialization_genericPoint _).mp hone,
    isImmediateSpecialization_of_coheight_eq_one_of_coheight_eq_two htwo hone hle⟩, ?_⟩
  exact Subtype.ext (subschemeι_pointClosurePoint x hmem)

/-! ### The sum of Stacks 0GU9 read over the intermediate points -/

/-- **The empty case of Stacks 0GU9.** If `x` does not specialize to `y`, then no point of `X`
both receives a tame-symbol boundary from `x` and carries a principal divisor meeting `y`, so the
contribution of `x` to the composite of the two differentials at `y` is zero. -/
theorem finsum_pointClosureOrdBoundaryTerm_eq_zero_of_not_specializes (k : ℤ)
    (ξ : PointwiseKTwoGroup C p k) {y : X} (x : pointsOfDimension C p (k + 2))
    (hxy : ¬ (x.1 : X) ⤳ y) :
    (∑ᶠ x' : pointsOfDimension C p (k + 1),
      pointClosureOrdBoundaryTerm C p k ξ y x x') = 0 := by
  refine Eq.trans (finsum_congr fun x' ↦ ?_) finsum_zero
  by_cases hxx' : (x.1 : X) ⤳ (x'.1 : X)
  · by_cases hx'y : y ∈ closure ({(x'.1 : X)} : Set X)
    · exact absurd (hxx'.trans (specializes_iff_mem_closure.mpr hx'y)) hxy
    · exact pointClosureOrdBoundaryTerm_of_notMem_closure C p k ξ x x' hx'y
  · exact pointClosureOrdBoundaryTerm_of_not_specializes C p k ξ y x x' hxx'

/-- **The index translation for Stacks 0GU9.** When `x` of relative dimension `k + 2` specializes
to `y` of relative dimension `k`, the contribution of `x` to the composite of the two
differentials at `y` is a sum over the intermediate points of `closure {x}`: a point of relative
dimension `k + 1` contributes only if it lies between `x` and `y`, and such a point is an
intermediate point of `closure {x}`.

This is the re-indexing which puts the sum on the index set of
`Stacks.Chow.sum_intermediatePointMilnorBoundaryOrder_eq_zero`. -/
theorem finsum_pointClosureOrdBoundaryTerm_eq_finsum_intermediatePoint (k : ℤ)
    (ξ : PointwiseKTwoGroup C p k) (x : pointsOfDimension C p (k + 2))
    (y : pointsOfDimension C p k) (hxy : (x.1 : X) ⤳ (y.1 : X)) :
    (∑ᶠ x' : pointsOfDimension C p (k + 1),
        pointClosureOrdBoundaryTerm C p k ξ y.1 x x') =
      ∑ᶠ z : PointClosureIntermediatePoint (x.1 : X) (specializes_iff_mem_closure.mp hxy),
        pointClosureOrdBoundaryTerm C p k ξ y.1 x
          (intermediatePointOfDimension C p ((mem_pointsOfDimension C p).mp x.2)
            (specializes_iff_mem_closure.mp hxy) z) := by
  set hy := specializes_iff_mem_closure.mp hxy
  set hx := (mem_pointsOfDimension C p).mp x.2
  have hsub : Function.support (fun x' : pointsOfDimension C p (k + 1) ↦
      pointClosureOrdBoundaryTerm C p k ξ y.1 x x') ⊆
      Set.range (intermediatePointOfDimension C p hx hy) := by
    intro x' hx'
    have hne : pointClosureOrdBoundaryTerm C p k ξ y.1 x x' ≠ 0 := hx'
    have hxx' : (x.1 : X) ⤳ (x'.1 : X) := by
      by_contra hnot
      exact hne (pointClosureOrdBoundaryTerm_of_not_specializes C p k ξ y.1 x x' hnot)
    have hx'y : (y.1 : X) ∈ closure ({(x'.1 : X)} : Set X) := by
      by_contra hnot
      exact hne (pointClosureOrdBoundaryTerm_of_notMem_closure C p k ξ x x' hnot)
    obtain ⟨z, hz⟩ := exists_intermediatePointOfDimension_eq C p hx hy
      ((mem_pointsOfDimension C p).mp y.2) x' hxx' (specializes_iff_mem_closure.mpr hx'y)
    exact ⟨z, hz⟩
  rw [finsum_eq_finsum_mem_of_support_subset hsub]
  exact finsum_mem_range (injective_intermediatePointOfDimension C p hx hy)

end Stacks.Chow

end
