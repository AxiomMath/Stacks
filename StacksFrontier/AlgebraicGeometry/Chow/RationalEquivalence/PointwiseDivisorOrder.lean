module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.PointwiseMilnorBoundary

/-!
# The divisor differential of Stacks 0GU3 read coefficientwise as an order of vanishing

Let `(S, δ)` be the base situation of chapter 42 and `p : X ⟶ S` locally of finite type. The
divisor differential of Stacks 0GU3, `Stacks.Chow.pointwiseDivisorDifferential`, sends a locally
finite family of degree-one Milnor K-classes at the points of relative dimension `k + 1` to the
`k`-cycle which is the sum of the pushed-forward principal divisors. This file reads a single
coefficient of that cycle as a homomorphism out of one degree-one Milnor K-group.

Fix a point `x'` of `X` and a point `y` of `X`. A degree-one Milnor K-class at `x'` is a unit of
the residue field `κ(x')`, which is a nonzero rational function on the integral closed subscheme
`closure {x'}` (Stacks 01RV); pushing the principal divisor of that function forward to `X` and
reading its coefficient at `y` gives an integer, and the assignment is additive because the
principal divisor of a product is the sum of the principal divisors (Stacks 02RP). The resulting
`Stacks.Chow.pointClosureOrdHom` is the coefficient of the differential, one summand at a time:
`Stacks.Chow.pointwiseDivisorDifferential_apply_eq_finsum` expresses the degree-zero coordinate
of the differential at `y` as the locally finite sum of these over all `x'` of relative dimension
`k + 1`.

That shape is what the proof of Stacks 0GU9 needs. The composite of the divisor differential with
the tame-symbol differential of Stacks 0GU9,
`Stacks.Chow.pointwiseMilnorBoundary`, becomes a double locally finite sum, and the two sums may
be interchanged because their joint support is finite:
`Stacks.Chow.finsum_pointClosureOrdBoundaryTerm_comm`. Interchanging them
reduces the vanishing of the composite to one point `x` of relative dimension `k + 2` at a time,
which is `Stacks.Chow.pointwiseDivisorDifferential_comp_pointwiseMilnorBoundary_of_forall`. That
reduction is the source's "by additivity, since the sum is locally finite".

## What is carried

No further input is assumed. Everything below carries `[LocallyOfFiniteType p]`, the standing
hypothesis of chapter 42, which is what makes `closure {x}` locally Noetherian and so its
principal divisors defined.

## Main definitions

* `Stacks.Chow.pointClosureOrd`, `Stacks.Chow.pointClosureOrdHom` — the coefficient at `y` of the
  pushed-forward principal divisor on `closure {x'}` of the rational function attached to a
  degree-one Milnor K-class at `x'`, as an integer and as a homomorphism.

## Main results

* `Stacks.Chow.pointClosureOrd_eq_zero_of_notMem_closure` — the coefficient vanishes away from
  `closure {x'}`.
* `Stacks.Chow.pointwiseDivisorDifferential_apply_eq_finsum` — the degree-zero coordinate of the
  divisor differential at `y` is the locally finite sum of those coefficients.
* `Stacks.Chow.finite_support_pointClosureOrdBoundaryTerm` — the joint support of the double sum
  attached to the composite of the two differentials is finite.
* `Stacks.Chow.pointwiseDivisorDifferential_comp_pointwiseMilnorBoundary_of_forall` — **the
  reduction**: the composite vanishes as soon as it vanishes one point of relative dimension
  `k + 2` at a time.

## References

* [Stacks Project, Tag 01RV](https://stacks.math.columbia.edu/tag/01RV)
* [Stacks Project, Tag 02RP](https://stacks.math.columbia.edu/tag/02RP)
* [Stacks Project, Tag 0GU2](https://stacks.math.columbia.edu/tag/0GU2)
* [Stacks Project, Tag 0GU3](https://stacks.math.columbia.edu/tag/0GU3)
* [Stacks Project, Tag 0GU9](https://stacks.math.columbia.edu/tag/0GU9)
* [Stacks Project, Tag 0GUA](https://stacks.math.columbia.edu/tag/0GUA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]

/-! ### The coefficient of a principal divisor on the closure of a point -/

/-- The coefficient at `y` of the pushforward to `X` of the principal divisor, on the integral
closed subscheme `closure {x'}`, of the rational function whose value at `x'` is a given
degree-one Milnor K-class there. -/
def pointClosureOrd (x' : X) (u : MilnorKTheory (X.residueField x') 1) (y : X) : ℤ :=
  principalDivisorPushforward C p (integralComponentAt x') (isIntegral_integralComponentAt x')
    (integralComponentFunction x'
      (Additive.toMul (milnorKTheoryOneAddEquiv (X.residueField x') u))) y

/-- The zero class has coefficient zero: it is the constant rational function `1`, whose
principal divisor is the zero cycle. -/
@[simp]
theorem pointClosureOrd_zero (x' y : X) : pointClosureOrd C p x' 0 y = 0 := by
  rw [pointClosureOrd, show Additive.toMul
    (milnorKTheoryOneAddEquiv (X.residueField x') 0) = 1 by simp,
    integralComponentFunction_one, principalDivisorPushforward_one]
  rfl

/-- The coefficient is additive in the Milnor K-class: a sum of classes is a product of rational
functions, and the principal divisor of a product is the sum of the principal divisors. -/
theorem pointClosureOrd_add (x' : X) (u v : MilnorKTheory (X.residueField x') 1) (y : X) :
    pointClosureOrd C p x' (u + v) y =
      pointClosureOrd C p x' u y + pointClosureOrd C p x' v y := by
  rw [pointClosureOrd, pointClosureOrd, pointClosureOrd,
    show Additive.toMul (milnorKTheoryOneAddEquiv (X.residueField x') (u + v)) =
      Additive.toMul (milnorKTheoryOneAddEquiv (X.residueField x') u) *
        Additive.toMul (milnorKTheoryOneAddEquiv (X.residueField x') v) by
      rw [map_add]; rfl,
    integralComponentFunction_mul, principalDivisorPushforward_mul]
  rfl

/-- **The coefficient at `y` of the principal divisor on `closure {x'}`, as a homomorphism out of
the degree-one Milnor K-group at `x'`.** This is one summand of the coefficient at `y` of the
divisor differential of Stacks 0GU3. -/
def pointClosureOrdHom (x' y : X) : MilnorKTheory (X.residueField x') 1 →+ ℤ where
  toFun u := pointClosureOrd C p x' u y
  map_zero' := pointClosureOrd_zero C p x' y
  map_add' u v := pointClosureOrd_add C p x' u v y

/-- The homomorphism `pointClosureOrdHom C p x' y` sends a class `u` to
`pointClosureOrd C p x' u y`. -/
@[simp] theorem pointClosureOrdHom_apply (x' y : X)
    (u : MilnorKTheory (X.residueField x') 1) :
    pointClosureOrdHom C p x' y u = pointClosureOrd C p x' u y := rfl

/-- **Away from `closure {x'}` the coefficient vanishes.** The pushed-forward principal divisor
on `closure {x'}` is supported on that closed subscheme. -/
theorem pointClosureOrd_eq_zero_of_notMem_closure (x' : X)
    (u : MilnorKTheory (X.residueField x') 1) {y : X}
    (hy : y ∉ closure ({x'} : Set X)) : pointClosureOrd C p x' u y = 0 := by
  by_contra h
  refine hy ?_
  have hsub := support_principalDivisorPushforward_subset C p (integralComponentAt x')
    (isIntegral_integralComponentAt x')
    (integralComponentFunction x'
      (Additive.toMul (milnorKTheoryOneAddEquiv (X.residueField x') u)))
  rw [coe_support_integralComponentAt] at hsub
  exact hsub h

/-- The contribution of a point to the divisor of a pointwise Milnor K₁-chain is the coefficient
attached to the class of the chain there. -/
theorem pointwiseDivisorTerm_apply_eq_pointClosureOrd (k : ℤ) (a : PointwiseKOneGroup C p k)
    (x' : pointsOfDimension C p (k + 1)) (y : X) :
    pointwiseDivisorTerm C p k a x' y = pointClosureOrd C p x'.1 (a.1 x') y := rfl

/-- **The divisor differential of Stacks 0GU3 read coefficientwise.** The degree-zero coordinate
at `y` of the divisor differential applied to a chain `a` is the locally finite sum, over the
points `x'` of relative dimension `k + 1`, of the coefficients at `y` of the principal divisors
on `closure {x'}` of the classes of `a`. -/
theorem pointwiseDivisorDifferential_apply_eq_finsum (k : ℤ) (a : PointwiseKOneGroup C p k)
    (y : pointsOfDimension C p k) :
    milnorKTheoryZeroAddEquiv (X.residueField y.1)
        ((pointwiseDivisorDifferential C p k a).1 y) =
      ∑ᶠ x' : pointsOfDimension C p (k + 1),
        pointClosureOrdHom C p x'.1 y.1 (a.1 x') := by
  rw [show milnorKTheoryZeroAddEquiv (X.residueField y.1)
      ((pointwiseDivisorDifferential C p k a).1 y) = (pointwiseDivisorSum C p k a).1 y from
    pointwiseCycleEquiv_apply C p k (pointwiseDivisorSum C p k a) y,
    pointwiseDivisorSum_apply]
  exact finsum_congr fun x' ↦ pointwiseDivisorTerm_apply_eq_pointClosureOrd C p k a x' y.1

/-! ### The composite of the two differentials as a double locally finite sum -/

/-- A locally finite sum may be read over any set containing the support of its terms. -/
public theorem finsum_eq_finsum_mem_of_support_subset {ι M : Type*} [AddCommMonoid M]
    {f : ι → M} {s : Set ι} (h : Function.support f ⊆ s) :
    (∑ᶠ i : ι, f i) = ∑ᶠ i ∈ s, f i := by
  rw [finsum_mem_def, Set.indicator_eq_self.mpr h]

/-- The contribution of a pair of points to the composite of the two differentials of Stacks
0GU9 at a point `y`: the coefficient at `y` of the principal divisor on `closure {x'}` of the
tame-symbol boundary along `x ⇝ x'` of the class of the chain at `x`. -/
def pointClosureOrdBoundaryTerm (k : ℤ) (ξ : PointwiseKTwoGroup C p k) (y : X)
    (x : pointsOfDimension C p (k + 2)) (x' : pointsOfDimension C p (k + 1)) : ℤ :=
  pointClosureOrdHom C p x'.1 y (pointwiseMilnorBoundaryTerm C p k ξ x x')

/-- A pair whose first point does not specialize to the second contributes nothing. -/
theorem pointClosureOrdBoundaryTerm_of_not_specializes (k : ℤ) (ξ : PointwiseKTwoGroup C p k)
    (y : X) (x : pointsOfDimension C p (k + 2)) (x' : pointsOfDimension C p (k + 1))
    (hx : ¬ (x.1 : X) ⤳ (x'.1 : X)) :
    pointClosureOrdBoundaryTerm C p k ξ y x x' = 0 := by
  rw [pointClosureOrdBoundaryTerm,
    pointwiseMilnorBoundaryTerm_of_not_specializes C p k ξ x x' hx, map_zero]

/-- A pair whose second point does not specialize to `y` contributes nothing. -/
theorem pointClosureOrdBoundaryTerm_of_notMem_closure (k : ℤ) (ξ : PointwiseKTwoGroup C p k)
    {y : X} (x : pointsOfDimension C p (k + 2)) (x' : pointsOfDimension C p (k + 1))
    (hy : y ∉ closure ({(x'.1 : X)} : Set X)) :
    pointClosureOrdBoundaryTerm C p k ξ y x x' = 0 :=
  pointClosureOrd_eq_zero_of_notMem_closure C p x'.1 _ hy

/-- Where the chain vanishes, the pair contributes nothing. -/
theorem pointClosureOrdBoundaryTerm_of_eq_zero (k : ℤ) (ξ : PointwiseKTwoGroup C p k) (y : X)
    {x : pointsOfDimension C p (k + 2)} (hx : ξ.1 x = 0)
    (x' : pointsOfDimension C p (k + 1)) :
    pointClosureOrdBoundaryTerm C p k ξ y x x' = 0 := by
  rw [pointClosureOrdBoundaryTerm, pointwiseMilnorBoundaryTerm_of_eq_zero C p k ξ hx, map_zero]

/-- **The joint support of the double sum is finite.** An affine, hence quasi-compact, open
neighbourhood `U` of `y` contains only finitely many points of relative dimension `k + 2` at
which the chain is nonzero, and each of those contributes at only finitely many points of `U`;
and a contributing pair lies in `U × U`, because `y` lies in the closure of `x'` and `x'` in the
closure of `x`. -/
theorem finite_support_pointClosureOrdBoundaryTerm (k : ℤ) (ξ : PointwiseKTwoGroup C p k)
    (y : X) :
    (Function.support fun z : pointsOfDimension C p (k + 2) × pointsOfDimension C p (k + 1) ↦
      pointClosureOrdBoundaryTerm C p k ξ y z.1 z.2).Finite := by
  classical
  obtain ⟨_, ⟨U, hUaff, rfl⟩, hyU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hU : IsCompact (U : Set X) := hUaff.isCompact
  have hF : {x : pointsOfDimension C p (k + 2) | (x.1 : X) ∈ (U : Set X) ∧
      ξ.1 x ≠ 0}.Finite := ξ.2 U hU
  refine (hF.biUnion (fun x _ ↦ (finite_pointwiseMilnorBoundaryTerm_ne_zero C p k ξ x U hU).image
    (fun x' ↦ ((x, x') : pointsOfDimension C p (k + 2) × pointsOfDimension C p (k + 1))))).subset
    ?_
  rintro ⟨x, x'⟩ hz
  have hne : pointClosureOrdBoundaryTerm C p k ξ y x x' ≠ 0 := hz
  have hax : ξ.1 x ≠ 0 := fun h ↦ hne (pointClosureOrdBoundaryTerm_of_eq_zero C p k ξ y h x')
  have hspec : (x.1 : X) ⤳ (x'.1 : X) := by
    by_contra hnot
    exact hne (pointClosureOrdBoundaryTerm_of_not_specializes C p k ξ y x x' hnot)
  have hycl : y ∈ closure ({(x'.1 : X)} : Set X) := by
    by_contra hnot
    exact hne (pointClosureOrdBoundaryTerm_of_notMem_closure C p k ξ x x' hnot)
  have hx'U : (x'.1 : X) ∈ (U : Set X) :=
    (specializes_iff_mem_closure.mpr hycl).mem_open U.2 hyU
  have hxU : (x.1 : X) ∈ (U : Set X) := hspec.mem_open U.2 hx'U
  have hxmem : x ∈ {z : pointsOfDimension C p (k + 2) | (z.1 : X) ∈ (U : Set X) ∧
    ξ.1 z ≠ 0} := ⟨hxU, hax⟩
  refine Set.mem_biUnion hxmem ⟨x', ⟨hx'U, ?_⟩, rfl⟩
  exact fun h ↦ hne (by rw [pointClosureOrdBoundaryTerm, h, map_zero])

/-- **The coefficient of the composite is a double locally finite sum.** The coefficient at `x'`
of the tame-symbol differential of Stacks 0GU9 is a locally finite sum of local boundaries, and
the coefficient attached to `x'` is additive, so it distributes over that sum. -/
theorem pointClosureOrdHom_pointwiseMilnorBoundary_apply (k : ℤ)
    (ξ : PointwiseKTwoGroup C p k) (y : X) (x' : pointsOfDimension C p (k + 1)) :
    pointClosureOrdHom C p x'.1 y ((pointwiseMilnorBoundary C p k ξ).1 x') =
      ∑ᶠ x : pointsOfDimension C p (k + 2), pointClosureOrdBoundaryTerm C p k ξ y x x' := by
  rw [pointwiseMilnorBoundary_apply, pointwiseMilnorBoundaryCoeff]
  exact (pointClosureOrdHom C p x'.1 y).map_finsum
    (finite_support_pointwiseMilnorBoundaryTerm C p k ξ x')

/-- If a term vanishes outside `t` in its second variable, the sum over a set in its first
variable is supported in `t`. -/
private theorem support_finsum_mem_subset {ι κ M : Type*} [AddCommMonoid M] (s : Set ι)
    (f : ι → κ → M) {t : Set κ} (h : ∀ i j, f i j ≠ 0 → j ∈ t) :
    Function.support (fun j ↦ ∑ᶠ i ∈ s, f i j) ⊆ t := by
  intro j hj
  by_contra hnot
  exact hj (finsum_mem_eq_zero_of_forall_eq_zero fun i _ ↦ not_not.mp fun h' ↦ hnot (h i j h'))

/-- **The two sums of the composite may be interchanged.** Their joint support is finite, so both
iterated sums restrict to finite sets of indices and the interchange is the one for finite
sums. -/
theorem finsum_pointClosureOrdBoundaryTerm_comm (k : ℤ) (ξ : PointwiseKTwoGroup C p k) (y : X) :
    (∑ᶠ x' : pointsOfDimension C p (k + 1), ∑ᶠ x : pointsOfDimension C p (k + 2),
        pointClosureOrdBoundaryTerm C p k ξ y x x') =
      ∑ᶠ x : pointsOfDimension C p (k + 2), ∑ᶠ x' : pointsOfDimension C p (k + 1),
        pointClosureOrdBoundaryTerm C p k ξ y x x' := by
  classical
  set T := fun (x : pointsOfDimension C p (k + 2)) (x' : pointsOfDimension C p (k + 1)) ↦
    pointClosureOrdBoundaryTerm C p k ξ y x x' with hT
  have hP := finite_support_pointClosureOrdBoundaryTerm C p k ξ y
  set S : Set (pointsOfDimension C p (k + 2)) := Prod.fst '' Function.support
    (fun z : pointsOfDimension C p (k + 2) × pointsOfDimension C p (k + 1) ↦ T z.1 z.2) with hS
  set S' : Set (pointsOfDimension C p (k + 1)) := Prod.snd '' Function.support
    (fun z : pointsOfDimension C p (k + 2) × pointsOfDimension C p (k + 1) ↦ T z.1 z.2) with hS'
  have hSfin : S.Finite := hP.image _
  have hS'fin : S'.Finite := hP.image _
  have hmemS : ∀ x x', T x x' ≠ 0 → x ∈ S := fun x x' h ↦ ⟨(x, x'), h, rfl⟩
  have hmemS' : ∀ x x', T x x' ≠ 0 → x' ∈ S' := fun x x' h ↦ ⟨(x, x'), h, rfl⟩
  have hinnerx : ∀ x', (∑ᶠ x, T x x') = ∑ᶠ x ∈ S, T x x' := fun x' ↦
    finsum_eq_finsum_mem_of_support_subset fun x hx ↦ hmemS x x' hx
  have hinnerx' : ∀ x, (∑ᶠ x', T x x') = ∑ᶠ x' ∈ S', T x x' := fun x ↦
    finsum_eq_finsum_mem_of_support_subset fun x' hx' ↦ hmemS' x x' hx'
  have houterx' : Function.support (fun x' ↦ ∑ᶠ x ∈ S, T x x') ⊆ S' :=
    support_finsum_mem_subset S T fun x x' h ↦ hmemS' x x' h
  have houterx : Function.support (fun x ↦ ∑ᶠ x' ∈ S', T x x') ⊆ S :=
    support_finsum_mem_subset S' (fun x' x ↦ T x x') fun x' x h ↦ hmemS x x' h
  calc (∑ᶠ x' : pointsOfDimension C p (k + 1), ∑ᶠ x : pointsOfDimension C p (k + 2), T x x')
      = ∑ᶠ x' : pointsOfDimension C p (k + 1), ∑ᶠ x ∈ S, T x x' := finsum_congr hinnerx
    _ = ∑ᶠ x' ∈ S', ∑ᶠ x ∈ S, T x x' := finsum_eq_finsum_mem_of_support_subset houterx'
    _ = ∑ᶠ x ∈ S, ∑ᶠ x' ∈ S', T x x' := (finsum_mem_comm T hSfin hS'fin).symm
    _ = ∑ᶠ x : pointsOfDimension C p (k + 2), ∑ᶠ x' ∈ S', T x x' :=
        (finsum_eq_finsum_mem_of_support_subset houterx).symm
    _ = ∑ᶠ x : pointsOfDimension C p (k + 2), ∑ᶠ x' : pointsOfDimension C p (k + 1), T x x' :=
        finsum_congr fun x ↦ (hinnerx' x).symm

/-- **The reduction of Stacks 0GU9 to one point of relative dimension `k + 2` at a time.** The
composite of the tame-symbol differential of Stacks 0GU9 with the divisor differential of Stacks
0GU3 is the zero homomorphism as soon as, for every chain, every point `y` of relative dimension
`k` and every point `x` of relative dimension `k + 2`, the contributions of the pairs `(x, x')`
sum to zero.

This is the source's reduction "since the sum is locally finite, and by additivity, we may assume
`ξ = α_x` for a single point `x`". -/
theorem pointwiseDivisorDifferential_comp_pointwiseMilnorBoundary_of_forall (k : ℤ)
    (h : ∀ (ξ : PointwiseKTwoGroup C p k) (y : pointsOfDimension C p k)
      (x : pointsOfDimension C p (k + 2)),
      (∑ᶠ x' : pointsOfDimension C p (k + 1),
        pointClosureOrdBoundaryTerm C p k ξ y.1 x x') = 0) :
    (pointwiseDivisorDifferential C p k).comp (pointwiseMilnorBoundary C p k) = 0 := by
  refine AddMonoidHom.ext fun ξ ↦ Subtype.ext (funext fun y ↦ ?_)
  show (pointwiseDivisorDifferential C p k (pointwiseMilnorBoundary C p k ξ)).1 y = 0
  refine (milnorKTheoryZeroAddEquiv (X.residueField y.1)).injective ?_
  rw [pointwiseDivisorDifferential_apply_eq_finsum, map_zero,
    finsum_congr fun x' ↦ pointClosureOrdHom_pointwiseMilnorBoundary_apply C p k ξ y.1 x',
    finsum_pointClosureOrdBoundaryTerm_comm C p k ξ y.1,
    finsum_congr fun x ↦ h ξ y x]
  exact finsum_zero

end Stacks.Chow

end
