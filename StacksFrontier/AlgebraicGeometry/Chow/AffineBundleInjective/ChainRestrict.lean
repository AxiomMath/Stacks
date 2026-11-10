module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.MilnorChowLocalizationSequence

/-!
# Restricting locally finite Milnor K-chains to a set of points

Let `(S, δ)` be the base situation of chapter 42 and `p : X ⟶ S` locally of finite type. A
locally finite Milnor K-chain on `X` (Stacks 0GU2) is a locally finite family of Milnor K-classes
at the points of a fixed relative dimension. Keeping the classes at the points of a set `T` and
discarding the others is again such a chain. The differentials of Stacks 0GU9 have the following
support properties:

* the coefficient of the tame-symbol differential, and of the divisor differential of
  Stacks 0GU3, at a point `y` vanishes as soon as no point carrying the chain specializes to `y`;
* consequently, if no point carrying a chain specializes into `T`, both differentials of that
  chain restrict to zero on `T`.

## Main definitions

* `Stacks.Chow.milnorChainRestrict` — the restriction of a locally finite Milnor K-chain to a
  set of points.

## Main results

* `Stacks.Chow.pointwiseMilnorBoundary_apply_eq_zero_of_forall` and
  `Stacks.Chow.pointwiseDivisorDifferential_apply_eq_zero_of_forall` — the coefficient of a
  differential at a point no point of the support specializes to vanishes.
* `Stacks.Chow.milnorChainRestrict_pointwiseMilnorBoundary_eq_zero` and
  `Stacks.Chow.milnorChainRestrict_pointwiseDivisorDifferential_eq_zero` — the same, restricted
  to a set.

## References

* [Stacks Project, Tag 0GU2](https://stacks.math.columbia.edu/tag/0GU2)
* [Stacks Project, Tag 0GU3](https://stacks.math.columbia.edu/tag/0GU3)
* [Stacks Project, Tag 0GU9](https://stacks.math.columbia.edu/tag/0GU9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)

/-! ### Restriction to a set of points -/

open Classical in
/-- **The restriction of a locally finite Milnor K-chain to a set `T` of points**: the classes at
the points of `T` are kept and the others are replaced by zero. The support only shrinks, so the
family stays locally finite. -/
def milnorChainRestrict (T : Set X) (m : ℤ) (n : ℕ) :
    MilnorChainGroup C p m n →+ MilnorChainGroup C p m n where
  toFun a := ⟨fun x ↦ if (x : X) ∈ T then a.1 x else 0, fun U hU ↦ (a.2 U hU).subset (by
    rintro x ⟨hxU, hx⟩
    refine ⟨hxU, fun h ↦ hx ?_⟩
    simp [h])⟩
  map_zero' := Subtype.ext (funext fun x ↦ by simp)
  map_add' a b := Subtype.ext (funext fun x ↦ by
    change (if (x : X) ∈ T then a.1 x + b.1 x else 0) =
      (if (x : X) ∈ T then a.1 x else 0) + (if (x : X) ∈ T then b.1 x else 0)
    split_ifs <;> simp)

variable {C p}

/-- At a point of `T`, the restriction of a chain to `T` has the same class as the chain. -/
theorem milnorChainRestrict_apply_of_mem {T : Set X} {m : ℤ} {n : ℕ} (a : MilnorChainGroup C p m n)
    {x : pointsOfDimension C p m} (hx : (x : X) ∈ T) :
    (milnorChainRestrict C p T m n a).1 x = a.1 x := by
  classical
  change (if (x : X) ∈ T then a.1 x else 0) = a.1 x
  rw [ite_eq_left hx]

/-- At a point outside `T`, the restriction of a chain to `T` has class zero. -/
theorem milnorChainRestrict_apply_of_notMem {T : Set X} {m : ℤ} {n : ℕ}
    (a : MilnorChainGroup C p m n) {x : pointsOfDimension C p m} (hx : (x : X) ∉ T) :
    (milnorChainRestrict C p T m n a).1 x = 0 := by
  classical
  change (if (x : X) ∈ T then a.1 x else 0) = 0
  rw [ite_eq_right hx]

/-- Restricting twice is restricting to the intersection. -/
theorem milnorChainRestrict_milnorChainRestrict (T T' : Set X) (m : ℤ) (n : ℕ)
    (a : MilnorChainGroup C p m n) :
    milnorChainRestrict C p T m n (milnorChainRestrict C p T' m n a) =
      milnorChainRestrict C p (T ∩ T') m n a := by
  refine Subtype.ext (funext fun x ↦ ?_)
  by_cases hT : (x : X) ∈ T
  · by_cases hT' : (x : X) ∈ T'
    · rw [milnorChainRestrict_apply_of_mem _ hT, milnorChainRestrict_apply_of_mem _ hT',
        milnorChainRestrict_apply_of_mem (T := T ∩ T') _ ⟨hT, hT'⟩]
    · rw [milnorChainRestrict_apply_of_mem _ hT, milnorChainRestrict_apply_of_notMem _ hT',
        milnorChainRestrict_apply_of_notMem (T := T ∩ T') _ fun h ↦ hT' h.2]
  · rw [milnorChainRestrict_apply_of_notMem _ hT,
      milnorChainRestrict_apply_of_notMem (T := T ∩ T') _ fun h ↦ hT h.1]

/-- A chain all of whose points lie in `T` is its own restriction to `T`. -/
theorem milnorChainRestrict_eq_self {T : Set X} {m : ℤ} {n : ℕ} (a : MilnorChainGroup C p m n)
    (ha : ∀ x : pointsOfDimension C p m, a.1 x ≠ 0 → (x : X) ∈ T) :
    milnorChainRestrict C p T m n a = a := by
  refine Subtype.ext (funext fun x ↦ ?_)
  by_cases hx : (x : X) ∈ T
  · exact milnorChainRestrict_apply_of_mem _ hx
  · rw [milnorChainRestrict_apply_of_notMem _ hx]
    by_contra h
    exact hx (ha x (Ne.symm h))

/-- A chain none of whose points lie in `T` restricts to zero on `T`. -/
theorem milnorChainRestrict_eq_zero {T : Set X} {m : ℤ} {n : ℕ} (a : MilnorChainGroup C p m n)
    (ha : ∀ x : pointsOfDimension C p m, a.1 x ≠ 0 → (x : X) ∉ T) :
    milnorChainRestrict C p T m n a = 0 := by
  refine Subtype.ext (funext fun x ↦ ?_)
  by_cases hx : (x : X) ∈ T
  · rw [milnorChainRestrict_apply_of_mem _ hx]
    by_contra h
    exact ha x h hx
  · exact milnorChainRestrict_apply_of_notMem _ hx

/-- Two chains with the same restriction to `T` and to its complement are equal. -/
theorem eq_of_milnorChainRestrict_eq {T : Set X} {m : ℤ} {n : ℕ} {a b : MilnorChainGroup C p m n}
    (h : milnorChainRestrict C p T m n a = milnorChainRestrict C p T m n b)
    (h' : milnorChainRestrict C p Tᶜ m n a = milnorChainRestrict C p Tᶜ m n b) : a = b := by
  refine Subtype.ext (funext fun x ↦ ?_)
  by_cases hx : (x : X) ∈ T
  · have := congrArg (fun c : MilnorChainGroup C p m n ↦ c.1 x) h
    simpa [milnorChainRestrict_apply_of_mem _ hx] using this
  · have := congrArg (fun c : MilnorChainGroup C p m n ↦ c.1 x) h'
    simpa [milnorChainRestrict_apply_of_mem (T := Tᶜ) _ hx] using this

/-! ### Support of the two differentials -/

variable [LocallyOfFiniteType p]

/-- **The tame-symbol differential vanishes at a point no point of the chain specializes to.**
Each contribution to the coefficient at `x'` comes from a point carrying the chain and
specializing to `x'`. -/
theorem pointwiseMilnorBoundary_apply_eq_zero_of_forall (k : ℤ) (ξ : PointwiseKTwoGroup C p k)
    (x' : pointsOfDimension C p (k + 1))
    (h : ∀ x : pointsOfDimension C p (k + 2), ξ.1 x ≠ 0 → ¬ ((x : X) ⤳ (x' : X))) :
    (pointwiseMilnorBoundary C p k ξ).1 x' = 0 := by
  rw [pointwiseMilnorBoundary_apply, pointwiseMilnorBoundaryCoeff]
  refine (finsum_congr fun x ↦ ?_).trans finsum_zero
  by_cases hx : ξ.1 x = 0
  · exact pointwiseMilnorBoundaryTerm_of_eq_zero C p k ξ hx x'
  · exact pointwiseMilnorBoundaryTerm_of_not_specializes C p k ξ x x' (h x hx)

/-- A point at which the tame-symbol differential of a chain is nonzero is a specialization of a
point carrying the chain. -/
theorem exists_specializes_of_pointwiseMilnorBoundary_apply_ne_zero (k : ℤ)
    (ξ : PointwiseKTwoGroup C p k) {x' : pointsOfDimension C p (k + 1)}
    (h : (pointwiseMilnorBoundary C p k ξ).1 x' ≠ 0) :
    ∃ x : pointsOfDimension C p (k + 2), ξ.1 x ≠ 0 ∧ (x : X) ⤳ (x' : X) := by
  by_contra hcon
  exact h (pointwiseMilnorBoundary_apply_eq_zero_of_forall k ξ x' fun x hx hs ↦
    hcon ⟨x, hx, hs⟩)

/-- **The divisor differential vanishes at a point no point of the chain specializes to.** The
contribution of a point `x'` is the coefficient of a principal divisor on `closure {x'}`, which
vanishes off that closed set. -/
theorem pointwiseDivisorDifferential_apply_eq_zero_of_forall (k : ℤ)
    (a : PointwiseKOneGroup C p k) (y : pointsOfDimension C p k)
    (h : ∀ x : pointsOfDimension C p (k + 1), a.1 x ≠ 0 → ¬ ((x : X) ⤳ (y : X))) :
    (pointwiseDivisorDifferential C p k a).1 y = 0 := by
  apply (milnorKTheoryZeroAddEquiv (X.residueField y.1)).injective
  rw [pointwiseDivisorDifferential_apply_eq_finsum, map_zero]
  refine (finsum_congr fun x ↦ ?_).trans finsum_zero
  by_cases hx : a.1 x = 0
  · rw [hx, map_zero]
  · exact pointClosureOrd_eq_zero_of_notMem_closure C p x.1 (a.1 x)
      fun hy ↦ h x hx (specializes_iff_mem_closure.mpr hy)

/-- A point at which the divisor differential of a chain is nonzero is a specialization of a
point carrying the chain. -/
theorem exists_specializes_of_pointwiseDivisorDifferential_apply_ne_zero (k : ℤ)
    (a : PointwiseKOneGroup C p k) {y : pointsOfDimension C p k}
    (h : (pointwiseDivisorDifferential C p k a).1 y ≠ 0) :
    ∃ x : pointsOfDimension C p (k + 1), a.1 x ≠ 0 ∧ (x : X) ⤳ (y : X) := by
  by_contra hcon
  exact h (pointwiseDivisorDifferential_apply_eq_zero_of_forall k a y fun x hx hs ↦
    hcon ⟨x, hx, hs⟩)

/-- **If no point carrying a chain specializes into `T`, its tame-symbol differential restricts to
zero on `T`.** -/
theorem milnorChainRestrict_pointwiseMilnorBoundary_eq_zero {T : Set X} (k : ℤ)
    (ξ : PointwiseKTwoGroup C p k)
    (h : ∀ x : pointsOfDimension C p (k + 2), ξ.1 x ≠ 0 → ∀ y ∈ T, ¬ ((x : X) ⤳ y)) :
    milnorChainRestrict C p T (k + 1) 1 (pointwiseMilnorBoundary C p k ξ) = 0 :=
  milnorChainRestrict_eq_zero _ fun x' hx' hx'T ↦ by
    obtain ⟨x, hx, hs⟩ := exists_specializes_of_pointwiseMilnorBoundary_apply_ne_zero k ξ hx'
    exact h x hx _ hx'T hs

/-- **If no point carrying a chain specializes into `T`, its divisor differential restricts to
zero on `T`.** -/
theorem milnorChainRestrict_pointwiseDivisorDifferential_eq_zero {T : Set X} (k : ℤ)
    (a : PointwiseKOneGroup C p k)
    (h : ∀ x : pointsOfDimension C p (k + 1), a.1 x ≠ 0 → ∀ y ∈ T, ¬ ((x : X) ⤳ y)) :
    milnorChainRestrict C p T k 0 (pointwiseDivisorDifferential C p k a) = 0 :=
  milnorChainRestrict_eq_zero _ fun y hy hyT ↦ by
    obtain ⟨x, hx, hs⟩ := exists_specializes_of_pointwiseDivisorDifferential_apply_ne_zero k a hy
    exact h x hx _ hyT hs

end Stacks.Chow

end
