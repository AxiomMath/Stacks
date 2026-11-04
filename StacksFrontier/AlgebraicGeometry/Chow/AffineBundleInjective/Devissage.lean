module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundleInjective.BundleCyclePullback
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundleInjective.FibreStatements

/-!
# The dévissage of a Milnor K₁-chain along an affine-space bundle

Let `(S, δ)` be the base situation of chapter 42 and `f : X ⟶ Y` an affine-space bundle of rank
`r` between schemes locally of finite type over `S`. Let `a` be a locally finite Milnor K₁-chain
on `X` whose divisor has no component on the fibres over the points `y` with
`δ(y) ≠ k + 1 - r`. Assuming the boundary-lifting property `Stacks.Chow.FibreBoundaryLift` of all
fibres, this file modifies `a` by tame-symbol boundaries, which does not change its divisor, until
it lives at the generic points of the fibres over the points of relative dimension `k + 1 - r`.

The modification proceeds one level at a time. If every point carrying `a` lies over a point of
relative dimension at most `N`, with `N ≠ k + 1 - r`, then over each point `y` with `δ(y) = N` the
piece of `a` on the fibre over `y` is the boundary, on that fibre, of a K₂-chain supported there;
the locally finite sum of those K₂-chains is subtracted from `a` through its boundary, and what
remains lies over points of relative dimension at most `N - 1`. Nothing new appears over the
level `N`, because a point of relative dimension `N` has no proper generization of relative
dimension `≤ N`.

This is the source's Step 2 of Stacks 0GUB carried out on chains rather than on the six-term
sequences of Stacks 0GUA, the role of the dense open over which the bundle is trivial being played
by the generic points of the closed subsets of `Y`. Combined with the unit-descent property
`Stacks.Chow.FibreUnitDescent` of the fibres, the chain that remains is a pullback from `Y`, which
gives the injectivity of flat pullback on Chow groups.

## Main definitions

* `Stacks.Chow.FibreFamily` and `Stacks.Chow.FibreFamily.sum` — a family of chains supported on
  distinct fibres, and its locally finite sum.

## Main results

* `Stacks.Chow.exists_devissage_step` — one level of the dévissage.
* `Stacks.Chow.exists_devissage` — the whole dévissage.
* `Stacks.Chow.flatPullbackChow_injective_of_fibreProperties` — injectivity of
  `f^* : A_k(Y) ⟶ A_{k+r}(X)` from the fibrewise properties.

## References

* [Stacks Project, Tag 0GUA](https://stacks.math.columbia.edu/tag/0GUA)
* [Stacks Project, Tag 0GUB](https://stacks.math.columbia.edu/tag/0GUB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Sums of chains supported on distinct fibres -/

section FamilySum

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) (f : X ⟶ Y)

/-- A family of chains, one supported on the fibre over each point of `Y`, only finitely many
nonzero over every quasi-compact open: the data of a locally finite sum of chains on distinct
fibres. -/
structure FibreFamily (m : ℤ) (n : ℕ) where
  /-- The chain over each point. -/
  chain : Y → MilnorChainGroup C sX m n
  supported : ∀ (y : Y) (w : pointsOfDimension C sX m), (chain y).1 w ≠ 0 → f.base w.1 = y
  finite : ∀ W : Y.Opens, IsCompact (W : Set Y) → {y : Y | y ∈ W ∧ chain y ≠ 0}.Finite

variable {C sX f}

/-- At a point lying over `y`, the restriction to the fibre over `y` does not change the value. -/
private theorem fibreRestrict_apply_of_base_eq {m : ℤ} {n : ℕ} (a : MilnorChainGroup C sX m n)
    {y : Y} {w : pointsOfDimension C sX m} (h : f.base w.1 = y) :
    (fibreRestrict C sX f y m n a).1 w = a.1 w :=
  milnorChainRestrict_apply_of_mem _ (show w.1 ∈ f.base ⁻¹' {y} from h)

/-- At a point not lying over `y`, the restriction to the fibre over `y` has value zero. -/
private theorem fibreRestrict_apply_of_base_ne {m : ℤ} {n : ℕ} (a : MilnorChainGroup C sX m n)
    {y : Y} {w : pointsOfDimension C sX m} (h : f.base w.1 ≠ y) :
    (fibreRestrict C sX f y m n a).1 w = 0 :=
  milnorChainRestrict_apply_of_notMem _ (show w.1 ∉ f.base ⁻¹' {y} from h)

/-- The locally finite sum of a family of chains supported on distinct fibres: at a point `w`
it is the value of the chain over `f w`. -/
def FibreFamily.sum {m : ℤ} {n : ℕ} (F : FibreFamily C sX f m n) : MilnorChainGroup C sX m n :=
  ⟨fun w ↦ (F.chain (f.base w.1)).1 w, fun U hU ↦ by
    obtain ⟨V, hV, hUV⟩ := exists_isCompact_opens_superset (hU.image f.continuous)
    refine ((F.finite V hV).biUnion fun y _ ↦ (F.chain y).2 U hU).subset ?_
    rintro w ⟨hwU, hw⟩
    refine Set.mem_biUnion (x := f.base w.1) ⟨hUV ⟨w.1, hwU, rfl⟩, fun h ↦ hw ?_⟩ ⟨hwU, hw⟩
    change (F.chain (f.base w.1)).1 w = 0
    rw [h]
    rfl⟩

/-- The value of the sum at a point `w` is the value at `w` of the chain over `f w`. -/
theorem FibreFamily.sum_apply {m : ℤ} {n : ℕ} (F : FibreFamily C sX f m n)
    (w : pointsOfDimension C sX m) : F.sum.1 w = (F.chain (f.base w.1)).1 w := rfl

/-- On the fibre over `y` the sum is the chain over `y`. -/
theorem fibreRestrict_fibreFamily_sum {m : ℤ} {n : ℕ} (F : FibreFamily C sX f m n) (y : Y) :
    fibreRestrict C sX f y m n F.sum = F.chain y := by
  refine Subtype.ext (funext fun w ↦ ?_)
  by_cases hw : f.base w.1 = y
  · rw [fibreRestrict_apply_of_base_eq _ hw, FibreFamily.sum_apply, hw]
  · rw [fibreRestrict_apply_of_base_ne _ hw]
    by_contra h
    exact hw (F.supported y w (Ne.symm h))

/-- Away from the fibre over `y`, the sum is supported over the other points carrying the
family. -/
theorem fibreFamily_sum_sub_apply_ne_zero {m : ℤ} {n : ℕ} (F : FibreFamily C sX f m n) (y : Y)
    {w : pointsOfDimension C sX m} (h : (F.sum - F.chain y).1 w ≠ 0) :
    f.base w.1 ≠ y ∧ F.chain (f.base w.1) ≠ 0 := by
  have hval : (F.sum - F.chain y).1 w = (F.chain (f.base w.1)).1 w - (F.chain y).1 w := rfl
  by_cases hw : f.base w.1 = y
  · refine absurd ?_ h
    rw [hval, hw, sub_self]
  · refine ⟨hw, fun h0 ↦ h ?_⟩
    have hy : (F.chain y).1 w = 0 := by
      by_contra hne
      exact hw (F.supported y w hne)
    rw [hval, h0, hy]
    simp

/-- A chain whose restriction to the fibre over `y` is nonzero is carried by a point over `y`. -/
theorem exists_base_eq_of_fibreRestrict_ne_zero {m : ℤ} {n : ℕ} {a : MilnorChainGroup C sX m n}
    {y : Y} (h : fibreRestrict C sX f y m n a ≠ 0) :
    ∃ ξ : pointsOfDimension C sX m, f.base ξ.1 = y ∧ a.1 ξ ≠ 0 := by
  obtain ⟨ξ, hξ⟩ : ∃ ξ, (fibreRestrict C sX f y m n a).1 ξ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact h (Subtype.ext (funext hall))
  have hξy : f.base ξ.1 = y := by
    by_contra hne
    exact hξ (fibreRestrict_apply_of_base_ne _ hne)
  refine ⟨ξ, hξy, fun h0 ↦ hξ ?_⟩
  rw [fibreRestrict_apply_of_base_eq _ hξy, h0]

/-- Along a quasi-compact morphism, the image of the support of a locally finite chain meets
every quasi-compact open in a finite set. -/
theorem finite_inter_image_support [QuasiCompact f] {m : ℤ} {n : ℕ}
    (a : MilnorChainGroup C sX m n) (W : Y.Opens) (hW : IsCompact (W : Set Y)) :
    {y : Y | y ∈ W ∧ ∃ ξ : pointsOfDimension C sX m, f.base ξ.1 = y ∧ a.1 ξ ≠ 0}.Finite := by
  obtain ⟨V, hV, hWV⟩ := exists_isCompact_opens_superset
    (QuasiCompact.isCompact_preimage (f := f) _ W.2 hW)
  refine ((a.2 V hV).image fun ξ : pointsOfDimension C sX m ↦ f.base ξ.1).subset ?_
  rintro y ⟨hyW, ξ, rfl, hξ⟩
  exact ⟨ξ, ⟨hWV (show ξ.1 ∈ f.base ⁻¹' (W : Set Y) from hyW), hξ⟩, rfl⟩

end FamilySum

/-! ### One level of the dévissage -/

section Step

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) (hbase : f ≫ sY = sX) {r : ℕ}
  (hb : IsAffineSpaceBundle f r)

include hbase hb in
/-- Relative dimension does not drop along an affine-space bundle. -/
theorem relativeDimension_le_of_isAffineSpaceBundle (x : X) :
    relativeDimension C.dimensionFunction sY (f.base x) ≤
      relativeDimension C.dimensionFunction sX x := by
  have := locallyOfFiniteType_of_isAffineSpaceBundle f r hb
  subst hbase
  rw [relativeDimension_comp_eq_add_trdeg C.dimensionFunction sY f x]
  omega

omit [LocallyOfFiniteType sX] in
/-- **A point of `Y` has no proper generization of relative dimension at most its own.** -/
theorem eq_of_specializes_of_relativeDimension_le {y y' : Y} (h : y ⤳ y')
    (hle : relativeDimension C.dimensionFunction sY y ≤
      relativeDimension C.dimensionFunction sY y') : y = y' := by
  by_contra hne
  have := relativeDimension_lt_of_specializes C sY h hne
  omega

/-- **The divisor of the piece of a chain on a fibre.** If every point carrying the K₁-chain `a`
lies over a point of relative dimension at most that of `y`, and the divisor of `a` has no
component on the fibre over `y`, then neither has the divisor of the piece of `a` on that
fibre. -/
theorem fibreRestrict_divisor_fibreRestrict_eq_zero_of_relativeDimension_le {y : Y} (k : ℤ)
    (a : PointwiseKOneGroup C sX k)
    (ha : ∀ ξ : pointsOfDimension C sX (k + 1), a.1 ξ ≠ 0 →
      relativeDimension C.dimensionFunction sY (f.base ξ.1) ≤
        relativeDimension C.dimensionFunction sY y)
    (hdiv : fibreRestrict C sX f y k 0 (pointwiseDivisorDifferential C sX k a) = 0) :
    fibreRestrict C sX f y k 0 (pointwiseDivisorDifferential C sX k
      (fibreRestrict C sX f y (k + 1) 1 a)) = 0 := by
  have hrest : fibreRestrict C sX f y k 0 (pointwiseDivisorDifferential C sX k
      (a - fibreRestrict C sX f y (k + 1) 1 a)) = 0 := by
    refine milnorChainRestrict_pointwiseDivisorDifferential_eq_zero k _ ?_
    intro ξ hξ y' hy' hspec
    have hval : (a - fibreRestrict C sX f y (k + 1) 1 a).1 ξ =
        a.1 ξ - (fibreRestrict C sX f y (k + 1) 1 a).1 ξ := rfl
    have hfy : f.base ξ.1 ≠ y := by
      intro hfy
      rw [hval, fibreRestrict_apply_of_base_eq _ hfy, sub_self] at hξ
      exact hξ rfl
    have haξ : a.1 ξ ≠ 0 := by
      intro h0
      rw [hval, h0, fibreRestrict_apply_of_base_ne _ hfy, sub_zero] at hξ
      exact hξ rfl
    exact hfy (eq_of_specializes_of_relativeDimension_le C sY (hy' ▸ hspec.map f.continuous)
      (ha ξ haξ))
  have hsub := congrArg (fibreRestrict C sX f y k 0)
    (congrArg (pointwiseDivisorDifferential C sX k)
      (sub_add_cancel a (fibreRestrict C sX f y (k + 1) 1 a)))
  rwa [map_add, map_add, hrest, zero_add, hdiv] at hsub

/-- On the fibre over a point `y` of relative dimension `N`, the boundary of the sum of a family
carried over points of relative dimension `N` is the boundary of the chain over `y`. -/
theorem fibreRestrict_boundary_fibreFamily_sum (k : ℤ) (F : FibreFamily C sX f (k + 2) 2)
    {N : ℤ} (hF : ∀ y, F.chain y ≠ 0 → relativeDimension C.dimensionFunction sY y = N)
    {y : Y} (hy : relativeDimension C.dimensionFunction sY y = N) :
    fibreRestrict C sX f y (k + 1) 1 (pointwiseMilnorBoundary C sX k F.sum) =
      fibreRestrict C sX f y (k + 1) 1 (pointwiseMilnorBoundary C sX k (F.chain y)) := by
  have hzero : fibreRestrict C sX f y (k + 1) 1
      (pointwiseMilnorBoundary C sX k (F.sum - F.chain y)) = 0 := by
    refine milnorChainRestrict_pointwiseMilnorBoundary_eq_zero k _ ?_
    intro w hw y' hy' hspec
    obtain ⟨hwy, hFw⟩ := fibreFamily_sum_sub_apply_ne_zero F y hw
    exact hwy (eq_of_specializes_of_relativeDimension_le C sY (hy' ▸ hspec.map f.continuous)
      (by rw [hF _ hFw, hy]))
  have hsplit := congrArg (fibreRestrict C sX f y (k + 1) 1)
    (congrArg (pointwiseMilnorBoundary C sX k) (sub_add_cancel F.sum (F.chain y)))
  rw [map_add, map_add, hzero, zero_add] at hsplit
  exact hsplit.symm

/-- **Subtracting fibrewise lifts lowers the level.** If every point carrying `a` lies over a
point of relative dimension at most `N`, and `F` is a family carried over points of relative
dimension `N` whose boundaries agree with `a` on those fibres, then every point carrying `a` minus
the boundary of the sum of `F` lies over a point of relative dimension at most `N - 1`. -/
theorem relativeDimension_le_of_sub_boundary_fibreFamily_sum (k : ℤ) {N : ℤ}
    (a : PointwiseKOneGroup C sX k)
    (ha : ∀ ξ : pointsOfDimension C sX (k + 1), a.1 ξ ≠ 0 →
      relativeDimension C.dimensionFunction sY (f.base ξ.1) ≤ N)
    (F : FibreFamily C sX f (k + 2) 2)
    (hF : ∀ y, F.chain y ≠ 0 → relativeDimension C.dimensionFunction sY y = N)
    (hFa : ∀ y, relativeDimension C.dimensionFunction sY y = N →
      fibreRestrict C sX f y (k + 1) 1 (pointwiseMilnorBoundary C sX k (F.chain y)) =
        fibreRestrict C sX f y (k + 1) 1 a)
    (ξ : pointsOfDimension C sX (k + 1))
    (hξ : (a - pointwiseMilnorBoundary C sX k F.sum).1 ξ ≠ 0) :
    relativeDimension C.dimensionFunction sY (f.base ξ.1) ≤ N - 1 := by
  have hbd : ∀ ξ' : pointsOfDimension C sX (k + 1),
      (pointwiseMilnorBoundary C sX k F.sum).1 ξ' ≠ 0 →
        relativeDimension C.dimensionFunction sY (f.base ξ'.1) ≤ N := by
    intro ξ' hξ'
    obtain ⟨w, hw, hsp⟩ := exists_specializes_of_pointwiseMilnorBoundary_apply_ne_zero k _ hξ'
    have hFw : F.chain (f.base w.1) ≠ 0 := fun h0 ↦ hw (by rw [FibreFamily.sum_apply, h0]; rfl)
    rw [← hF _ hFw]
    exact relativeDimension_le_of_specializes C sY (hsp.map f.continuous)
  have hval : (a - pointwiseMilnorBoundary C sX k F.sum).1 ξ =
      a.1 ξ - (pointwiseMilnorBoundary C sX k F.sum).1 ξ := rfl
  have hle : relativeDimension C.dimensionFunction sY (f.base ξ.1) ≤ N := by
    by_contra hgt
    have h1 : a.1 ξ = 0 := not_not.mp fun h ↦ hgt (ha ξ h)
    have h2 : (pointwiseMilnorBoundary C sX k F.sum).1 ξ = 0 := not_not.mp fun h ↦ hgt (hbd ξ h)
    exact hξ (by rw [hval, h1, h2, sub_zero])
  obtain hlt | heq := hle.lt_or_eq
  · omega
  have hdecomp := (fibreRestrict_boundary_fibreFamily_sum C sX sY f k F hF heq).trans (hFa _ heq)
  have hv := congrArg (fun c : PointwiseKOneGroup C sX k ↦ c.1 ξ) hdecomp
  rw [fibreRestrict_apply_of_base_eq _ rfl, fibreRestrict_apply_of_base_eq _ rfl] at hv
  exact absurd (by rw [hval, hv, sub_self]) hξ

include hbase hb in
/-- **One level of the dévissage.** If every point carrying the K₁-chain `a` lies over a point of
relative dimension at most `N ≠ k + 1 - r`, and the divisor of `a` has no component on the
fibres over the points of relative dimension `N`, then `a` differs by a tame-symbol boundary from
a chain all of whose points lie over points of relative dimension at most `N - 1`. -/
theorem exists_devissage_step (k : ℤ) (hL : ∀ y : Y, FibreBoundaryLift C sX sY f r k y)
    (N : ℤ) (hN : N ≠ k + 1 - r) (a : PointwiseKOneGroup C sX k)
    (ha : ∀ ξ : pointsOfDimension C sX (k + 1), a.1 ξ ≠ 0 →
      relativeDimension C.dimensionFunction sY (f.base ξ.1) ≤ N)
    (hdiv : ∀ y : Y, relativeDimension C.dimensionFunction sY y = N →
      fibreRestrict C sX f y k 0 (pointwiseDivisorDifferential C sX k a) = 0) :
    ∃ η : PointwiseKTwoGroup C sX k, ∀ ξ : pointsOfDimension C sX (k + 1),
      (a - pointwiseMilnorBoundary C sX k η).1 ξ ≠ 0 →
        relativeDimension C.dimensionFunction sY (f.base ξ.1) ≤ N - 1 := by
  classical
  have := quasiCompact_of_isAffineSpaceBundle f r hb
  have hpiece : ∀ y : Y, relativeDimension C.dimensionFunction sY y = N →
      ∃ η : PointwiseKTwoGroup C sX k, fibreRestrict C sX f y (k + 2) 2 η = η ∧
        fibreRestrict C sX f y (k + 1) 1 (pointwiseMilnorBoundary C sX k η) =
          fibreRestrict C sX f y (k + 1) 1 a := fun y hy ↦
    hL y (by rwa [hy]) _ (by rw [milnorChainRestrict_milnorChainRestrict, Set.inter_self])
      (fibreRestrict_divisor_fibreRestrict_eq_zero_of_relativeDimension_le C sX sY f k a
        (fun ξ hξ ↦ by rw [hy]; exact ha ξ hξ) (hdiv y hy))
  let F : FibreFamily C sX f (k + 2) 2 :=
    { chain := fun y ↦ if h : relativeDimension C.dimensionFunction sY y = N ∧
          fibreRestrict C sX f y (k + 1) 1 a ≠ 0 then (hpiece y h.1).choose else 0
      supported := fun y w hw ↦ by
        change ((if h : _ ∧ _ then (hpiece y h.1).choose else 0 :
          PointwiseKTwoGroup C sX k)).1 w ≠ 0 at hw
        split_ifs at hw with h
        · rw [← (hpiece y h.1).choose_spec.1] at hw
          by_contra hne
          exact hw (fibreRestrict_apply_of_base_ne _ hne)
        · exact absurd rfl hw
      finite := fun W hW ↦ (finite_inter_image_support (f := f) a W hW).subset fun y hy ↦
        ⟨hy.1, exists_base_eq_of_fibreRestrict_ne_zero (f := f) (a := a) fun h0 ↦ hy.2 (by
          show (if h : _ ∧ _ then (hpiece y h.1).choose else 0 : PointwiseKTwoGroup C sX k) = 0
          rw [dite_eq_right fun h ↦ h.2 h0])⟩ }
  have hF0 : ∀ y, ¬(relativeDimension C.dimensionFunction sY y = N ∧
      fibreRestrict C sX f y (k + 1) 1 a ≠ 0) → F.chain y = 0 := fun y h ↦ by
    show (if h : _ ∧ _ then _ else 0) = 0
    rw [dite_eq_right h]
  refine ⟨F.sum, relativeDimension_le_of_sub_boundary_fibreFamily_sum C sX sY f k a ha F
    (fun y hy ↦ not_not.mp fun hne ↦ hy (hF0 y fun h ↦ hne h.1)) fun y hy ↦ ?_⟩
  by_cases hay : fibreRestrict C sX f y (k + 1) 1 a = 0
  · rw [hF0 y fun h ↦ h.2 hay, map_zero, map_zero, hay]
  · have hFy : F.chain y = (hpiece y hy).choose := by
      show (if h : _ ∧ _ then _ else 0) = _
      rw [dite_eq_left ⟨hy, hay⟩]
    rw [hFy]
    exact (hpiece y hy).choose_spec.2

end Step

/-! ### The whole dévissage -/

section Whole

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) (hbase : f ≫ sY = sX) {r : ℕ}
  (hb : IsAffineSpaceBundle f r)

include hbase hb in
/-- **The dévissage.** If the divisor of a K₁-chain `a` has no component on the fibres over the
points of relative dimension greater than `k + 1 - r`, then `a` differs by a tame-symbol boundary
from a chain all of whose points lie over points of relative dimension at most `k + 1 - r`. -/
theorem exists_devissage (k : ℤ) (hL : ∀ y : Y, FibreBoundaryLift C sX sY f r k y)
    (a : PointwiseKOneGroup C sX k)
    (hdiv : ∀ y : Y, k + 1 - r < relativeDimension C.dimensionFunction sY y →
      fibreRestrict C sX f y k 0 (pointwiseDivisorDifferential C sX k a) = 0) :
    ∃ η : PointwiseKTwoGroup C sX k, ∀ ξ : pointsOfDimension C sX (k + 1),
      (a - pointwiseMilnorBoundary C sX k η).1 ξ ≠ 0 →
        relativeDimension C.dimensionFunction sY (f.base ξ.1) ≤ k + 1 - r := by
  suffices h : ∀ n : ℕ, n ≤ r → ∃ η : PointwiseKTwoGroup C sX k,
      ∀ ξ : pointsOfDimension C sX (k + 1), (a - pointwiseMilnorBoundary C sX k η).1 ξ ≠ 0 →
        relativeDimension C.dimensionFunction sY (f.base ξ.1) ≤ k + 1 - n from h r le_rfl
  intro n hn
  induction n with
  | zero =>
    refine ⟨0, fun ξ _ ↦ ?_⟩
    have := relativeDimension_le_of_isAffineSpaceBundle C sX sY f hbase hb ξ.1
    rw [(mem_pointsOfDimension C sX).mp ξ.2] at this
    simpa using this
  | succ n ih =>
    obtain ⟨η, hη⟩ := ih (Nat.le_of_succ_le hn)
    have hnr : (n : ℤ) < r := by exact_mod_cast hn
    have hdiv' : ∀ y : Y, relativeDimension C.dimensionFunction sY y = k + 1 - n →
        fibreRestrict C sX f y k 0
          (pointwiseDivisorDifferential C sX k (a - pointwiseMilnorBoundary C sX k η)) = 0 := by
      intro y hy
      rw [map_sub, pointwiseDivisorDifferential_pointwiseMilnorBoundary, sub_zero]
      exact hdiv y (by omega)
    obtain ⟨η', hη'⟩ := exists_devissage_step C sX sY f hbase hb k hL (k + 1 - n)
      (by omega) _ hη hdiv'
    refine ⟨η + η', fun ξ hξ ↦ ?_⟩
    have := hη' ξ (by rwa [map_add, ← sub_sub] at hξ)
    push_cast
    omega

end Whole

/-! ### Injectivity of flat pullback from the fibrewise properties -/

/-- Transporting the zero class along an equality of points gives the zero class. -/
theorem cast_milnorKTheory_residueField_zero {Y : Scheme.{u}} {y y' : Y} (e : y = y') (n : ℕ) :
    cast (congrArg (fun z ↦ MilnorKTheory (Y.residueField z) n) e)
      (0 : MilnorKTheory (Y.residueField y) n) = 0 := by
  subst e
  rfl

section Injectivity

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) (hbase : f ≫ sY = sX) {r : ℕ}
  (hb : IsAffineSpaceBundle f r)

include hbase hb in
/-- Two points of relative dimension `k + r + 1` over the same point of relative dimension
`k + 1` coincide. -/
theorem eq_of_base_eq_of_mem_pointsOfDimension (k : ℤ)
    {ξ ξ' : pointsOfDimension C sX (k + r + 1)} (h : f.base ξ.1 = f.base ξ'.1)
    (hmem : f.base ξ.1 ∈ pointsOfDimension C sY (k + 1)) : ξ = ξ' := by
  refine Subtype.ext (eq_of_relativeDimension_eq_add_of_isAffineSpaceBundle C sX sY f hbase hb
    h ?_ ?_)
  · rw [(mem_pointsOfDimension C sX).mp ξ.2, (mem_pointsOfDimension C sY).mp hmem]
    ring
  · rw [(mem_pointsOfDimension C sX).mp ξ'.2, ← h, (mem_pointsOfDimension C sY).mp hmem]
    ring

include hbase hb in
/-- **A K₁-chain whose values descend to `Y` is a pullback.** If every point carrying `a` lies
over a point of relative dimension `k + 1`, and the value of `a` at each of them comes from the
residue field of its image, then `a` is the pullback of a K₁-chain on `Y` carried by the images
of the points carrying `a`. -/
theorem exists_eq_bundleChainPullback_of_forall_exists (k : ℤ)
    (a : PointwiseKOneGroup C sX (k + r))
    (hlev : ∀ ξ : pointsOfDimension C sX (k + r + 1), a.1 ξ ≠ 0 →
      relativeDimension C.dimensionFunction sY (f.base ξ.1) = k + 1)
    (hdesc : ∀ ξ : pointsOfDimension C sX (k + r + 1), a.1 ξ ≠ 0 →
      ∃ c : MilnorKTheory (Y.residueField (f.base ξ.1)) 1,
        a.1 ξ = milnorKTransport (f.residueFieldMap ξ.1).hom 1 c) :
    ∃ b : PointwiseKOneGroup C sY k,
      a = bundleChainPullback C sX sY f hbase hb (k + 1) (k + r + 1) (by ring) 1 b ∧
      ∀ y : pointsOfDimension C sY (k + 1), b.1 y ≠ 0 →
        ∃ ξ : pointsOfDimension C sX (k + r + 1), f.base ξ.1 = y.1 ∧ a.1 ξ ≠ 0 := by
  classical
  have := quasiCompact_of_isAffineSpaceBundle f r hb
  let c : ∀ ξ : pointsOfDimension C sX (k + r + 1), MilnorKTheory (Y.residueField (f.base ξ.1)) 1 :=
    fun ξ ↦ if h : a.1 ξ ≠ 0 then (hdesc ξ h).choose else 0
  have hc0 : ∀ ξ, a.1 ξ = 0 → c ξ = 0 := fun ξ h ↦ dite_eq_right (not_not.mpr h)
  have hc : ∀ ξ, a.1 ξ = milnorKTransport (f.residueFieldMap ξ.1).hom 1 (c ξ) := fun ξ ↦ by
    by_cases h : a.1 ξ = 0
    · rw [hc0 ξ h, map_zero, h]
    · rw [show c ξ = (hdesc ξ h).choose from dite_eq_left h]
      exact (hdesc ξ h).choose_spec
  let bfun : ∀ y : pointsOfDimension C sY (k + 1), MilnorKTheory (Y.residueField y.1) 1 :=
    fun y ↦ if h : ∃ ξ : pointsOfDimension C sX (k + r + 1), f.base ξ.1 = y.1 then
      cast (congrArg (fun z ↦ MilnorKTheory (Y.residueField z) 1) h.choose_spec) (c h.choose)
      else 0
  have hbfun_ne : ∀ y, bfun y ≠ 0 → ∃ ξ : pointsOfDimension C sX (k + r + 1),
      f.base ξ.1 = y.1 ∧ a.1 ξ ≠ 0 := by
    intro y hy
    by_cases h : ∃ ξ : pointsOfDimension C sX (k + r + 1), f.base ξ.1 = y.1
    · refine ⟨h.choose, h.choose_spec, fun h0 ↦ hy ?_⟩
      rw [show bfun y = _ from dite_eq_left h, hc0 _ h0]
      exact cast_milnorKTheory_residueField_zero h.choose_spec 1
    · exact absurd (dite_eq_right h) hy
  let b : PointwiseKOneGroup C sY k := ⟨bfun, fun W hW ↦
    (Set.Finite.preimage (Set.injOn_of_injective Subtype.val_injective)
      (finite_inter_image_support (f := f) a W hW)).subset fun y hy ↦ ⟨hy.1, hbfun_ne y hy.2⟩⟩
  refine ⟨b, Subtype.ext (funext fun ξ ↦ ?_), hbfun_ne⟩
  by_cases hmem : f.base ξ.1 ∈ pointsOfDimension C sY (k + 1)
  · rw [bundleChainPullback_apply_of_mem C sX sY f hbase hb _ b ξ hmem, hc ξ]
    congr 1
    have hex : ∃ ξ' : pointsOfDimension C sX (k + r + 1), f.base ξ'.1 = f.base ξ.1 := ⟨ξ, rfl⟩
    show c ξ = (if h : ∃ ξ' : pointsOfDimension C sX (k + r + 1), f.base ξ'.1 = f.base ξ.1 then
      cast (congrArg (fun z ↦ MilnorKTheory (Y.residueField z) 1) h.choose_spec)
        (c h.choose) else 0)
    rw [dite_eq_left hex]
    have heq := eq_of_base_eq_of_mem_pointsOfDimension C sX sY f hbase hb k
      hex.choose_spec.symm hmem
    generalize hex.choose_spec = e
    revert e
    rw [← heq]
    exact fun _ ↦ rfl
  · rw [bundleChainPullback_apply_of_notMem C sX sY f hbase hb _ b ξ hmem]
    by_contra h
    exact hmem (by rw [mem_pointsOfDimension, hlev ξ h])

include hbase hb in
/-- **A K₁-chain living at the generic points of the fibres over points of relative dimension
`k + 1`, with no divisor on those fibres, is a pullback**, given the unit-descent property of the
fibres. -/
theorem exists_eq_bundleChainPullback_of_fibreUnitDescent (k : ℤ)
    (hU : ∀ y : Y, FibreUnitDescent C sX sY f r (k + r) y)
    (a : PointwiseKOneGroup C sX (k + r))
    (ha : ∀ ξ : pointsOfDimension C sX (k + r + 1), a.1 ξ ≠ 0 →
      relativeDimension C.dimensionFunction sY (f.base ξ.1) ≤ k + 1)
    (hdiv : ∀ ξ : pointsOfDimension C sX (k + r + 1), a.1 ξ ≠ 0 →
      fibreRestrict C sX f (f.base ξ.1) (k + r) 0
        (pointwiseDivisorDifferential C sX (k + r) a) = 0) :
    ∃ b : PointwiseKOneGroup C sY k,
      a = bundleChainPullback C sX sY f hbase hb (k + 1) (k + r + 1) (by ring) 1 b ∧
      ∀ y : pointsOfDimension C sY (k + 1), b.1 y ≠ 0 →
        ∃ ξ : pointsOfDimension C sX (k + r + 1), f.base ξ.1 = y.1 ∧ a.1 ξ ≠ 0 := by
  have hlev : ∀ ξ : pointsOfDimension C sX (k + r + 1), a.1 ξ ≠ 0 →
      relativeDimension C.dimensionFunction sY (f.base ξ.1) = k + 1 := by
    intro ξ hξ
    have h1 := relativeDimension_le_add_of_isAffineSpaceBundle C sX sY f hbase hb ξ.1
    rw [(mem_pointsOfDimension C sX).mp ξ.2] at h1
    have h2 := ha ξ hξ
    omega
  refine exists_eq_bundleChainPullback_of_forall_exists C sX sY f hbase hb k a hlev
    fun ξ hξ ↦ ?_
  obtain ⟨c, hc⟩ := hU (f.base ξ.1) (by rw [hlev ξ hξ]; ring)
    (fibreRestrict C sX f (f.base ξ.1) (k + r + 1) 1 a)
    (by rw [milnorChainRestrict_milnorChainRestrict, Set.inter_self])
    (fibreRestrict_divisor_fibreRestrict_eq_zero_of_relativeDimension_le C sX sY f (k + r) a
      (fun ξ' hξ' ↦ by rw [hlev ξ' hξ', hlev ξ hξ]) (hdiv ξ hξ)) ξ rfl
  refine ⟨c, ?_⟩
  rw [← hc, fibreRestrict_apply_of_base_eq _ rfl]

include hbase hb in
/-- **Injectivity of flat pullback along an affine-space bundle, from the fibrewise
properties.** If every fibre has the boundary-lifting and unit-descent properties of
`Stacks.Chow.FibreBoundaryLift` and `Stacks.Chow.FibreUnitDescent`, and pullback of K₁-chains is
compatible with the divisor differential of Stacks 0GU3, then `f^* : A_k(Y) ⟶ A_{k+r}(X)` is
injective. -/
theorem flatPullbackChow_injective_of_fibreProperties [LocallyOfFiniteType f] [Flat f]
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ)
    (hL : ∀ y : Y, FibreBoundaryLift C sX sY f r (k + r) y)
    (hU : ∀ y : Y, FibreUnitDescent C sX sY f r (k + r) y)
    (hdivpull : ∀ a : PointwiseKOneGroup C sY k,
      pointwiseDivisorDifferential C sX (k + r)
          (bundleChainPullback C sX sY f hbase hb (k + 1) (k + r + 1) (by ring) 1 a) =
        bundleChainPullback C sX sY f hbase hb k (k + r) rfl 0
          (pointwiseDivisorDifferential C sY k a)) :
    Function.Injective (flatPullbackChowOfRelativeDimension C sX sY f hbase r hf k) := by
  rw [injective_iff_map_eq_zero]
  intro α hα
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C sY k) α
  rw [flatPullbackChowOfRelativeDimension_mk] at hα
  set cp := pointwiseCycleEquiv C sY k c with hcp
  have hclass : pointwiseChowClass C sX (k + r)
      (pointwiseCycleEquiv C sX (k + r) (flatPullback C sX sY f hbase r hf k c)) = 0 := by
    show QuotientAddGroup.mk' _ ((pointwiseCycleEquiv C sX (k + r)).symm
      (pointwiseCycleEquiv C sX (k + r) _)) = 0
    rw [AddEquiv.symm_apply_apply]
    exact hα
  obtain ⟨a, ha⟩ := (pointwiseChowClass_eq_zero_iff C sX (k + r) _).mp hclass
  rw [pointwiseCycleEquiv_flatPullback_of_isAffineSpaceBundle C sX sY f hbase hb hf k c] at ha
  -- the divisor of `a` has no component over points of relative dimension other than `k`
  have hdivy : ∀ y : Y, relativeDimension C.dimensionFunction sY y ≠ k →
      fibreRestrict C sX f y (k + r) 0 (pointwiseDivisorDifferential C sX (k + r) a) = 0 := by
    intro y hy
    show milnorChainRestrict C sX (f.base ⁻¹' {y}) (k + r) 0
      (pointwiseDivisorDifferential C sX (k + r) a) = 0
    rw [ha, milnorChainRestrict_preimage_bundleChainPullback]
    rw [milnorChainRestrict_eq_zero _ fun z _ hz ↦ hy (by
      rw [← (mem_pointsOfDimension C sY).mp z.2]
      exact congrArg _ (Set.mem_singleton_iff.mp hz).symm), map_zero]
  obtain ⟨η, hη⟩ := exists_devissage C sX sY f hbase hb (k + r) hL a fun y hy ↦
    hdivy y (by omega)
  obtain ⟨b, hb', -⟩ := exists_eq_bundleChainPullback_of_fibreUnitDescent C sX sY f hbase hb k hU
    (a - pointwiseMilnorBoundary C sX (k + r) η) (fun ξ hξ ↦ by
      have := hη ξ hξ
      omega) (fun ξ hξ ↦ by
      rw [map_sub, pointwiseDivisorDifferential_pointwiseMilnorBoundary, sub_zero]
      have := hη ξ hξ
      exact hdivy _ (by
        have h1 := relativeDimension_le_add_of_isAffineSpaceBundle C sX sY f hbase hb ξ.1
        rw [(mem_pointsOfDimension C sX).mp ξ.2] at h1
        omega))
  have hdiv := congrArg (pointwiseDivisorDifferential C sX (k + r)) hb'
  rw [map_sub, pointwiseDivisorDifferential_pointwiseMilnorBoundary, sub_zero, ha,
    hdivpull b] at hdiv
  have hcb := bundleChainPullback_zero_injective C sX sY f hbase hb (rfl : k + r = k + r) hdiv
  have : pointwiseChowClass C sY k cp = 0 := by
    rw [hcp, hcb]
    exact pointwiseChowClass_pointwiseDivisorDifferential C sY k b
  change QuotientAddGroup.mk' _ ((pointwiseCycleEquiv C sY k).symm cp) = 0 at this
  rwa [hcp, AddEquiv.symm_apply_apply] at this

end Injectivity

end Stacks.Chow

end
