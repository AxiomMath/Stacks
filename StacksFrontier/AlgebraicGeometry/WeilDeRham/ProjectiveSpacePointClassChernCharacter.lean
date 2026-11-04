module

public import StacksFrontier.Algebra.DirectSum.RangeGrading
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TwistFormula
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleTwist
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.IteratedCap
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.ChernCharacterFundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.SmoothComparison
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TensorPowerSums
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.ProjectiveSpacePointClass

/-!
# The top Chern character of `𝒪(1)` on `ℙ^d_k` is the class of a point over `d!`

The cycle class map of Stacks 0FIF is defined on the classes `ch(α) ∩ [X] ∈ CH_*(X) ⊗ 𝐐`
(Chow Homology, Tags 0FEY and 0FEM). For `X = ℙ^d_k`, `α = [𝒪(1)]` and a `k`-rational point `x`,
the part of `ch(𝒪(1)) ∩ [ℙ^d_k]` of dimension `0` is

  `ch_d(𝒪(1)) ∩ [ℙ^d_k] = (1/d!) · x_*[Spec k]`   in `CH_0(ℙ^d_k) ⊗ 𝐐`.

This file proves it, with `ch` the Chern character of the base
(`Stacks.Chow.chernCharacterVectorBundle`, `ch_p = P_p/p!`), `-∩-` the cap product of Chow
cohomology classes on `CH_*(X) ⊗ 𝐐` (`Stacks.Chow.rationalChowCap`), and
`ch(α) ∩ [X]` the map of Stacks 0FEY (`Stacks.Chow.chernCharacterCapFundamentalClass`).

## The argument

For an invertible module `ℒ` the power sum is `P_p(ℒ) = c₁(ℒ)^p`
(`Stacks.Chow.powerSumTotal_of_rank_one`), and the operation of a total Chow cohomology class on
a test scheme is a ring homomorphism (`Stacks.Chow.TotalChowClass.op_pow`), the index-one part
of `c(ℒ)` acting by the first Chern class cap `c₁(ℒ) ∩ -` of Stacks 02SO / 02TI
(`Stacks.Chow.GenuineChern.chernCap_one_eq_invCap`).
So `P_p(ℒ) ∩ -` is the `p`-th power `Stacks.Chow.capPow` of `c₁(ℒ) ∩ -`
(`Stacks.WeilDeRham.chowCohomologyCap_powerSumClassOfFiniteLocallyFree_heq`), read on the test
scheme `𝟙 X`. On `ℙ^d_k` the fundamental class is concentrated in dimension `d`, and
`c₁(𝒪(1))^d ∩ [ℙ^d_k] = x_*[Spec k]` is
`Stacks.WeilDeRham.properChowPushforward_point_eq_capPow_of_iso`.

## Main results

* `Stacks.WeilDeRham.rationalChowCap_chernCharacter_twistingSheaf_eq_point` —
  `ch_d(𝒪(1)) ∩ [ℙ^d_k] = (1/d!) ⊗ x_*[Spec k]` in `CH_*(ℙ^d_k) ⊗ 𝐐`, placed in dimension `0`.
* `Stacks.WeilDeRham.chernCharacterCapFundamentalClass_twistingSheaf_apply_zero` — the
  dimension-`0` part of `ch(𝒪(1)) ∩ [ℙ^d_k]` is `(1/d!) ⊗ x_*[Spec k]`.
* `Stacks.WeilDeRham.chowCohomologyCap_powerSumClassOfFiniteLocallyFree_heq` — for `ℒ` of rank
  one on any `X`, `P_n(ℒ) ∩ α = c₁(ℒ)^n ∩ α`.

## References

* [Stacks Project, Tag 0FWD](https://stacks.math.columbia.edu/tag/0FWD)
* [Stacks Project, Tag 0FIF](https://stacks.math.columbia.edu/tag/0FIF)
* [Stacks Project, Tag 0FEY](https://stacks.math.columbia.edu/tag/0FEY)
* [Stacks Project, Tag 0FEM](https://stacks.math.columbia.edu/tag/0FEM)
* [Stacks Project, Tag 0FA7](https://stacks.math.columbia.edu/tag/0FA7)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Stacks.WeilDeRham

open Stacks.Chow

/-! ### The power sums of a module of rank one cap by powers of `c₁` -/

section RankOne

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (L : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1]

/-- **The index-one part of the total Chern class of a module of rank one caps by `c₁`.** On a
test scheme `g : T ⟶ X`, the index-`1` component of the operation of `c(ℒ)` is
`c₁(g^*ℒ) ∩ -`, the first Chern class cap of Stacks 02SO / 02TI. -/
theorem op_totalChern_apply_one {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (a : chowGroup C (g ≫ sX) k) :
    haveI := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank L 1 g
    haveI := GenuineChern.isInvertible_of_rank_one ((Scheme.Modules.pullback g).obj L)
    (totalChern C sX L 1).op g k 1 a =
      (invCap C (g ≫ sX) ((Scheme.Modules.pullback g).obj L)).capOnChow C (g ≫ sX) (k - 1)
        (chowGroupCast C (g ≫ sX) (by omega) a) := by
  have := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank L 1 g
  exact (op_totalChern_apply C sX L 1 g k 1 a).trans
    (GenuineChern.chernCap_one_eq_invCap C (g ≫ sX) ((Scheme.Modules.pullback g).obj L) k a)

/-- **The `n`-th power of `c₁(ℒ)` operates by the `n`-th power of `c₁(g^*ℒ) ∩ -`.** For `ℒ` of
rank one and a test scheme `g`, the index-`n` component of the operation of
`c₁(ℒ)^n = (c(ℒ)_1)^n` is `Stacks.Chow.capPow` of `c₁(g^*ℒ) ∩ -`. -/
theorem op_homComponent_totalChern_pow_heq {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g]
    (n : ℕ) (k : ℤ) (a : chowGroup C (g ≫ sX) k) :
    haveI := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank L 1 g
    haveI := GenuineChern.isInvertible_of_rank_one ((Scheme.Modules.pullback g).obj L)
    ((TotalChowClass.homComponent 1 (totalChern C sX L 1)).op g ^ n) k n a ≍
      capPow C (g ≫ sX) (invCap C (g ≫ sX) ((Scheme.Modules.pullback g).obj L)) n k (k - n)
        (by ring) a := by
  have := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank L 1 g
  have := GenuineChern.isInvertible_of_rank_one ((Scheme.Modules.pullback g).obj L)
  rw [TotalChowClass.op_homComponent]
  have hx := Stacks.Chow.isHomogeneous_homComponent 1 ((totalChern C sX L 1).op g)
  induction n with
  | zero =>
    rw [pow_zero, gradedCap_one_apply_zero, capPow_zero_apply]
    exact (gradedDegreeCast_heq _ _).trans (chowGroupCast_heq C _ _ _).symm
  | succ n ih =>
    rw [pow_succ', gradedCap_mul_succ_of_isHomogeneous_one_left hx, capPow_succ_apply', capTo_def]
    refine (gradedDegreeCast_heq _ _).trans ?_
    rw [homComponent_apply_self, op_totalChern_apply_one]
    refine capOnChow_heq C _ _ (by push_cast; ring) ?_
    refine (chowGroupCast_heq C _ _ _).trans (ih.trans ?_)
    exact GenuineChern.capPow_heq C _ _ _ _ rfl rfl (by push_cast; ring) HEq.rfl

/-- **`P_n(ℒ) ∩ α = c₁(ℒ)^n ∩ α` for `ℒ` of rank one.** The cap product with the `n`-th power sum
`P_n(ℒ) ∈ A^n(X)` (Stacks 0FA7) is the `n`-th power of the first Chern class cap, the latter read
on the test scheme `𝟙 X`, whose Chow groups are those of `X` along
`Stacks.Chow.chowGroupCongr`. -/
theorem chowCohomologyCap_powerSumClassOfFiniteLocallyFree_heq (n : ℕ) (k : ℤ)
    (α : chowGroup C sX k) :
    haveI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
    haveI := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank L 1 (𝟙 X)
    haveI := GenuineChern.isInvertible_of_rank_one ((Scheme.Modules.pullback (𝟙 X)).obj L)
    chowCohomologyCap C (gysinSystemOfInvertible C) sX n
        (powerSumClassOfFiniteLocallyFree C sX L n) k α ≍
      capPow C (𝟙 X ≫ sX) (invCap C (𝟙 X ≫ sX) ((Scheme.Modules.pullback (𝟙 X)).obj L)) n k
        (k - n) (by ring) (chowGroupCongr C (Category.id_comp sX).symm k α) := by
  have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  refine (chowCohomologyCap_heq_idRule_ofGysinSystem C _ sX n _ k α).trans ?_
  rw [powerSumClassOfFiniteLocallyFree, powerSumOfFiniteLocallyFree_eq_powerSumTotal C sX L 1,
    powerSumTotal_of_rank_one, ← TotalChowClass.op_apply, TotalChowClass.op_pow]
  exact op_homComponent_totalChern_pow_heq C sX L (𝟙 X) n k _

end RankOne

/-! ### Transport -/

section Transport

/-- Tensoring with a rational number respects heterogeneous equality of Chow classes in equal
degrees. -/
theorem tmul_chowGroup_heq (C : ChowSituation.{u}) {X : Scheme.{u}} (s : X ⟶ C.S)
    [LocallyOfFiniteType s] {i j : ℤ} (h : i = j) (q : ℚ) {y : chowGroup C s i}
    {z : chowGroup C s j} (hyz : y ≍ z) : (q ⊗ₜ[ℤ] y : ℚ ⊗[ℤ] chowGroup C s i) ≍
      (q ⊗ₜ[ℤ] z : ℚ ⊗[ℤ] chowGroup C s j) := by
  subst h
  cases hyz
  rfl

/-- The class `x_*[S]_n` of a section `x` of a structure morphism `s` does not depend, up to
heterogeneous equality, on how `s` and the degree `n` are written. -/
theorem properChowPushforward_section_heq (C : ChowSituation.{u}) {X : Scheme.{u}}
    (x : C.S ⟶ X) [IsProper x] {s s' : X ⟶ C.S} [LocallyOfFiniteType s]
    [LocallyOfFiniteType s'] (h : s = s') (hx : x ≫ s = 𝟙 _) (hx' : x ≫ s' = 𝟙 _) {n n' : ℤ}
    (hn : n = n') :
    properChowPushforward C (𝟙 _) s x hx n
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ n)
        (fundamentalChowClass C (𝟙 _) n) ≍
      properChowPushforward C (𝟙 _) s' x hx' n'
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ n')
        (fundamentalChowClass C (𝟙 _) n') := by
  subst h hn
  rfl

end Transport

/-! ### The top Chern character of `𝒪(1)` on `ℙ^d_k` -/

section ProjectiveSpace

open Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra
  Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff

variable (k : Type u) [Field k] (d : ℕ)

/-- **`ch_d(𝒪(1)) ∩ [ℙ^d_k] = (1/d!) · x_*[Spec k]`.** For every `k`-rational point `x` of the
polynomial model of `ℙ^d_k`, capping the fundamental class `[ℙ^d_k] ∈ CH_*(ℙ^d_k) ⊗ 𝐐` with the
degree-`d` component `ch_d(𝒪(1)) = P_d(𝒪(1))/d! ∈ A^d(ℙ^d_k) ⊗ 𝐐` of the Chern character of
`𝒪(1)` gives `(1/d!) ⊗ x_*[Spec k]`, in dimension `0`. -/
theorem rationalChowCap_chernCharacter_twistingSheaf_eq_point
    (x : Spec (.of k) ⟶ AlgebraicGeometry.Proj (polyGrading k d))
    (hx : x ≫ projToSpecCoeff k d = 𝟙 _) :
    haveI : IsProper x := isProper_of_comp_eq_id hx
    haveI := isFiniteLocallyFreeOfRank_one_of_isInvertible
      (X := AlgebraicGeometry.Proj (polyGrading k d))
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k d) 1)
    haveI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
      (R := (AlgebraicGeometry.Proj (polyGrading k d)).ringCatSheaf)
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k d) 1) 1
    rationalChowCap (fieldChowSituation k) (gysinSystemOfInvertible _) (projToSpecCoeff k d) d
        (chernCharacterVectorBundle (fieldChowSituation k) (projToSpecCoeff k d)
          (VectorBundleKZero.classOf _ (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k d) 1))
          d)
        (rationalFundamentalClass (fieldChowSituation k) (projToSpecCoeff k d)) =
      DirectSum.of
        (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) (projToSpecCoeff k d) j) 0
        (((d.factorial : ℚ)⁻¹) ⊗ₜ[ℤ]
          properChowPushforward (fieldChowSituation k) (𝟙 _) (projToSpecCoeff k d) x hx 0
            (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ 0)
            (fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0)) := by
  have : IsProper x := isProper_of_comp_eq_id hx
  have := isFiniteLocallyFreeOfRank_one_of_isInvertible
    (X := AlgebraicGeometry.Proj (polyGrading k d))
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k d) 1)
  have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (R := (AlgebraicGeometry.Proj (polyGrading k d)).ringCatSheaf)
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k d) 1) 1
  have := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank
    (X := AlgebraicGeometry.Proj (polyGrading k d))
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k d) 1) 1 (𝟙 _)
  have := GenuineChern.isInvertible_of_rank_one ((Scheme.Modules.pullback
    (𝟙 (AlgebraicGeometry.Proj (polyGrading k d)))).obj
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k d) 1))
  -- `[ℙ^d_k] = 1 ⊗ [ℙ^d_k]_d` and `ch_d(𝒪(1)) = (1/d!) ⊗ P_d(𝒪(1))`
  rw [rationalFundamentalClass_eq_of_relativeDimension k (projToSpecCoeff k d)
      (relativeDimension_projToSpecCoeff k d),
    chernCharacterVectorBundle_classOf (fieldChowSituation k) (projToSpecCoeff k d)
      (X := AlgebraicGeometry.Proj (polyGrading k d))
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k d) 1) d]
  unfold chernCharacterOfFiniteLocallyFree
  rw [rationalChowCap_of_tmul]
  refine DirectSum.of_eq_of_heq (by ring) ?_
  rw [mul_one]
  refine tmul_chowGroup_heq _ _ (by ring) _ ?_
  -- `P_d(𝒪(1)) ∩ [ℙ^d_k]_d = c₁(𝒪(1))^d ∩ [ℙ^d_k]_d`, read on the test scheme `𝟙`
  refine (chowCohomologyCap_powerSumClassOfFiniteLocallyFree_heq _ _ _ d d _).trans ?_
  rw [chowGroupCongr_fundamentalChowClass]
  refine (GenuineChern.capPow_heq _ _ _ _ rfl rfl (by ring : (d : ℤ) = (d - d) + d) rfl
    (fundamentalChowClass_heq _ _ (by ring : (d : ℤ) = (d - d) + d))).trans ?_
  -- `c₁(𝒪(1))^d ∩ [ℙ^d_k] = x_*[Spec k]`
  have hsP : projToSpecCoeff k d ≫ 𝟙 _ = 𝟙 _ ≫ projToSpecCoeff k d := by
    rw [Category.comp_id, Category.id_comp]
  have hx' : x ≫ 𝟙 _ ≫ projToSpecCoeff k d = 𝟙 _ := by rw [Category.id_comp]; exact hx
  have hpt := properChowPushforward_point_eq_capPow_of_iso k d
    (𝟙 _ ≫ projToSpecCoeff k d) hsP
    ((Scheme.Modules.pullback (𝟙 (AlgebraicGeometry.Proj (polyGrading k d)))).obj
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k d) 1))
    ((Scheme.Modules.pullbackId (AlgebraicGeometry.Proj (polyGrading k d))).app
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k d) 1)) x
    hx' ((d : ℤ) - d) (by ring)
  rw [← hpt]
  exact properChowPushforward_section_heq (fieldChowSituation k) x
    (s := 𝟙 _ ≫ projToSpecCoeff k d) (s' := projToSpecCoeff k d) (Category.id_comp _) hx' hx
    (n := (d : ℤ) - d) (n' := 0) (by ring)

/-- **The dimension-`0` part of `ch(𝒪(1)) ∩ [ℙ^d_k]` is `(1/d!) · x_*[Spec k]`.** For every
`k`-rational point `x` of the polynomial model of `ℙ^d_k`, the component in `CH_0(ℙ^d_k) ⊗ 𝐐` of
the class `ch([𝒪(1)]) ∩ [ℙ^d_k]` of Stacks 0FEY — the class the cycle class map of Stacks 0FIF is
defined on — is `(1/d!) ⊗ x_*[Spec k]`. Only `ch_d(𝒪(1))` contributes: `[ℙ^d_k]` lies in
dimension `d` and `ch_p(𝒪(1)) ∩ -` lowers dimension by `p`. -/
theorem chernCharacterCapFundamentalClass_twistingSheaf_apply_zero
    (x : Spec (.of k) ⟶ AlgebraicGeometry.Proj (polyGrading k d))
    (hx : x ≫ projToSpecCoeff k d = 𝟙 _) :
    haveI : IsProper x := isProper_of_comp_eq_id hx
    haveI := isFiniteLocallyFreeOfRank_one_of_isInvertible
      (X := AlgebraicGeometry.Proj (polyGrading k d))
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k d) 1)
    haveI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
      (R := (AlgebraicGeometry.Proj (polyGrading k d)).ringCatSheaf)
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k d) 1) 1
    chernCharacterCapFundamentalClass (fieldChowSituation k) (projToSpecCoeff k d)
        (VectorBundleKZero.classOf _ (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k d) 1))
        0 =
      ((d.factorial : ℚ)⁻¹) ⊗ₜ[ℤ]
        properChowPushforward (fieldChowSituation k) (𝟙 _) (projToSpecCoeff k d) x hx 0
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ 0)
          (fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0) := by
  have htop := rationalChowCap_chernCharacter_twistingSheaf_eq_point k d x hx
  have hfund := rationalFundamentalClass_eq_of_relativeDimension k (projToSpecCoeff k d)
    (relativeDimension_projToSpecCoeff k d)
  rw [hfund, ← DirectSum.lof_eq_of ℚ] at htop
  have hlo : ∀ y : AlgebraicGeometry.Proj (polyGrading k d),
      (0 : ℤ) ≤ relativeDimension (fieldChowSituation k).dimensionFunction
        (projToSpecCoeff k d) y := fun y => by
    rw [relativeDimension, fieldChowSituation_dimensionFunction, zero_add]
    exact Int.natCast_nonneg _
  rw [chernCharacterCapFundamentalClass_apply, hfund, ← DirectSum.lof_eq_of ℚ,
    chernCharacterCap_lof_eq_sum (fieldChowSituation k) (projToSpecCoeff k d) 0 hlo _ d _
      (Finset.range (d + 1)) fun p hp => Finset.mem_range.2 (by omega),
    DFinsupp.finsetSum_apply, Finset.sum_eq_single d]
  · rw [htop, DirectSum.of_eq_same]
  · intro p _ hp
    rw [rationalChowCap_lof, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (by omega)]
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

end ProjectiveSpace

end Stacks.WeilDeRham

end
