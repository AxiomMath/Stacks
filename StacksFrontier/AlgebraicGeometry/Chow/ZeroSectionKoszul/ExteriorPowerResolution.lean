module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.IntegralPerfectComplex
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.CriteriaLocalizedSituation
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectChernProperties
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.TotalChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.ExteriorPowerChernClasses

/-!
# The Chern classes of an object resolved by the exterior powers of a module

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `Y` be locally of
finite type over `S` and let `ℰ` be a finite locally free `𝒪_Y`-module of rank `r`. Suppose an
object `F` of `D(𝒪_Y)` is represented by a complex `K` with

  `K^{-n} ≅ ⋀ⁿ ℰ`  for `n ≥ 0`,  `K^m = 0`  for `m > 0`,

as the Koszul complex of a map `ℰ ⟶ 𝒪_Y` represents the structure sheaf of the closed subscheme
it cuts out when it is a resolution. Then `K` is a bounded complex of finite locally free modules,
so the Chern classes of `F` are defined (Stacks 0GUE (2)), and

  `c(F) = ∏_{n = 0}^{r} c(⋀ⁿ ℰ)^{(-1)ⁿ}`.

Combined with Stacks 0FEE this gives `c_t(F) = 0` for `0 < t < r` and
`c_r(F) = -(r-1)! c_r(ℰ)`, which is the first step of the proof of Stacks 0FEF.

## Main definitions

* `Stacks.Chow.ExteriorPowerResolution` — a representation of `F` by a complex whose terms are the
  exterior powers of `ℰ` in the nonpositive degrees.
* `Stacks.Chow.exteriorPowerRanks` — the ranks `binom(r, -m)` of its terms.

## Main results

* `Stacks.Chow.ExteriorPowerResolution.hasDefinedChernClasses` — the Chern classes of `F` are
  defined.
* `Stacks.Chow.ExteriorPowerResolution.perfectChernClass_eq` — `c(F) = ∏ c(⋀ⁿ ℰ)^{(-1)ⁿ}`.
* `Stacks.Chow.ExteriorPowerResolution.homPart_perfectChernClass` — `c_t(F) = 0` for
  `0 < t < r` and `c_r(F) = -(r-1)! c_r(ℰ)` (Stacks 0FEE).

## References

* [Stacks Project, Tag 0FEF](https://stacks.math.columbia.edu/tag/0FEF)
* [Stacks Project, Tag 0FEE](https://stacks.math.columbia.edu/tag/0FEE)
* [Stacks Project, Tag 0GUE](https://stacks.math.columbia.edu/tag/0GUE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-- **A resolution by exterior powers** of an object `F` of `D(𝒪_Y)`: a cochain complex `K` with
`K^{-n} ≅ ⋀ⁿ ℰ` for every `n ≥ 0` and `K^m = 0` for `m > 0`, together with an isomorphism
`K ≅ F` in `D(𝒪_Y)`. The Koszul complex of a regular section is the example. -/
structure ExteriorPowerResolution {Y : Scheme.{u}} (F : DerivedCategory Y.Modules)
    (ℰ : Y.Modules) where
  /-- The resolving complex. -/
  complex : CochainComplex Y.Modules ℤ
  /-- Its term in degree `-n` is the `n`-th exterior power of `ℰ`. -/
  termIso : ∀ n : ℕ, complex.X (-(n : ℤ)) ≅ Scheme.Modules.exteriorPower ℰ (n : ℤ)
  /-- It vanishes in positive degrees. -/
  isZero_of_pos : ∀ m : ℤ, 0 < m → IsZero (complex.X m)
  /-- It represents `F`. -/
  iso : Nonempty (DerivedCategory.Q.obj complex ≅ F)

/-- The ranks `binom(r, -m)` in the degrees `-r ≤ m ≤ 0` of a resolution of a module of rank `r`
by its exterior powers, and `0` elsewhere. -/
def exteriorPowerRanks (r : ℕ) : ℤ →₀ ℕ :=
  Finsupp.onFinset (Finset.Icc (-(r : ℤ)) 0) (fun m ↦ if m ≤ 0 then r.choose (-m).toNat else 0)
    fun m hm ↦ by
      by_cases h0 : m ≤ 0
      · rw [ite_eq_left h0] at hm
        refine Finset.mem_Icc.mpr ⟨?_, h0⟩
        by_contra hlt
        exact hm (Nat.choose_eq_zero_of_lt (by omega))
      · exact absurd (ite_eq_right h0) hm

/-- The rank in degree `m` is `binom(r, -m)` for `m ≤ 0` and `0` otherwise. -/
theorem exteriorPowerRanks_apply (r : ℕ) (m : ℤ) :
    exteriorPowerRanks r m = if m ≤ 0 then r.choose (-m).toNat else 0 :=
  rfl

/-- The rank in degree `-n` is `binom(r, n)`. -/
theorem exteriorPowerRanks_neg (r n : ℕ) : exteriorPowerRanks r (-(n : ℤ)) = r.choose n := by
  rw [exteriorPowerRanks_apply, ite_eq_left (by omega), neg_neg, Int.toNat_natCast]

/-- The rank vanishes outside the degrees `-r ≤ m ≤ 0`. -/
private theorem exteriorPowerRanks_eq_zero_of_notMem {r : ℕ} {m : ℤ}
    (hm : m ∉ Finset.Icc (-(r : ℤ)) 0) : exteriorPowerRanks r m = 0 :=
  Finsupp.notMem_support_iff.1 fun h ↦ hm (Finsupp.support_onFinset_subset h)

namespace ExteriorPowerResolution

variable {Y : Scheme.{u}} {F : DerivedCategory Y.Modules} {ℰ : Y.Modules} (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} ℰ r]
  (R : ExteriorPowerResolution F ℰ)

/-- **The terms of the resolution have the ranks `binom(r, -m)`.** -/
theorem isFiniteLocallyFreeOfRank_X (m : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R.complex.X m)
      (exteriorPowerRanks r m) := by
  by_cases hm : m ≤ 0
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = -(n : ℤ) := ⟨(-m).toNat, by omega⟩
    rw [exteriorPowerRanks_neg]
    have := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower ℰ r n
    exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      (R.termIso n).symm inferInstance
  · rw [exteriorPowerRanks_apply, ite_eq_right hm]
    exact AlgebraicGeometry.isFiniteLocallyFreeOfRank_zero_of_isZero (R.isZero_of_pos m (by omega))

/-- The resolving complex is zero below degree `-r`: the exterior powers of a module of rank `r`
vanish above `r`. -/
theorem isZero_X_of_lt (m : ℤ) (hm : m < -(r : ℤ)) : IsZero (R.complex.X m) := by
  have h := R.isFiniteLocallyFreeOfRank_X r m
  rw [exteriorPowerRanks_eq_zero_of_notMem (by simp; omega)] at h
  exact Stacks.WeilCohomology.isZero_of_isFiniteLocallyFreeOfRank_zero _ h

include r in
/-- **The resolving complex is a bounded complex of finite locally free modules.** -/
theorem isLocallyBoundedFiniteLocallyFree :
    IsLocallyBoundedFiniteLocallyFree R.complex :=
  isLocallyBoundedFiniteLocallyFree_of_bounded R.complex
    ⟨-(r : ℤ), 0, (CochainComplex.isStrictlyGE_iff _ _).2 fun m hm ↦ R.isZero_X_of_lt r m hm,
      (CochainComplex.isStrictlyLE_iff _ _).2 fun m hm ↦ R.isZero_of_pos m hm⟩
    fun m ↦ @AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ _ _
      _ _ _ _ _ (R.isFiniteLocallyFreeOfRank_X r m)

include r R in
/-- **The Chern classes of an object resolved by exterior powers are defined** (Stacks 0GUE
(2)). -/
theorem hasDefinedChernClasses : HasDefinedChernClasses F :=
  hasDefinedChernClasses_of_envelope (𝟙 Y) ⟨inferInstance, isCompletelyDecomposed_id Y⟩ F
    R.complex (R.isLocallyBoundedFiniteLocallyFree r)
    ⟨(Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIso Y.toRingedSpace).app F ≪≫
      R.iso.some.symm⟩

variable (C : ChowSituation.{u}) (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- The factor of degree `-n` of the total Chern class of the resolving complex is
`c(⋀ⁿ ℰ)^{(-1)ⁿ}`. -/
theorem complexChernFactor_neg (n : ℕ) :
    complexChernFactor C sY R.complex (exteriorPowerRanks r) (R.isFiniteLocallyFreeOfRank_X r)
        (-(n : ℤ)) =
      @totalChernUnit C Y sY _ (Scheme.Modules.exteriorPower ℰ (n : ℤ)) (r.choose n)
        (Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower ℰ r n) ^ ((-1 : ℤ) ^ n) := by
  have := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower ℰ r n
  have := R.isFiniteLocallyFreeOfRank_X r (-(n : ℤ))
  rw [complexChernFactor, Int.negOnePow_neg, Int.coe_negOnePow_natCast]
  congr 1
  exact Units.ext (totalChern_congr C sY (R.termIso n) (exteriorPowerRanks_neg r n))

include R in
/-- **The total Chern class of an object resolved by the exterior powers of `ℰ`** is the
alternating product `∏_{n = 0}^{r} c(⋀ⁿ ℰ)^{(-1)ⁿ}`. -/
theorem perfectChernClass_eq (hF : HasDefinedChernClasses F) :
    perfectChernClass C sY hF = (altExteriorTotalChern C sY ℰ r : TotalChowClass C sY) := by
  rw [perfectChernClass_eq_complexChern C sY hF (R.isLocallyBoundedFiniteLocallyFree r)
      R.iso.some,
    complexChern_eq_complexChernBounded C sY _ (exteriorPowerRanks r)
      (R.isFiniteLocallyFreeOfRank_X r),
    complexChernBounded_eq_prod C sY _ _ _ (Finset.Icc (-(r : ℤ)) 0) fun m hm ↦
      exteriorPowerRanks_eq_zero_of_notMem hm,
    complexChernProd, altExteriorTotalChern]
  congr 1
  -- the two orderings of the factors are permutations of each other
  have hperm : List.Perm ((Finset.Icc (-(r : ℤ)) 0).sort (· ≤ ·))
      ((List.range (r + 1)).map fun n : ℕ ↦ -(n : ℤ)) := by
    refine (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) ?_).2 fun m ↦ ?_
    · exact (List.nodup_range).map fun a b h ↦ by simpa using h
    · simp only [Finset.mem_sort, Finset.mem_Icc, List.mem_map, List.mem_range]
      exact ⟨fun ⟨h1, h2⟩ ↦ ⟨(-m).toNat, by omega, by omega⟩, fun ⟨n, hn, h⟩ ↦ by omega⟩
  have hcomm : ((Finset.Icc (-(r : ℤ)) 0).sort (· ≤ ·)).map
      (complexChernFactor C sY R.complex (exteriorPowerRanks r)
        (R.isFiniteLocallyFreeOfRank_X r)) |>.Pairwise Commute := by
    refine List.Pairwise.map _ (fun a b _ ↦ ?_) (List.pairwise_of_forall_mem_list fun _ _ _ _ ↦
      trivial)
    have := R.isFiniteLocallyFreeOfRank_X r a
    have := R.isFiniteLocallyFreeOfRank_X r b
    refine Commute.zpow_zpow ?_ _ _
    exact Units.ext (totalChern_commute C sY _ _ _ _)
  rw [(hperm.map _).prod_eq' hcomm, List.map_map]
  congr 1
  exact List.map_congr_left fun n _ ↦ R.complexChernFactor_neg r C sY n

include R in
/-- **Stacks 0FEE for an object resolved by exterior powers**: for `ℰ` of rank `r ≥ 1`,
`c_t(F) = 0` for `0 < t < r` and `c_r(F) = -(r-1)! c_r(ℰ)`. -/
theorem homPart_perfectChernClass (hr : r ≠ 0) (hF : HasDefinedChernClasses F) :
    (∀ t, 0 < t → t < r → TotalChowClass.homComponent t (perfectChernClass C sY hF) = 0) ∧
      TotalChowClass.homComponent r (perfectChernClass C sY hF) =
        -(Nat.factorial (r - 1) • TotalChowClass.homComponent r (totalChern C sY ℰ r)) := by
  rw [R.perfectChernClass_eq r C sY hF]
  exact homPart_altExteriorTotalChern C sY ℰ hr

end ExteriorPowerResolution

end Stacks.Chow

end
