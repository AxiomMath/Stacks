module

public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.ExteriorPowerAlternatingDescent
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.KoszulContraction
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ComplexChernClass
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# The total Chern class of a Koszul complex

Let `Y` be locally of finite type over the base of chapter 42, `𝒱` a finite locally free
`𝒪_Y`-module of rank `r ≥ 1` and `φ : 𝒱 ⟶ 𝒪_Y`. The **Koszul complex** of `φ` is the cochain
complex

  `0 ⟶ ⋀ʳ 𝒱 ⟶ ⋯ ⟶ ⋀² 𝒱 ⟶ 𝒱 ⟶ 𝒪_Y ⟶ 0`

with `⋀ⁿ 𝒱` in cohomological degree `-n` and the contraction against `φ` as differential
([Stacks, Tag 062K]). Its total Chern class in the sense of [Stacks, Tag 0ESZ] is the alternating
product `∏_n c(⋀ⁿ 𝒱)^{(-1)ⁿ}`, and by [Stacks, Tag 0FEE] its components in the degrees
`1, …, r - 1` vanish while its degree-`r` component is `-(r - 1)! c_r(𝒱)`.

The computation does not invert anything in a commutative ring: writing `c_±` for the products of
`c(⋀ⁿ 𝒱)` over even and odd `n`, the total Chern class `c(K)` satisfies `c(K) c_- = c_+`
(the factors commute by Stacks 02UA), so `(c(K) - 1) c_- = c_+ - c_-`, and the components of the
right-hand side below the rank are those of
`Stacks.Chow.homComponent_altChern_sub_of_lt`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.koszulChain`: the Koszul complex as a chain complex indexed
  by `ℕ`, with `⋀ⁿ 𝒱` in degree `n`.
* `AlgebraicGeometry.Scheme.Modules.koszulComplex`: the same complex in cohomological degrees
  `≤ 0`.
* `Stacks.Chow.koszulRank`: the ranks of its terms.

## Main results

* `Stacks.Chow.TotalChowClass.homComponent_sub_one_eq_of_mul_eq`: the ring-theoretic step.
* `Stacks.Chow.complexChernBounded_koszulComplex_mul`: `c(K) c_- = c_+`.
* `Stacks.Chow.homComponent_complexChernBounded_koszulComplex_of_lt`,
  `Stacks.Chow.homComponent_complexChernBounded_koszulComplex_rank`: Stacks 0FEE for the Koszul
  complex.

## References

* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
* [Stacks Project, Tag 0FEE](https://stacks.math.columbia.edu/tag/0FEE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Finset

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (V : X.Modules) (φ : V ⟶ SheafOfModules.unit X.ringCatSheaf)

/-- **The Koszul contraction `⋀ⁿ⁺¹ 𝒱 ⟶ ⋀ⁿ 𝒱`** against `φ : 𝒱 ⟶ 𝒪_X`, on the scheme-level exterior
powers. -/
def koszulContraction (n : ℕ) :
    exteriorPower V ((n + 1 : ℕ) : ℤ) ⟶ exteriorPower V ((n : ℕ) : ℤ) :=
  SheafOfModules.exteriorContraction (Osharp := X.sheaf) V (exteriorAlgebra V)
    (exteriorGenerator V) (isExteriorAlgebra_exteriorAlgebra V) φ n

/-- Two successive Koszul contractions compose to zero. -/
theorem koszulContraction_comp (n : ℕ) :
    koszulContraction V φ (n + 1) ≫ koszulContraction V φ n = 0 :=
  SheafOfModules.exteriorContraction_comp_exteriorContraction (Osharp := X.sheaf) V
    (exteriorAlgebra V) (exteriorGenerator V) (isExteriorAlgebra_exteriorAlgebra V) φ n

/-- **The Koszul complex of `φ : 𝒱 ⟶ 𝒪_X`**, indexed homologically: `⋀ⁿ 𝒱` in degree `n`, with
the contraction against `φ` as differential (Stacks 062K). -/
def koszulChain : ChainComplex X.Modules ℕ :=
  ChainComplex.of (fun n => exteriorPower V ((n : ℕ) : ℤ)) (koszulContraction V φ)
    (koszulContraction_comp V φ)

/-- **The Koszul complex of `φ : 𝒱 ⟶ 𝒪_X` in cohomological degrees `≤ 0`**: `⋀ⁿ 𝒱` sits in
degree `-n`, and the terms in positive degrees are zero. -/
def koszulComplex : CochainComplex X.Modules ℤ :=
  (koszulChain V φ).extend ComplexShape.embeddingDownNat

/-- The term of the Koszul complex in degree `-n` is `⋀ⁿ 𝒱`. -/
def koszulComplexXIso (n : ℕ) {m : ℤ} (hm : -(n : ℤ) = m) :
    (koszulComplex V φ).X m ≅ exteriorPower V ((n : ℕ) : ℤ) :=
  (koszulChain V φ).extendXIso ComplexShape.embeddingDownNat hm

/-- The terms of the Koszul complex in positive degrees are zero. -/
theorem isZero_koszulComplex_X {m : ℤ} (hm : 0 < m) : IsZero ((koszulComplex V φ).X m) :=
  (koszulChain V φ).isZero_extend_X ComplexShape.embeddingDownNat m fun n h => by
    simp only [ComplexShape.embeddingDownNat_f] at h
    omega

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.Chow

/-! ### The ring-theoretic step -/

namespace TotalChowClass

variable {C : ChowSituation.{u}} {Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]

/-- **Comparing a total class with a quotient of two others below a degree.** If `P O = E`, the
degree-`0` component of `O` is `1` and `E - O` vanishes in the degrees below `r`, then `P - 1`
and `E - O` have the same components in the degrees `≤ r`. -/
theorem homComponent_sub_one_eq_of_mul_eq {P O E : TotalChowClass C sY} (h : P * O = E)
    (hO : homComponent 0 O = 1) {r : ℕ} (hEO : ∀ s < r, homComponent s (E - O) = 0) :
    ∀ t ≤ r, homComponent t (P - 1) = homComponent t (E - O) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    have key : homComponent t ((P - 1) * O) = homComponent t (E - O) := by
      rw [sub_mul, one_mul, h]
    rw [homComponent_mul, Finset.sum_range_succ', Nat.sub_zero, hO, mul_one] at key
    rw [← key]
    refine (add_eq_right.mpr (Finset.sum_eq_zero fun j hj => ?_)).symm
    have hj' := mem_range.1 hj
    rw [ih (t - (j + 1)) (by omega) (by omega), hEO _ (by omega), zero_mul]

end TotalChowClass

/-! ### The ranks of the Koszul complex -/

section Koszul

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (V : Y.Modules) (φ : V ⟶ SheafOfModules.unit Y.ringCatSheaf) (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} V r]

/-- **The ranks of the Koszul complex** of a module of rank `r`: `binom(r, n)` in degree `-n`. -/
def koszulRank : ℤ →₀ ℕ :=
  Finsupp.onFinset (Finset.Icc (-(r : ℤ)) 0)
    (fun m => if m ≤ 0 then r.choose (-m).toNat else 0) (by
      intro m hm
      rw [Finset.mem_Icc]
      by_contra hc
      apply hm
      by_cases h0 : m ≤ 0
      · rw [if_pos h0]
        exact Nat.choose_eq_zero_of_lt (by omega)
      · rw [if_neg h0])

/-- The rank of the Koszul complex in degree `-n` is `binom(r, n)`. -/
theorem koszulRank_neg (n : ℕ) : koszulRank r (-(n : ℤ)) = r.choose n := by
  simp only [koszulRank, Finsupp.onFinset_apply]
  rw [if_pos (by omega), neg_neg, Int.toNat_natCast]

/-- The rank of the Koszul complex in a positive degree is `0`. -/
theorem koszulRank_of_pos {m : ℤ} (hm : 0 < m) : koszulRank r m = 0 := by
  simp only [koszulRank, Finsupp.onFinset_apply]
  rw [if_neg (by omega)]

/-- The terms of the Koszul complex are finite locally free of the ranks `koszulRank`. -/
theorem isFiniteLocallyFreeOfRank_koszulComplex (m : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.koszulComplex V φ).X m) (koszulRank r m) := by
  by_cases hm : m ≤ 0
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, -(n : ℤ) = m := ⟨(-m).toNat, by omega⟩
    rw [koszulRank_neg]
    have := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower V r n
    exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      (Scheme.Modules.koszulComplexXIso V φ n rfl).symm inferInstance
  · rw [koszulRank_of_pos r (by omega)]
    exact AlgebraicGeometry.isFiniteLocallyFreeOfRank_zero_of_isZero
      (Scheme.Modules.isZero_koszulComplex_X V φ (by omega))

/-- The total Chern class of a term of the Koszul complex is that of the exterior power. -/
theorem totalChern_koszulComplex_X (n : ℕ) (_hn : n ≤ r) :
    letI := isFiniteLocallyFreeOfRank_koszulComplex V φ r (-(n : ℤ))
    letI := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower V r n
    totalChern C sY ((Scheme.Modules.koszulComplex V φ).X (-(n : ℤ))) (koszulRank r (-(n : ℤ))) =
      totalChern C sY (Scheme.Modules.exteriorPower V ((n : ℕ) : ℤ)) (r.choose n) := by
  let := isFiniteLocallyFreeOfRank_koszulComplex V φ r (-(n : ℤ))
  let := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower V r n
  exact totalChern_congr C sY (Scheme.Modules.koszulComplexXIso V φ n rfl) (koszulRank_neg r n)

/-- `[-r, 0] ⊆ ℤ` is the image of `range (r + 1)` under `m ↦ -m`. -/
private theorem Icc_neg_natCast_zero_eq_map_range (r : ℕ) :
    Finset.Icc (-(r : ℤ)) 0 =
      (range (r + 1)).map ⟨fun m : ℕ => -(m : ℤ), fun a b h => by simpa using h⟩ := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_map, mem_range]
  show _ ↔ ∃ a, a < r + 1 ∧ -(a : ℤ) = n
  exact ⟨fun hn => ⟨(-n).toNat, by omega, by omega⟩, fun ⟨m, hm, h⟩ => by omega⟩

open scoped IsMulCommutative in
/-- **`c(K) c_- = c_+`** for the Koszul complex `K` of `φ : 𝒱 ⟶ 𝒪_Y`, `𝒱` of rank `r`: the total
Chern class of Stacks 0ESZ of the Koszul complex, multiplied by the product of the `c(⋀ⁿ 𝒱)` over
odd `n`, is the product over even `n`. -/
theorem complexChernBounded_koszulComplex_mul :
    complexChernBounded C sY (Scheme.Modules.koszulComplex V φ) (koszulRank r)
        (isFiniteLocallyFreeOfRank_koszulComplex V φ r) *
      ((altChernOdd C sY V r : chernTotalSubring C sY) : TotalChowClass C sY) =
    ((altChernEven C sY V r : chernTotalSubring C sY) : TotalChowClass C sY) := by
  classical
  set K := Scheme.Modules.koszulComplex V φ
  have hK := isFiniteLocallyFreeOfRank_koszulComplex V φ r
  let u : ℤ → (TotalChowClass C sY)ˣ := fun n =>
    (let := hK n; totalChernUnit C sY (K.X n) (koszulRank r n))
  have hcomm : ∀ x ∈ Set.range u, ∀ y ∈ Set.range u, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    let := hK a
    let := hK b
    exact Units.ext (commute_totalChern C sY (K.X a) (K.X b) _ _).eq
  have := Subgroup.isMulCommutative_closure fun a ha b hb _ => hcomm a ha b hb
  set G := Subgroup.closure (Set.range u)
  have hmem : ∀ n, complexChernFactor C sY K (koszulRank r) hK n ∈ G := fun n =>
    Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_range_self (f := u) n)) _
  let g : ℤ → G := fun n => ⟨_, hmem n⟩
  let c' : ℕ → G := fun m => ⟨u (-(m : ℤ)), Subgroup.subset_closure (Set.mem_range_self _)⟩
  have hP : complexChernBounded C sY K (koszulRank r) hK =
      (((∏ n ∈ Finset.Icc (-(r : ℤ)) 0, g n : G) : (TotalChowClass C sY)ˣ) :
        TotalChowClass C sY) := by
    rw [complexChernBounded_eq_prod C sY K (koszulRank r) hK (Finset.Icc (-(r : ℤ)) 0)
      (fun n hn => Finsupp.notMem_support_iff.1 fun h => hn (Finsupp.support_onFinset_subset h)),
      complexChernProd]
    congr 1
    rw [← Finset.prod_map_toList,
      ← ((Finset.sort_perm_toList (Finset.Icc (-(r : ℤ)) 0) (· ≤ ·)).map g).prod_eq,
      ← Subgroup.coe_subtype, map_list_prod, List.map_map]
    rfl
  have hwin : (∏ n ∈ Finset.Icc (-(r : ℤ)) 0, g n) =
      (∏ m ∈ (range (r + 1)).filter Even, c' m) *
        (∏ m ∈ (range (r + 1)).filter (fun m => ¬ Even m), c' m)⁻¹ := by
    have hg : ∀ m : ℕ, g (-(m : ℤ)) = c' m ^ (((-(m : ℤ)).negOnePow : ℤˣ) : ℤ) := fun m =>
      Subtype.ext (by rw [Subgroup.coe_zpow]; rfl)
    rw [Icc_neg_natCast_zero_eq_map_range r, prod_map,
      ← prod_filter_mul_prod_filter_not (range (r + 1)) Even, ← prod_inv_distrib]
    congr 1
    · refine prod_congr rfl fun m hm => ?_
      have he : Even (m : ℤ) := (Int.even_coe_nat m).2 (mem_filter.1 hm).2
      refine (hg m).trans ?_
      rw [Int.negOnePow_neg, Int.negOnePow_even _ he,
        Units.val_one, zpow_one]
    · refine prod_congr rfl fun m hm => ?_
      have ho : Odd (m : ℤ) := (Int.odd_coe_nat m).2 (Nat.not_even_iff_odd.1 (mem_filter.1 hm).2)
      refine (hg m).trans ?_
      rw [Int.negOnePow_neg, Int.negOnePow_odd _ ho,
        Units.val_neg, Units.val_one, zpow_neg_one]
  have hsub : ∀ S : Finset ℕ, S ⊆ range (r + 1) →
      ((∏ m ∈ S, (let := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower V r m
          chernTotal C sY (Scheme.Modules.exteriorPower V (m : ℤ)) (r.choose m)) :
          chernTotalSubring C sY) : TotalChowClass C sY) =
        (((∏ m ∈ S, c' m : G) : (TotalChowClass C sY)ˣ) : TotalChowClass C sY) := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; simp
    | insert a S ha ih =>
        intro hS
        rw [prod_insert ha, prod_insert ha, Subring.coe_mul, Subgroup.coe_mul, Units.val_mul,
          ih ((subset_insert a S).trans hS)]
        congr 1
        have har : a ≤ r := Nat.lt_succ_iff.1 (mem_range.1 (hS (mem_insert_self a S)))
        exact (totalChern_koszulComplex_X C sY V φ r a har).symm
  rw [hP, hwin, altChernOdd, altChernEven, hsub _ (filter_subset (fun m => ¬ Even m) _),
    hsub _ (filter_subset Even _), ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel_right]

open scoped IsMulCommutative in
/-- The degree-`0` component of a product of total Chern classes is `1`. -/
theorem apply_zero_prod_chernTotal (S : Finset ℕ) :
    ((∏ m ∈ S, (letI := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower V r m
        chernTotal C sY (Scheme.Modules.exteriorPower V (m : ℤ)) (r.choose m)) :
        chernTotalSubring C sY) : TotalChowClass C sY) 0 = (1 : TotalChowClass C sY) 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [prod_empty, Subring.coe_one]
  | insert a S ha ih =>
      rw [prod_insert ha, Subring.coe_mul]
      let := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower V r a
      exact TotalChowClass.mul_apply_zero_eq_one
        (totalChern_apply_zero C sY (Scheme.Modules.exteriorPower V (a : ℤ)) (r.choose a)) ih

/-- The components of `c(K) - 1` in the degrees `≤ r` are those of `c_+ - c_-`. -/
theorem homComponent_complexChernBounded_koszulComplex_sub_one {t : ℕ} (ht : t ≤ r) :
    TotalChowClass.homComponent t
        (complexChernBounded C sY (Scheme.Modules.koszulComplex V φ) (koszulRank r)
          (isFiniteLocallyFreeOfRank_koszulComplex V φ r) - 1) =
      TotalChowClass.homComponent t
        ((altChernEven C sY V r - altChernOdd C sY V r : chernTotalSubring C sY) :
          TotalChowClass C sY) := by
  rw [AddSubgroupClass.coe_sub]
  refine TotalChowClass.homComponent_sub_one_eq_of_mul_eq
    (complexChernBounded_koszulComplex_mul C sY V φ r)
    (TotalChowClass.homComponent_zero_of_apply_zero (apply_zero_prod_chernTotal C sY V r _))
    (fun s hs => ?_) t ht
  rw [← AddSubgroupClass.coe_sub]
  exact homComponent_altChern_sub_of_lt C sY V r hs

/-- **[Stacks, Tag 0FEE] for the Koszul complex, below the rank**: for `0 < t < r` the degree-`t`
component of the total Chern class of the Koszul complex of `φ : 𝒱 ⟶ 𝒪_Y`, `𝒱` of rank `r`,
vanishes. -/
theorem homComponent_complexChernBounded_koszulComplex_of_lt {t : ℕ} (ht0 : 0 < t)
    (ht : t < r) :
    TotalChowClass.homComponent t
        (complexChernBounded C sY (Scheme.Modules.koszulComplex V φ) (koszulRank r)
          (isFiniteLocallyFreeOfRank_koszulComplex V φ r)) = 0 := by
  have h := homComponent_complexChernBounded_koszulComplex_sub_one C sY V φ r ht.le
  rw [map_sub, TotalChowClass.homComponent_one, if_neg (by omega), sub_zero] at h
  exact h.trans (homComponent_altChern_sub_of_lt C sY V r ht)

/-- **[Stacks, Tag 0FEE] for the Koszul complex, in the degree of the rank**: the degree-`r`
component of the total Chern class of the Koszul complex of `φ : 𝒱 ⟶ 𝒪_Y`, `𝒱` of rank `r ≥ 1`,
is `-(r - 1)! c_r(𝒱)`. -/
theorem homComponent_complexChernBounded_koszulComplex_rank (hr : r ≠ 0) :
    TotalChowClass.homComponent r
        (complexChernBounded C sY (Scheme.Modules.koszulComplex V φ) (koszulRank r)
          (isFiniteLocallyFreeOfRank_koszulComplex V φ r)) =
      -((r - 1).factorial • TotalChowClass.homComponent r (totalChern C sY V r)) := by
  have h := homComponent_complexChernBounded_koszulComplex_sub_one C sY V φ r le_rfl
  rw [map_sub, TotalChowClass.homComponent_one, if_neg hr, sub_zero] at h
  exact h.trans (homComponent_altChern_sub_rank C sY V r hr)

end Koszul

end Stacks.Chow
