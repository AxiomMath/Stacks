module

public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.KoszulComplexChern
public import StacksCore.Tactic.StacksAttribute

/-!
# The alternating product of the Chern classes of the exterior powers: Stacks 0FEE

Let `(S, δ)` be as in Situation 02QL, let `Y` be locally of finite type over `S` and let `ℰ` be a
finite locally free `𝒪_Y`-module of rank `r ≥ 1`. [Stacks, Tag 0FEE] asserts

  `∏_{n = 0, …, r} c(⋀ⁿ ℰ)^{(-1)ⁿ} = 1 - (r - 1)! c_r(ℰ) + …`.

Here every term is the library's own: `c(⋀ⁿ ℰ)` is the total Chern class `Stacks.Chow.totalChern`
of the exterior power, whose degree-`j` component is the bivariant Chern class `c_j(⋀ⁿ ℰ)` of
Stacks 0B7H (`Stacks.Chow.GenuineChern.chernClass`), and the product is taken in the ring
`Stacks.Chow.TotalChowClass` of total Chow cohomology classes `∏_{p ≥ 0} A^p(Y)`, where a class
`1 + c_1 + c_2 + ⋯` is a unit (`Stacks.Chow.totalChernUnit`). That ring is not claimed to be
commutative, so the alternating product is the ordered product over `n = 0, 1, …, r`
(`Stacks.Chow.exteriorPowerChernAltProd`); its factors commute (Stacks 02UA, through
`Stacks.Chow.commute_totalChern`), so the order is immaterial. The `+ …` of the source stands for
terms of degree `> r`, about which the source's proof — "the first nonzero term in our Chern class
is in degree `r` and equal to the predicted value" — says nothing; the statement proved is that
the alternating product and `1 - (r - 1)! c_r(ℰ)` have the same homogeneous components in every
degree `≤ r`.

## The proof

Write `c_± = ∏_{n even/odd} c(⋀ⁿ ℰ)` (`Stacks.Chow.altChernEven`, `Stacks.Chow.altChernOdd`).
The factors commute, so the alternating product `P` satisfies `P c_- = c_+`
(`Stacks.Chow.exteriorPowerChernAltProd_mul_altChernOdd`), hence `(P - 1) c_- = c_+ - c_-`; as
`c_-` has degree-`0` component `1`, `P - 1` and `c_+ - c_-` agree in the degrees `≤ r` as soon as
`c_+ - c_-` vanishes below `r` (`Stacks.Chow.TotalChowClass.homComponent_sub_one_eq_of_mul_eq`).

The components of `c_+ - c_-` in the degrees `≤ r` are those of the source's computation,
`Stacks.Chow.homComponent_altChern_sub_of_lt` and `Stacks.Chow.homComponent_altChern_sub_rank`,
and these are proved by the splitting principle, not assumed:

* **Stacks 02UL.** On every test scheme `g : T ⟶ Y` the splitting morphism of
  `Stacks.Chow.exists_splittingMorphism_basechange_unconditional` gives a flat `π : P ⟶ T` with
  injective flat pullback on Chow groups along which `π^* g^* ℰ` has a filtration with invertible
  successive quotients `ℒ_1, …, ℒ_r`; flat pullback carries `c(⋀ⁿ g^*ℰ)` to `c(⋀ⁿ π^* g^*ℰ)`
  (Stacks 02U8, `Stacks.Chow.GenuineChern.intertwines_chernFamily`), and a total class is
  determined by its operations on the test schemes (`Stacks.Chow.TotalChowClass.ext_op`).
* **Stacks 02UJ, 02UI.** For the filtered module the Chern roots of `⋀ⁿ` are the sums of `n`
  distinct roots `x_i = c_1(ℒ_i)`,
  `c(⋀ⁿ ℰ) = ∏_{i_1 < ⋯ < i_n} (1 + x_{i_1} + ⋯ + x_{i_n})`
  (`Stacks.Chow.totalChern_exteriorPower_of_hasQuotients`), by induction along the filtration
  with the Whitney formula of Stacks 02UI
  (`Stacks.Chow.GenuineChern.chernFamily_eq_mul_of_shortExact`) and the twist formula of Stacks
  02UD.
* The comparison of elementary symmetric functions of the subset sums of even and odd
  cardinality, `AlgebraicGeometry.subsetSumEsymm_even_eq_odd` and
  `AlgebraicGeometry.subsetSumEsymm_even_sub_odd`, replaces the source's logarithm.

## Main definitions

* `Stacks.Chow.exteriorPowerChernUnit` — `c(⋀ⁿ ℰ)` as a unit of the ring of total classes.
* `Stacks.Chow.exteriorPowerChernAltProd` — `∏_{n = 0}^{r} c(⋀ⁿ ℰ)^{(-1)ⁿ}`.

## Main results

* `Stacks.Chow.exteriorPowerChernAltProd_mul_altChernOdd` — `P c_- = c_+`.
* `Stacks.Chow.homComponent_exteriorPowerChernAltProd` — **Stacks 0FEE.**
* `Stacks.Chow.homComponent_exteriorPowerChernAltProd_zero`,
  `Stacks.Chow.homComponent_exteriorPowerChernAltProd_of_lt`,
  `Stacks.Chow.homComponent_exteriorPowerChernAltProd_rank` — its three readings: `1` in degree
  `0`, `0` in the degrees `1, …, r - 1`, `-(r - 1)! c_r(ℰ)` in degree `r`.

## References

* [Stacks Project, Tag 0FEE](https://stacks.math.columbia.edu/tag/0FEE)
* [Stacks Project, Tag 02UK](https://stacks.math.columbia.edu/tag/02UK)
* [Stacks Project, Tag 02UL](https://stacks.math.columbia.edu/tag/02UL)
* [Stacks Project, Tag 02UJ](https://stacks.math.columbia.edu/tag/02UJ)
* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Finset

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (V : Y.Modules) (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} V r]

/-- **The total Chern class `c(⋀ⁿ ℰ)`** of the `n`-th exterior power of a finite locally free
module `ℰ` of rank `r`, as a unit of the ring of total Chow cohomology classes; `⋀ⁿ ℰ` has rank
`binom(r, n)`. -/
def exteriorPowerChernUnit (n : ℕ) : (TotalChowClass C sY)ˣ :=
  letI := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower V r n
  totalChernUnit C sY (Scheme.Modules.exteriorPower V (n : ℤ)) (r.choose n)

/-- The unit `c(⋀ⁿ ℰ)` is the total Chern class of `⋀ⁿ ℰ`. -/
theorem val_exteriorPowerChernUnit (n : ℕ) :
    (exteriorPowerChernUnit C sY V r n : TotalChowClass C sY) =
      letI := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower V r n
      totalChern C sY (Scheme.Modules.exteriorPower V (n : ℤ)) (r.choose n) :=
  rfl

/-- **The alternating product `∏_{n = 0}^{r} c(⋀ⁿ ℰ)^{(-1)ⁿ}`** of the total Chern classes of
the exterior powers of a finite locally free module `ℰ` of rank `r`, in the group of units of the
ring of total Chow cohomology classes. The ring is not claimed to be commutative, so this is the
ordered product over `n = 0, 1, …, r`; its factors commute. -/
def exteriorPowerChernAltProd : (TotalChowClass C sY)ˣ :=
  ((List.range (r + 1)).map fun n => exteriorPowerChernUnit C sY V r n ^ ((-1 : ℤ) ^ n)).prod

open scoped IsMulCommutative in
/-- **`P c_- = c_+`**: the alternating product `P = ∏_{n} c(⋀ⁿ ℰ)^{(-1)ⁿ}`, multiplied by the
product `c_-` of the `c(⋀ⁿ ℰ)` over odd `n`, is the product `c_+` over even `n`. The factors
commute (`Stacks.Chow.commute_totalChern`), so the products may be formed in the commutative
subgroup of units they generate. -/
theorem exteriorPowerChernAltProd_mul_altChernOdd :
    (exteriorPowerChernAltProd C sY V r : TotalChowClass C sY) *
        ((altChernOdd C sY V r : chernTotalSubring C sY) : TotalChowClass C sY) =
      ((altChernEven C sY V r : chernTotalSubring C sY) : TotalChowClass C sY) := by
  classical
  set u := exteriorPowerChernUnit C sY V r with hu
  have hcomm : ∀ x ∈ Set.range u, ∀ y ∈ Set.range u, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    let := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower V r a
    let := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower V r b
    exact Units.ext (commute_totalChern C sY _ _ _ _).eq
  have := Subgroup.isMulCommutative_closure hcomm
  set G := Subgroup.closure (Set.range u) with hG
  let c' : ℕ → G := fun m => ⟨u m, Subgroup.subset_closure (Set.mem_range_self _)⟩
  -- the ordered product is the product in the commutative group `G`
  have hP : exteriorPowerChernAltProd C sY V r =
      ((∏ n ∈ range (r + 1), c' n ^ ((-1 : ℤ) ^ n) : G) : (TotalChowClass C sY)ˣ) := by
    rw [← List.toFinset_range, List.prod_toFinset _ List.nodup_range, ← Subgroup.coe_subtype,
      map_list_prod, List.map_map]
    rfl
  -- the even and the odd factors
  have hwin : (∏ n ∈ range (r + 1), c' n ^ ((-1 : ℤ) ^ n)) =
      (∏ m ∈ (range (r + 1)).filter Even, c' m) *
        (∏ m ∈ (range (r + 1)).filter (fun m => ¬ Even m), c' m)⁻¹ := by
    rw [← prod_filter_mul_prod_filter_not (range (r + 1)) Even, ← prod_inv_distrib]
    congr 1
    · refine prod_congr rfl fun m hm => ?_
      rw [Even.neg_one_pow (mem_filter.1 hm).2, zpow_one]
    · refine prod_congr rfl fun m hm => ?_
      rw [Odd.neg_one_pow (Nat.not_even_iff_odd.1 (mem_filter.1 hm).2), zpow_neg_one]
  -- the products of total Chern classes over a set of exterior degrees
  have hsub : ∀ S : Finset ℕ,
      ((∏ m ∈ S, (let := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower V r m
          chernTotal C sY (Scheme.Modules.exteriorPower V (m : ℤ)) (r.choose m)) :
          chernTotalSubring C sY) : TotalChowClass C sY) =
        (((∏ m ∈ S, c' m : G) : (TotalChowClass C sY)ˣ) : TotalChowClass C sY) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
        rw [prod_insert ha, prod_insert ha, Subring.coe_mul, Subgroup.coe_mul, Units.val_mul, ih]
        rfl
  rw [hP, hwin, altChernOdd, altChernEven, hsub, hsub, ← Units.val_mul, ← Subgroup.coe_mul,
    inv_mul_cancel_right]

/-- The degree-`t` component of `1 - (r - 1)! c_r(ℰ)`. -/
private theorem homComponent_one_sub_factorial_smul (t : ℕ) :
    TotalChowClass.homComponent t
        (1 - (r - 1).factorial • TotalChowClass.homComponent r (totalChern C sY V r)) =
      TotalChowClass.homComponent t (1 : TotalChowClass C sY) -
        if t = r then (r - 1).factorial • TotalChowClass.homComponent r (totalChern C sY V r)
        else 0 := by
  rw [map_sub, map_nsmul,
    (TotalChowClass.isHomogeneous_homComponent r (totalChern C sY V r)).homComponent_eq_ite t,
    smul_ite, smul_zero]

/-- **Stacks 0FEE.** For a finite locally free module `ℰ` of rank `r ≥ 1` on `Y`, the alternating
product `∏_{n = 0}^{r} c(⋀ⁿ ℰ)^{(-1)ⁿ}` of the total Chern classes of its exterior powers, in the
ring `∏_{p ≥ 0} A^p(Y)` of total Chow cohomology classes, agrees with `1 - (r - 1)! c_r(ℰ)` in
every degree `≤ r`. The `+ …` of the source is the part in degrees `> r`, on which nothing is
asserted. -/
@[stacks 0FEE "the whole lemma, for the library's Chern classes: c(wedge^n E) is the total \
  Chern class totalChern of Stacks 0B7H, the product is the ordered product of units in the ring \
  TotalChowClass = prod_{p >= 0} A^p(Y) of total Chow cohomology classes, and '= 1 - (r-1)! c_r(E) \
  + ...' is the equality of homogeneous components in every degree <= r. The splitting principle \
  is proved, not assumed: Stacks 02UL via exists_splittingMorphism_basechange_unconditional, the \
  Chern roots of the exterior powers via 02UI and 02UJ (totalChern_exteriorPower_of_hasQuotients)"]
theorem homComponent_exteriorPowerChernAltProd (hr : r ≠ 0) {t : ℕ} (ht : t ≤ r) :
    TotalChowClass.homComponent t (exteriorPowerChernAltProd C sY V r : TotalChowClass C sY) =
      TotalChowClass.homComponent t
        (1 - (r - 1).factorial • TotalChowClass.homComponent r (totalChern C sY V r)) := by
  have h := TotalChowClass.homComponent_sub_one_eq_of_mul_eq
    (exteriorPowerChernAltProd_mul_altChernOdd C sY V r)
    (TotalChowClass.homComponent_zero_of_apply_zero (apply_zero_prod_chernTotal C sY V r _))
    (fun s hs => by
      rw [← AddSubgroupClass.coe_sub]
      exact homComponent_altChern_sub_of_lt C sY V r hs) t ht
  rw [← AddSubgroupClass.coe_sub, map_sub, sub_eq_iff_eq_add] at h
  rw [h, homComponent_one_sub_factorial_smul]
  rcases lt_or_eq_of_le ht with hlt | rfl
  · rw [homComponent_altChern_sub_of_lt C sY V r hlt, ite_eq_right hlt.ne, sub_zero, zero_add]
  · rw [homComponent_altChern_sub_rank C sY V t hr, ite_eq_left rfl,
      TotalChowClass.homComponent_one, ite_eq_right hr, zero_sub, add_zero]

/-- **Stacks 0FEE in degree `0`**: the degree-`0` component of `∏_{n} c(⋀ⁿ ℰ)^{(-1)ⁿ}` is `1`. -/
theorem homComponent_exteriorPowerChernAltProd_zero (hr : r ≠ 0) :
    TotalChowClass.homComponent 0 (exteriorPowerChernAltProd C sY V r : TotalChowClass C sY) =
      1 := by
  rw [homComponent_exteriorPowerChernAltProd C sY V r hr (Nat.zero_le r),
    homComponent_one_sub_factorial_smul, ite_eq_right (Ne.symm hr), sub_zero,
    TotalChowClass.homComponent_one, ite_eq_left rfl]

/-- **Stacks 0FEE below the rank**: for `0 < t < r` the degree-`t` component of
`∏_{n} c(⋀ⁿ ℰ)^{(-1)ⁿ}` vanishes. -/
theorem homComponent_exteriorPowerChernAltProd_of_lt {t : ℕ} (ht0 : 0 < t) (ht : t < r) :
    TotalChowClass.homComponent t (exteriorPowerChernAltProd C sY V r : TotalChowClass C sY) =
      0 := by
  rw [homComponent_exteriorPowerChernAltProd C sY V r (by omega) ht.le,
    homComponent_one_sub_factorial_smul, ite_eq_right ht.ne, sub_zero,
    TotalChowClass.homComponent_one,
    ite_eq_right ht0.ne']

/-- **Stacks 0FEE in the degree of the rank**: the degree-`r` component of
`∏_{n} c(⋀ⁿ ℰ)^{(-1)ⁿ}` is `-(r - 1)! c_r(ℰ)`. -/
theorem homComponent_exteriorPowerChernAltProd_rank (hr : r ≠ 0) :
    TotalChowClass.homComponent r (exteriorPowerChernAltProd C sY V r : TotalChowClass C sY) =
      -((r - 1).factorial • TotalChowClass.homComponent r (totalChern C sY V r)) := by
  rw [homComponent_exteriorPowerChernAltProd C sY V r hr le_rfl,
    homComponent_one_sub_factorial_smul, ite_eq_left rfl, TotalChowClass.homComponent_one,
    ite_eq_right hr, zero_sub]

end Stacks.Chow

end
