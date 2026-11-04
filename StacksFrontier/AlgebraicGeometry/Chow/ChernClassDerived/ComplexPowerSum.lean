module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ComplexChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ChernCommutation
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TwistFormula
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleComm
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.NewtonAdditivity
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.NewtonAdditivity

/-!
# Newton's power sums of the homogeneous components of a total class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `Y` be locally of
finite type over `S`. This file collects the algebra of Newton's power sums
`P_p(c_1, …, c_p)` (Stacks 0F9B) of the homogeneous components of a total class
`c ∈ ∏_{p ≥ 0} A^p(Y)`, read in the non-commutative ring of total classes: Newton's recursion
`AlgebraicGeometry.newtonPowerSum` with degree-zero term `0`.

* `Stacks.Chow.TotalChowClass.newtonComponents_mul` — **additivity**: for total classes `c, d`
  with degree-zero component `1` whose homogeneous components commute,
  `P_p(cd) = P_p(c) + P_p(d)` (Stacks 0F9C in algebraic form,
  `Stacks.Chow.TotalChowClass.newtonPowerSum_mul_of_commute_homComponent`), and its versions for
  inverses and ordered products.
* `Stacks.Chow.TotalChowClass.commute_homComponent_totalChern` — the Chern classes of finite
  locally free modules commute (from the commutation of their cap products, Stacks 02U6/0B7G).

The power sums `P_p(ℰ)` of a finite locally free module and `P_p(ℰ^•)` of a locally bounded
complex are `Stacks.Chow.modulePowerSum` and `Stacks.Chow.complexPowerSumComponent`; the
convolution formula for the homogeneous components of a product and the components of `1` are
`Stacks.Chow.TotalChowClass.homComponent_mul` and `Stacks.Chow.TotalChowClass.homComponent_one`
of `StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ChernCommutation`.

## Main definitions

* `Stacks.Chow.TotalChowClass.homSeries` — a total class as the power series of its homogeneous
  components, a ring homomorphism.
* `Stacks.Chow.TotalChowClass.newtonComponents` — Newton's power sums of the homogeneous
  components of a total class.

## References

* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
* [Stacks Project, Tag 0F9C](https://stacks.math.columbia.edu/tag/0F9C)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Finset PowerSeries

universe u

namespace Stacks.Chow

namespace TotalChowClass

variable {C : ChowSituation.{u}} {Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]

/-- **A total class as the power series of its homogeneous components**, a ring homomorphism to
the power series over the ring of total classes. -/
def homSeries : TotalChowClass C sY →+* (TotalChowClass C sY)⟦X⟧ where
  toFun c := mk fun i ↦ homComponent i c
  map_one' := by
    ext n
    rw [coeff_mk, homComponent_one, coeff_one]
  map_mul' c d := by
    ext n
    rw [coeff_mk, homComponent_mul, coeff_mul,
      ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j ↦ homComponent j c * homComponent i d) n, ← Finset.Nat.sum_antidiagonal_swap]
    simp only [Prod.fst_swap, Prod.snd_swap, coeff_mk]
  map_zero' := by ext n; simp
  map_add' c d := by ext n; simp

/-- The `i`-th coefficient of `homSeries c` is the homogeneous component of degree `i` of `c`. -/
@[simp]
theorem coeff_homSeries (c : TotalChowClass C sY) (i : ℕ) :
    coeff i (homSeries c) = homComponent i c :=
  show coeff i (mk fun i ↦ homComponent i c) = _ from coeff_mk _ _

variable (C sY) in
/-- **The homogeneous components of the Chern classes of finite locally free modules commute**:
for `ℰ` of rank `r` and `ℱ` of rank `s`, `c_i(ℰ) c_j(ℱ) = c_j(ℱ) c_i(ℰ)`. -/
theorem commute_homComponent_totalChern (F : Y.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    (F' : Y.Modules) (s : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F' s] (i j : ℕ) :
    Commute (homComponent i (totalChern C sY F r)) (homComponent j (totalChern C sY F' s)) := by
  show _ * _ = _ * _
  refine ext_op fun g _ ↦ ?_
  rw [op_mul, op_mul, op_homComponent, op_homComponent]
  have hu := Stacks.Chow.isHomogeneous_homComponent i ((totalChern C sY F r).op g)
  have hv := Stacks.Chow.isHomogeneous_homComponent j ((totalChern C sY F' s).op g)
  funext k m
  refine AddMonoidHom.ext fun α ↦ ?_
  by_cases hm : m = i + j
  · subst hm
    rw [gradedCap_mul_apply_of_isHomogeneous_right hv _ k (by omega),
      gradedCap_mul_apply_of_isHomogeneous_right hu _ k (by omega),
      capTo_congr_index _ (show i + j - j = i by omega),
      capTo_congr_index _ (show i + j - i = j by omega), capTo_def, capTo_def,
      Stacks.Chow.homComponent_apply_self, Stacks.Chow.homComponent_apply_self,
      Stacks.Chow.homComponent_apply_self, Stacks.Chow.homComponent_apply_self]
    by_cases hi : i ≤ r
    · by_cases hj : j ≤ s
      · let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r g
        let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F' s g
        refine eq_of_heq ((gradedDegreeCast_heq _ _).trans (HEq.trans ?_
          (gradedDegreeCast_heq _ _).symm))
        rw [op_totalChern_apply C sY F' s g k ⟨j, Nat.lt_succ_of_le hj⟩ α,
          op_totalChern_apply C sY F r g _ ⟨i, Nat.lt_succ_of_le hi⟩,
          op_totalChern_apply C sY F r g k ⟨i, Nat.lt_succ_of_le hi⟩ α,
          op_totalChern_apply C sY F' s g _ ⟨j, Nat.lt_succ_of_le hj⟩]
        exact (heq_of_eq (GenuineChern.chernCap_chernCap_comm C (g ≫ sY)
          ((Scheme.Modules.pullback g).obj F) r ((Scheme.Modules.pullback g).obj F') s k
          ⟨i, Nat.lt_succ_of_le hi⟩ ⟨j, Nat.lt_succ_of_le hj⟩ α)).trans
          (chowGroupCast_heq C _ _ _)
      · rw [op_totalChern_of_lt C sY F' s g k (by omega), AddMonoidHom.zero_apply, map_zero,
          map_zero, op_totalChern_of_lt C sY F' s g _ (by omega), AddMonoidHom.zero_apply,
          map_zero]
    · rw [op_totalChern_of_lt C sY F r g k (by omega), AddMonoidHom.zero_apply, map_zero,
        map_zero, op_totalChern_of_lt C sY F r g _ (by omega), AddMonoidHom.zero_apply, map_zero]
  · rw [(hu.mul hv) k m hm, (hv.mul hu) k m (by omega)]

variable (C sY) in
/-- The homogeneous component of degree `0` of a total Chern class is `1`. -/
theorem homComponent_zero_totalChern (F : Y.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] :
    homComponent 0 (totalChern C sY F r) = 1 := by
  refine ext_op fun g _ ↦ ?_
  rw [op_homComponent, op_one]
  funext k m
  refine AddMonoidHom.ext fun α ↦ ?_
  by_cases hm : m = 0
  · subst hm
    let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r g
    rw [Stacks.Chow.homComponent_apply_self, gradedCap_one_apply_zero]
    refine eq_of_heq ((heq_of_eq (op_totalChern_apply C sY F r g k 0 α)).trans
      ((chowGroupCast_heq C _ (show k - ((0 : Fin (r + 1)) : ℕ) = k by simp) _).symm.trans ?_))
    rw [GenuineChern.chernCap_zero_apply]
    exact (gradedDegreeCast_heq _ α).symm
  · rw [Stacks.Chow.homComponent_apply_of_ne hm, gradedCap_one_of_ne hm]

/-! ### Newton's power sums of the homogeneous components -/

/-- Newton's power sums of the homogeneous components of a total class: Newton's recursion
`AlgebraicGeometry.newtonPowerSum` of Stacks 0F9B with degree-zero term `0`. -/
abbrev newtonComponents (c : TotalChowClass C sY) (p : ℕ) : TotalChowClass C sY :=
  AlgebraicGeometry.newtonPowerSum 0 (fun i : ℕ+ ↦ homComponent (i : ℕ) c) p

/-- A total class whose homogeneous component of degree `0` is `1` has degree-`0` component
that of `1`. -/
theorem apply_zero_of_homComponent_zero {c : TotalChowClass C sY} (hc : homComponent 0 c = 1) :
    c 0 = (1 : TotalChowClass C sY) 0 := by
  have h := congrFun hc 0
  rwa [homComponent_apply, if_pos rfl] at h

/-- **Additivity of the power sums of total classes** whose homogeneous components commute. -/
theorem newtonComponents_mul {c d : TotalChowClass C sY} (hc : homComponent 0 c = 1)
    (hd : homComponent 0 d = 1) (hcd : ∀ i j, Commute (homComponent i c) (homComponent j d))
    (p : ℕ) : newtonComponents (c * d) p = newtonComponents c p + newtonComponents d p := by
  have h := TotalChowClass.newtonPowerSum_mul_of_commute_homComponent
    (apply_zero_of_homComponent_zero hc)
    (apply_zero_of_homComponent_zero hd) hcd 0 0 p
  rwa [add_zero] at h

/-- An element commuting with the homogeneous components of `c` and of `d` commutes with those of
`c d`. -/
theorem commute_homComponent_mul {c d : TotalChowClass C sY} {x : TotalChowClass C sY}
    (hc : ∀ i, Commute (homComponent i c) x) (hd : ∀ i, Commute (homComponent i d) x) (n : ℕ) :
    Commute (homComponent n (c * d)) x := by
  have h := commute_coeff_mul (f := homSeries c) (g := homSeries d) (x := x)
    (fun i ↦ by rw [coeff_homSeries]; exact hc i) (fun i ↦ by rw [coeff_homSeries]; exact hd i) n
  rwa [← map_mul, coeff_homSeries] at h

/-- An element commuting with the homogeneous components of `c` commutes with those of `c⁻¹`. -/
theorem commute_homComponent_of_mul_eq_one {c d : TotalChowClass C sY}
    (hc : homComponent 0 c = 1) (hcd : c * d = 1) {x : TotalChowClass C sY}
    (h : ∀ i, Commute (homComponent i c) x) (n : ℕ) : Commute (homComponent n d) x := by
  have h' := commute_coeff_of_mul_eq_one (f := homSeries c) (g := homSeries d)
    (by rw [← coeff_zero_eq_constantCoeff_apply, coeff_homSeries, hc])
    (by rw [← map_mul, hcd, map_one]) (x := x) (fun i ↦ by rw [coeff_homSeries]; exact h i) n
  rwa [coeff_homSeries] at h'

/-- The homogeneous component of degree `0` of an inverse. -/
theorem homComponent_zero_of_mul_eq_one {c d : TotalChowClass C sY}
    (hc : homComponent 0 c = 1) (hcd : c * d = 1) : homComponent 0 d = 1 := by
  have h := congrArg (coeff 0) (congrArg homSeries hcd)
  rwa [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, map_mul, map_mul,
    map_one, map_one, ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
    coeff_homSeries, coeff_homSeries, hc, one_mul] at h

/-- The power sums of `1` vanish. -/
theorem newtonComponents_one (p : ℕ) : newtonComponents (1 : TotalChowClass C sY) p = 0 := by
  have h : (fun i : ℕ+ ↦ homComponent (i : ℕ) (1 : TotalChowClass C sY)) = 0 := by
    funext i
    rw [homComponent_one, if_neg i.ne_zero, Pi.zero_apply]
  rw [newtonComponents, h, newtonPowerSum_zero_family]

/-- **The power sums of an inverse** are the negatives of the power sums. -/
theorem newtonComponents_of_mul_eq_one {c d : TotalChowClass C sY} (hc : homComponent 0 c = 1)
    (hcd : c * d = 1) (hcc : ∀ i j, Commute (homComponent i c) (homComponent j c)) (p : ℕ) :
    newtonComponents d p = -newtonComponents c p := by
  have h := newtonComponents_mul hc (homComponent_zero_of_mul_eq_one hc hcd)
    (fun i j ↦ (commute_homComponent_of_mul_eq_one hc hcd (fun k ↦ hcc k i) j).symm) p
  rw [hcd, newtonComponents_one] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

/-- A product of total classes with homogeneous component `1` in degree `0` has homogeneous
component `1` in degree `0`. -/
theorem homComponent_zero_list_prod (l : List (TotalChowClass C sY))
    (h : ∀ c ∈ l, homComponent 0 c = 1) : homComponent 0 l.prod = 1 := by
  induction l with
  | nil => rw [List.prod_nil, homComponent_one, if_pos rfl]
  | cons a l ih =>
    rw [List.forall_mem_cons] at h
    rw [List.prod_cons, homComponent_mul, Finset.sum_range_one, Nat.sub_zero, h.1, ih h.2, one_mul]

/-- An element commuting with the homogeneous components of the members of a list commutes with
those of the product. -/
theorem commute_homComponent_list_prod (l : List (TotalChowClass C sY)) (x : TotalChowClass C sY)
    (h : ∀ c ∈ l, ∀ i, Commute (homComponent i c) x) (n : ℕ) :
    Commute (homComponent n l.prod) x := by
  induction l generalizing n with
  | nil =>
    rw [List.prod_nil, homComponent_one]
    split_ifs
    · exact Commute.one_left x
    · exact Commute.zero_left x
  | cons a l ih =>
    rw [List.forall_mem_cons] at h
    rw [List.prod_cons]
    exact commute_homComponent_mul h.1 (ih h.2) n

/-- **Additivity over a list**: the power sums of a product of total classes with homogeneous
component `1` in degree `0` and pairwise commuting homogeneous components are the sum of the
power sums of the factors. -/
theorem newtonComponents_list_prod (l : List (TotalChowClass C sY))
    (h0 : ∀ c ∈ l, homComponent 0 c = 1)
    (hcomm : ∀ c ∈ l, ∀ d ∈ l, ∀ i j, Commute (homComponent i c) (homComponent j d)) (p : ℕ) :
    newtonComponents l.prod p = (l.map fun c ↦ newtonComponents c p).sum := by
  induction l with
  | nil => rw [List.prod_nil, newtonComponents_one, List.map_nil, List.sum_nil]
  | cons c l ih =>
    rw [List.forall_mem_cons] at h0
    have hcl : ∀ c ∈ l, ∀ d ∈ l, ∀ i j, Commute (homComponent i c) (homComponent j d) :=
      fun a ha b hb ↦ hcomm a (.tail _ ha) b (.tail _ hb)
    rw [List.prod_cons, newtonComponents_mul h0.1 (homComponent_zero_list_prod l h0.2)
      (fun i j ↦ (commute_homComponent_list_prod l _ (fun d hd k ↦ (hcomm c List.mem_cons_self d
        (.tail _ hd) i k).symm) j).symm), ih h0.2 hcl, List.map_cons,
      List.sum_cons]

end TotalChowClass

end Stacks.Chow

end
