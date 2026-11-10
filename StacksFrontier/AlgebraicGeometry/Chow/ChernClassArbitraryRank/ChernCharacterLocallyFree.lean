module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.BivariantPowerSumShortExact
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.ChernCharacter
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.ChernPolynomial
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.ChernProductVanishing
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.LocallyFreeRemark
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.ChernRootPowerSums
import StacksCore.Tactic.StacksAttribute

/-!
# The Chern character of a finite locally free module of arbitrary rank (Stacks 0ESX)

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S` and let `ℰ` be a
finite locally free `𝒪_X`-module whose rank need not be constant. The degree `p` component of the
Chern character of `ℰ` is

  `ch_p(ℰ) = P_p(ℰ)/p! ∈ A^p(X) ⊗ 𝐐`,

where `P_p ∈ 𝐙[r, c_1, c_2, …]` is the power sum of Stacks 0F9B (with `P_0 = r`) and `P_p(ℰ)` is
its value at the rank `r(ℰ)` and the Chern classes `c_i(ℰ)` of Stacks 0ESW, as in Stacks 0FA7
(`Stacks.Chow.chernPolynomialComponent`). **Stacks 0ESX** records that the full Chern character
`ch(ℰ) = (ch_0(ℰ), ch_1(ℰ), …)` is therefore an element of `∏_{p ≥ 0} (A^p(X) ⊗ 𝐐)`, and that if
`X` is quasi-compact and of finite dimension then `ch(ℰ) ∈ A^*(X) ⊗ 𝐐 = ⊕_{p ≥ 0} (A^p(X) ⊗ 𝐐)`.

## The finite-dimensional statement

If `X` is quasi-compact the rank of `ℰ` is bounded, say by `R`, so `c_i(ℰ) = 0` for `i > R`; and if
`dim X < m`, every product of `m` Chern classes of positive degree vanishes
(`Stacks.Chow.list_prod_homComponent_totalChernClassOfModule_eq_zero`, proved in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.ChernProductVanishing` by restricting
to a dense open on which `ℰ` is free and to its complement, of smaller dimension). A monomial of
weighted degree `p` in `c_1, …, c_R` has at least `p / R` factors, so `P_p(ℰ) = 0` as soon as
`p ≥ R m`, and `ch(ℰ)` has only finitely many nonzero components. This replaces the appeal of the
source to Stacks 0FDX and the splitting principle, and needs no ample invertible module on `X`.

## Main results

* `Stacks.Chow.modulePowerSumArbitraryRank_eq_chernPolynomialClass` — the power sum `P_p(ℰ)` glued
  from the rank loci is `P_p(r(ℰ), c_1(ℰ), c_2(ℰ), …)` in the sense of Stacks 0FA7.
* `Stacks.Chow.moduleChernCharacter_apply_eq` — **Stacks 0ESX**: the Chern character
  `Stacks.Chow.moduleChernCharacter` of `ℰ`, an element of `∏_{p ≥ 0} (A^p(X) ⊗ 𝐐)`, has components
  `ch_p(ℰ) = P_p(ℰ)/p!`.
* `Stacks.Chow.exists_chernPolynomialClass_powerSumChernPolynomial_eq_zero` — for `X`
  quasi-compact of finite dimension, `P_p(ℰ) = 0` for all large `p`.
* `Stacks.Chow.exists_gradedRationalChowCohomology_eq_moduleChernCharacter` —
  **Stacks 0ESX**: `ch(ℰ) ∈ A^*(X) ⊗ 𝐐` for `X` quasi-compact of finite dimension.

## References

* [Stacks Project, Tag 0ESX](https://stacks.math.columbia.edu/tag/0ESX)
* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
* [Stacks Project, Tag 0FA7](https://stacks.math.columbia.edu/tag/0FA7)
* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
* [Stacks Project, Tag 0FDX](https://stacks.math.columbia.edu/tag/0FDX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-! ### Products of Chern classes of a module of arbitrary rank -/

section Products

/-- **Products of Chern classes vanish above the dimension, in arbitrary rank.** If `X` is
quasi-compact of dimension `< m`, every product `c_{i_1}(ℰ) ⋯ c_{i_m}(ℰ)` of `m` Chern classes of
positive degree of a finite locally free module of arbitrary rank vanishes: on each rank locus it
is a product of Chern classes of a module of constant rank. -/
theorem list_prod_homComponent_totalChernClassOfModule_eq_zero [CompactSpace X] (m : ℕ)
    (hdim : topologicalKrullDim X < (m : WithBot ℕ∞)) (f : Fin m → ℕ+) :
    (List.ofFn fun j ↦
      TotalChowClass.homComponent (f j : ℕ) (totalChernClassOfModule C sX E)).prod = 0 := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsNoetherian X := {}
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_rankLociFamily E) fun ρ ↦ ?_
  rw [map_list_prod, map_zero, List.map_ofFn]
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (rankLociFamily E ρ).ι).obj E) ρ.down :=
    isFiniteLocallyFreeOfRank_pullback_rankLociFamily E ρ
  have : NoetherianSpace (rankLociFamily E ρ : Scheme.{u}) :=
    inferInstanceAs (NoetherianSpace ((rankLociFamily E ρ : Set X)))
  have hdimρ : topologicalKrullDim (rankLociFamily E ρ : Scheme.{u}) < (m : WithBot ℕ∞) :=
    (topologicalKrullDim_subspace_le X (rankLociFamily E ρ : Set X)).trans_lt hdim
  refine Eq.trans ?_ (list_prod_homComponent_totalChern_eq_zero C m
    ((rankLociFamily E ρ).ι ≫ sX) hdimρ ((Scheme.Modules.pullback (rankLociFamily E ρ).ι).obj E)
    ρ.down f)
  congr 1
  refine List.ofFn_inj.2 (funext fun j ↦ ?_)
  change TotalChowClass.res _ rfl (TotalChowClass.homComponent _ _) = _
  rw [TotalChowClass.res_homComponent, res_totalChernClassOfModule_rankLocus]

/-- The list form: a product of at least `m` Chern classes of positive degree vanishes when
`X` is quasi-compact of dimension `< m`. -/
theorem list_prod_eq_zero_of_le_length [CompactSpace X] {m : ℕ}
    (hdim : topologicalKrullDim X < (m : WithBot ℕ∞)) (l : List (TotalChowClass C sX))
    (hl : ∀ x ∈ l, ∃ i : ℕ+,
      x = TotalChowClass.homComponent (i : ℕ) (totalChernClassOfModule C sX E))
    (hlen : m ≤ l.length) : l.prod = 0 := by
  rw [← List.take_append_drop m l, List.prod_append]
  set l' := l.take m with hl'def
  have hl'len : l'.length = m := by simp [l', hlen]
  have hl' : ∀ j : Fin l'.length, ∃ i : ℕ+,
      l'.get j = TotalChowClass.homComponent (i : ℕ) (totalChernClassOfModule C sX E) :=
    fun j ↦ hl _ (List.mem_of_mem_take (List.get_mem _ _))
  choose f hf using hl'
  have hdim' : topologicalKrullDim X < (l'.length : WithBot ℕ∞) := by
    rw [hl'len]
    exact hdim
  have hprod : l'.prod = 0 := by
    calc l'.prod = (List.ofFn l'.get).prod := by rw [List.ofFn_get]
      _ = (List.ofFn fun j ↦
            TotalChowClass.homComponent (f j : ℕ) (totalChernClassOfModule C sX E)).prod := by
          rw [funext hf]
      _ = 0 := list_prod_homComponent_totalChernClassOfModule_eq_zero C sX E l'.length hdim' f
  rw [hprod, zero_mul]

/-- **The Chern classes of `ℰ` vanish above the rank.** On a quasi-compact `X` the rank of `ℰ` is
bounded, and `c_i(ℰ) = 0` for every `i` above the bound. -/
theorem exists_homComponent_totalChernClassOfModule_eq_zero [CompactSpace X] :
    ∃ R : ℕ, ∀ i : ℕ, R < i →
      TotalChowClass.homComponent i (totalChernClassOfModule C sX E) = 0 := by
  obtain ⟨R, hR⟩ := (moduleRank E).range_finite.bddAbove
  refine ⟨R, fun i hi ↦ ?_⟩
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_rankLociFamily E) fun ρ ↦ ?_
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (rankLociFamily E ρ).ι).obj E) ρ.down :=
    isFiniteLocallyFreeOfRank_pullback_rankLociFamily E ρ
  rw [map_zero, TotalChowClass.res_homComponent, res_totalChernClassOfModule_rankLocus]
  rcases isEmpty_or_nonempty (rankLociFamily E ρ : Scheme.{u}) with h | ⟨⟨x⟩⟩
  · have := TotalChowClass.subsingleton_of_isEmpty (C := C) ((rankLociFamily E ρ).ι ≫ sX)
    exact Subsingleton.elim _ _
  · have hρ : ρ.down ≤ R := hR ⟨x.1, (mem_rankLocus E).1 x.2⟩
    refine TotalChowClass.ext fun p ↦ ?_
    rw [TotalChowClass.homComponent_apply]
    split_ifs with hp
    · subst hp
      exact totalChern_apply_of_lt C _ _ _ (by omega)
    · rfl

end Products

/-! ### Products of at least `n` Chern classes -/

section Filtration

/-- The additive subgroup of `∏_{p ≥ 0} A^p(X)` generated by the products of at least `n` Chern
classes of positive degree of `ℰ`. -/
def chernProductSubgroup (n : ℕ) : AddSubgroup (TotalChowClass C sX) :=
  AddSubgroup.closure {y | ∃ l : List (TotalChowClass C sX),
    (∀ x ∈ l, ∃ i : ℕ+,
      x = TotalChowClass.homComponent (i : ℕ) (totalChernClassOfModule C sX E)) ∧
    n ≤ l.length ∧ y = l.prod}

/-- A product of at least `n` Chern classes lies in the subgroup. -/
theorem list_prod_mem_chernProductSubgroup {n : ℕ} (l : List (TotalChowClass C sX))
    (hl : ∀ x ∈ l, ∃ i : ℕ+,
      x = TotalChowClass.homComponent (i : ℕ) (totalChernClassOfModule C sX E))
    (hlen : n ≤ l.length) : l.prod ∈ chernProductSubgroup C sX E n :=
  AddSubgroup.subset_closure ⟨l, hl, hlen, rfl⟩

/-- The subgroups decrease with `n`. -/
theorem chernProductSubgroup_antitone {m n : ℕ} (h : m ≤ n) :
    chernProductSubgroup C sX E n ≤ chernProductSubgroup C sX E m :=
  AddSubgroup.closure_mono fun _ ⟨l, hl, hlen, hy⟩ ↦ ⟨l, hl, h.trans hlen, hy⟩

/-- The product of an element of the `m`-th and of the `n`-th subgroup lies in the
`(m + n)`-th. -/
theorem mul_mem_chernProductSubgroup {m n : ℕ} {a b : TotalChowClass C sX}
    (ha : a ∈ chernProductSubgroup C sX E m) (hb : b ∈ chernProductSubgroup C sX E n) :
    a * b ∈ chernProductSubgroup C sX E (m + n) := by
  induction ha using AddSubgroup.closure_induction with
  | mem x hx =>
    induction hb using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨l, hl, hlen, rfl⟩ := hx
      obtain ⟨l', hl', hlen', rfl⟩ := hy
      rw [← List.prod_append]
      refine list_prod_mem_chernProductSubgroup C sX E _ (fun x hx ↦ ?_) (by simp; omega)
      rcases List.mem_append.1 hx with hx | hx
      · exact hl x hx
      · exact hl' x hx
    | zero => rw [mul_zero]; exact zero_mem _
    | add y y' _ _ h h' => rw [mul_add]; exact add_mem h h'
    | neg y _ h => rw [mul_neg]; exact neg_mem h
  | zero => rw [zero_mul]; exact zero_mem _
  | add x x' _ _ h h' => rw [add_mul]; exact add_mem h h'
  | neg x _ h => rw [neg_mul]; exact neg_mem h

/-- On a quasi-compact `X` of dimension `< m`, the `m`-th subgroup is zero. -/
theorem eq_zero_of_mem_chernProductSubgroup [CompactSpace X] {m : ℕ}
    (hdim : topologicalKrullDim X < (m : WithBot ℕ∞)) {a : TotalChowClass C sX}
    (ha : a ∈ chernProductSubgroup C sX E m) : a = 0 := by
  induction ha using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨l, hl, hlen, rfl⟩ := hx
    exact list_prod_eq_zero_of_le_length C sX E hdim l hl hlen
  | zero => rfl
  | add x y _ _ hx hy => rw [hx, hy, add_zero]
  | neg x _ hx => rw [hx, neg_zero]

end Filtration

/-! ### The power sums vanish in large degrees -/

section PowerSums

/-- The Chern classes of `ℰ` of positive degree commute pairwise. -/
theorem commute_homComponent_totalChernClassOfModule_pnat (i j : ℕ+) :
    Commute (TotalChowClass.homComponent (i : ℕ) (totalChernClassOfModule C sX E))
      (TotalChowClass.homComponent (j : ℕ) (totalChernClassOfModule C sX E)) :=
  commute_homComponent_totalChernClassOfModule C sX E E i j

/-- **`P_p(ℰ)` in positive degree is the power sum evaluated at the Chern classes.** -/
theorem chernPolynomialClass_rename_some (P : MvPolynomial ℕ+ ℤ) :
    chernPolynomialClass C sX E (rename some P) =
      commEval (commute_homComponent_totalChernClassOfModule_pnat C sX E) P := by
  have h := eq_commEval (commute_homComponent_totalChernClassOfModule_pnat C sX E)
    (f := (chernPolynomialClass C sX E).comp (rename (some : ℕ+ → Option ℕ+)).toRingHom)
    fun i ↦ by
      rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, rename_X,
        chernPolynomialClass_X_some]
  exact RingHom.congr_fun h P

/-- An element of `WithBot ℕ∞` below `⊤` is below a natural number. -/
theorem exists_lt_natCast_of_lt_top {x : WithBot ℕ∞} (hx : x < ⊤) :
    ∃ m : ℕ, x < (m : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact ⟨0, WithBot.bot_lt_coe _⟩
  | coe x =>
    induction x using ENat.recTopCoe with
    | top => exact absurd hx (lt_irrefl _)
    | coe n =>
      refine ⟨n + 1, ?_⟩
      exact_mod_cast Nat.lt_succ_self n

/-- **The power sums `P_p(ℰ)` vanish in large degrees.** If `X` is quasi-compact and of finite
dimension, then `P_p(ℰ) = 0` for all large `p`: with `R ≥ 1` bounding the rank of `ℰ` and
`dim X < m`, every monomial of `P_p` in the classes `c_1(ℰ), …, c_R(ℰ)` has at least `p / R`
factors, hence at least `m` once `p ≥ R m`. -/
theorem exists_chernPolynomialClass_powerSumChernPolynomial_eq_zero [CompactSpace X]
    (hdim : topologicalKrullDim X < ⊤) :
    ∃ N : ℕ, ∀ p : ℕ, N < p →
      chernPolynomialClass C sX E (powerSumChernPolynomial p : ChernPolynomial) = 0 := by
  obtain ⟨m, hm⟩ := exists_lt_natCast_of_lt_top hdim
  obtain ⟨R, hR⟩ := exists_homComponent_totalChernClassOfModule_eq_zero C sX E
  set R' := max R 1 with hR'
  have hR'pos : (0 : ℚ) < R' := by exact_mod_cast lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  -- the filtration by the number of factors, reindexed by the weight
  set A : ℕ → AddSubgroup (TotalChowClass C sX) :=
    fun k ↦ chernProductSubgroup C sX E ⌈(k : ℚ) / R'⌉₊ with hA
  have : SetLike.GradedMonoid A :=
    { one_mem := by
        change (1 : TotalChowClass C sX) ∈ chernProductSubgroup C sX E ⌈((0 : ℕ) : ℚ) / R'⌉₊
        simp only [Nat.cast_zero, zero_div, Nat.ceil_zero]
        exact list_prod_mem_chernProductSubgroup C sX E [] (by simp) le_rfl
      mul_mem := fun i j a b ha hb ↦ by
        refine chernProductSubgroup_antitone C sX E ?_ (mul_mem_chernProductSubgroup C sX E ha hb)
        push_cast
        rw [add_div]
        exact Nat.ceil_add_le _ _ }
  have hw : ∀ i : ℕ+,
      TotalChowClass.homComponent (i : ℕ) (totalChernClassOfModule C sX E) ∈ A (i : ℕ) := by
    intro i
    by_cases hi : (i : ℕ) ≤ R
    · have h1 := list_prod_mem_chernProductSubgroup C sX E
        [TotalChowClass.homComponent (i : ℕ) (totalChernClassOfModule C sX E)]
        (fun x hx ↦ ⟨i, List.mem_singleton.1 hx⟩) (n := 1) le_rfl
      rw [List.prod_singleton] at h1
      refine chernProductSubgroup_antitone C sX E ?_ h1
      refine Nat.ceil_le.2 ?_
      rw [Nat.cast_one, div_le_one hR'pos]
      exact_mod_cast hi.trans (le_max_left R 1)
    · rw [hR i (by omega)]
      exact zero_mem _
  refine ⟨R' * m, fun p hp ↦ ?_⟩
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by
    have : 0 < p := lt_of_le_of_lt (Nat.zero_le _) hp
    omega⟩
  rw [coe_powerSumChernPolynomial_succ, chernPolynomialClass_rename_some]
  have hmem := commEval_mem (commute_homComponent_totalChernClassOfModule_pnat C sX E) hw
    (powerSumPolynomial (q + 1)).2
  refine eq_zero_of_mem_chernProductSubgroup C sX E hm
    (chernProductSubgroup_antitone C sX E ?_ hmem)
  have h1 : (m : ℚ) ≤ ((q + 1 : ℕ) : ℚ) / R' := by
    rw [le_div_iff₀ hR'pos]
    exact_mod_cast (by nlinarith [hp] : m * R' ≤ q + 1)
  exact_mod_cast h1.trans (Nat.le_ceil _)

end PowerSums

/-! ### The power sums as polynomials in the rank and the Chern classes -/

section Polynomial

/-- Evaluation of a polynomial in the variables `c_i` only, read in `𝐙[r, c_1, c_2, …]`, is
evaluation at the values of the `c_i`. -/
theorem commEval_rename_some {R : Type*} [Ring R] {z : Option ℕ+ → R}
    (hz : ∀ i j, Commute (z i) (z j)) (P : MvPolynomial ℕ+ ℤ) :
    commEval hz (rename some P) = commEval (fun i j ↦ hz (some i) (some j)) P := by
  have h := eq_commEval (fun i j ↦ hz (some i) (some j))
    (f := (commEval hz).comp (rename (some : ℕ+ → Option ℕ+)).toRingHom)
    fun i ↦ by rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, rename_X,
      commEval_X]
  exact RingHom.congr_fun h P

/-- **The power-sum polynomial of Stacks 0F9B evaluated at a commuting family is Newton's
recursion**, in every positive degree. -/
theorem commEval_powerSumPolynomial {R : Type*} [Ring R] {c : ℕ+ → R}
    (hc : ∀ i j, Commute (c i) (c j)) (r : R) :
    ∀ p : ℕ, 0 < p →
      commEval hc (powerSumPolynomial p : MvPolynomial ℕ+ ℤ) = newtonPowerSum r c p := by
  intro p
  induction p using Nat.case_strong_induction_on with
  | hz => intro hp; omega
  | hi p ih =>
    intro _
    have hC : ∀ n : ℤ, commEval hc (C n) = (n : R) := fun n ↦ eq_intCast ((commEval hc).comp C) n
    rw [newtonPowerSum_succ, coe_powerSumPolynomial_succ, map_add, map_sum]
    congr 1
    · refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hjp : j < p := Finset.mem_range.mp hj
      rw [map_mul, map_mul, hC, commEval_X, ih (p - j) (by omega) (by omega)]
      push_cast
      rfl
    · rw [map_mul, hC, commEval_X]
      push_cast
      rfl

/-- **For a module of constant rank `r`, the power sum `P_p(ℱ)` is the polynomial `P_p` of
Stacks 0F9B evaluated at `r` and the Chern classes of Stacks 0B7H.** -/
theorem modulePowerSum_eq_chernPolynomialClassOfRank {Y : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (F : Y.Modules) (r : ℕ)
    [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (p : ℕ) :
    modulePowerSum C sY F r hF p =
      chernPolynomialClassOfRank C sY F r (powerSumChernPolynomial p : ChernPolynomial) := by
  rcases p with _ | p
  · rw [modulePowerSum_zero, coe_powerSumChernPolynomial_zero, degreeZeroPowerSum,
      chernPolynomialClassOfRank, commEval_X]
    rfl
  · rw [coe_powerSumChernPolynomial_succ, chernPolynomialClassOfRank, commEval_rename_some,
      commEval_powerSumPolynomial _ ((r : ℤ) • (1 : TotalChowClass C sY)) (p + 1) (by omega)]
    rfl

/-- **The power sum `P_p(ℰ)` of a module of arbitrary rank is `P_p(r(ℰ), c_1(ℰ), c_2(ℰ), …)`**:
the power sums glued from the rank loci are the values at `ℰ` of the polynomials `P_p` of
Stacks 0F9B in the sense of Stacks 0FA7. -/
theorem modulePowerSumArbitraryRank_eq_chernPolynomialClass (p : ℕ) :
    modulePowerSumArbitraryRank C sX E p =
      chernPolynomialClass C sX E (powerSumChernPolynomial p : ChernPolynomial) := by
  refine (eq_modulePowerSumArbitraryRank_of_res_eq C sX E p fun r ↦ ?_).symm
  have := isFiniteLocallyFreeOfRank_pullback_rankLocus E r
  rw [res_chernPolynomialClass_of_rank C sX E (rankLocus E r).ι rfl r,
    modulePowerSum_eq_chernPolynomialClassOfRank]

end Polynomial

/-- The degree-zero component of the rank `r(ℰ)` of Stacks 0FA7, a total class, is the rank class
`r(ℰ) ∈ A^0(X)` of Stacks 0ESW: both restrict to `r · 1` on each rank locus `X_r`. -/
theorem rankTotalClass_apply_zero_eq_rankClassOfLocallyFree :
    rankTotalClass C sX E 0 = SectionZeroScheme.rankClassOfLocallyFree C sX E := by
  refine SectionZeroScheme.eq_of_chowCohomologyRestriction_rankLocus_eq C sX E fun r ↦ ?_
  refine Eq.trans ?_
    (SectionZeroScheme.chowCohomologyRestriction_rankClassOfLocallyFree C sX E r).symm
  have h := TotalChowClass.res_rfl_apply (rankLocus E r).ι (rankTotalClass C sX E) 0
  rw [rankTotalClass, res_rankFunctionClass_rankLocus] at h
  refine h.symm.trans ?_
  change (r : ℤ) • (1 : TotalChowClass C ((rankLocus E r).ι ≫ sX)) 0 = _
  rw [TotalChowClass.one_apply_zero]
  rfl

/-! ### The Chern character -/

section ChernCharacter

/-- **Stacks 0ESX, the Chern character of a module of arbitrary rank.** For a finite locally free
module `ℰ` whose rank need not be constant, the Chern character
`ch(ℰ) = (ch_0(ℰ), ch_1(ℰ), …) ∈ ∏_{p ≥ 0} (A^p(X) ⊗ 𝐐)` (`Stacks.Chow.moduleChernCharacter`) has
components `ch_p(ℰ) = P_p(ℰ)/p!`, where `P_p(ℰ) ∈ A^p(X)` is the power sum of Stacks 0F9B (with
`P_0 = r`) evaluated at the rank `r(ℰ)` and the Chern classes `c_i(ℰ)` of Stacks 0ESW, as in
Stacks 0FA7. -/
@[stacks 0ESX "the components ch_p(E) = P_p(E)/p! ∈ A^p(X) ⊗ Q of the Chern character of a \
finite locally free module of not necessarily constant rank, with P_p of 0F9B evaluated at the \
rank and Chern classes of 0ESW (0FA7), so that ch(E) ∈ ∏_{p ≥ 0} (A^p(X) ⊗ Q)"]
theorem moduleChernCharacter_apply_eq (p : ℕ) :
    moduleChernCharacter C sX E p =
      ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ]
        chernPolynomialComponent C sX E p (powerSumChernPolynomial p) := by
  rw [moduleChernCharacter_apply, moduleChernCharacterComponent,
    modulePowerSumComponentArbitraryRank, modulePowerSumArbitraryRank_eq_chernPolynomialClass]
  rfl

/-- **`ch_0(ℰ)` is the rank** `r(ℰ) ∈ A^0(X)` of Stacks 0ESW. -/
theorem moduleChernCharacter_zero :
    moduleChernCharacter C sX E 0 =
      (1 : ℚ) ⊗ₜ[ℤ] SectionZeroScheme.rankClassOfLocallyFree C sX E := by
  rw [moduleChernCharacter_apply_eq, chernPolynomialComponent, coe_powerSumChernPolynomial_zero,
    degreeZeroPowerSum, chernPolynomialClass_X_none,
    rankTotalClass_apply_zero_eq_rankClassOfLocallyFree, Nat.factorial_zero, Nat.cast_one,
    inv_one]

add_to_stacks 0ESX "the full Chern character ch(E) ∈ ∏_{p ≥ 0} (A^p(X) ⊗ Q) of a finite \
locally free module of not necessarily constant rank, built from the genuine classes of 0B7H on \
the rank loci" Stacks.Chow.moduleChernCharacter

/-- On a quasi-compact `X` of finite dimension the components `ch_p(ℰ)` vanish for all large
`p`. -/
theorem exists_moduleChernCharacter_eq_zero [CompactSpace X]
    (hdim : topologicalKrullDim X < ⊤) :
    ∃ N : ℕ, ∀ p : ℕ, N < p → moduleChernCharacter C sX E p = 0 := by
  obtain ⟨N, hN⟩ := exists_chernPolynomialClass_powerSumChernPolynomial_eq_zero C sX E hdim
  refine ⟨N, fun p hp ↦ ?_⟩
  rw [moduleChernCharacter_apply_eq, chernPolynomialComponent, hN p hp,
    TotalChowClass.zero_apply, TensorProduct.tmul_zero]

/-- **Stacks 0ESX, the finite-dimensional case.** If `X` is quasi-compact and `dim X < ∞`, then
`ch(ℰ) ∈ A^*(X) ⊗ 𝐐`: the full Chern character is the image of an element of the direct sum
`⊕_{p ≥ 0} (A^p(X) ⊗ 𝐐)` under its inclusion into the product. -/
@[stacks 0ESX "for X quasi-compact with dim(X) < ∞, ch(E) ∈ A^*(X) ⊗ Q: the full Chern \
character is the image of an element of ⊕_p (A^p(X) ⊗ Q)"]
theorem exists_gradedRationalChowCohomology_eq_moduleChernCharacter [CompactSpace X]
    (hdim : topologicalKrullDim X < ⊤) :
    ∃ y : gradedRationalChowCohomology C (gysinSystemOfInvertible C) sX,
      ∀ p : ℕ, y p = moduleChernCharacter C sX E p := by
  classical
  obtain ⟨N, hN⟩ := exists_moduleChernCharacter_eq_zero C sX E hdim
  refine ⟨∑ q ∈ Finset.range (N + 1),
    DirectSum.of _ q (moduleChernCharacter C sX E q), fun p ↦ ?_⟩
  rw [DirectSum.sum_apply]
  rcases le_or_gt p N with hp | hp
  · rw [Finset.sum_eq_single p]
    · exact DirectSum.of_eq_same p _
    · exact fun b _ hb ↦ DirectSum.of_eq_of_ne b p _ (Ne.symm hb)
    · exact fun h ↦ absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hp)) h
  · rw [Finset.sum_eq_zero fun b hb ↦ DirectSum.of_eq_of_ne b p _ (by
      have := Finset.mem_range.1 hb
      omega)]
    exact (hN p hp).symm

end ChernCharacter

end Stacks.Chow

end
