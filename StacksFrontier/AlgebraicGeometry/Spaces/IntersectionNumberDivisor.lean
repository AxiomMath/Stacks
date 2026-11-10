module

public import Mathlib.Algebra.BigOperators.Fin
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.NumericalIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# Intersecting with an effective Cartier divisor

Let `k` be a field, let `X` be a proper algebraic space over `k`, let `i : Z ⟶ X` be a closed
subspace of dimension `d` and let `L₁, …, L_d` be invertible `𝒪_X`-modules.  If `L₁|_Z` is the
invertible sheaf `𝒪_Z(D)` of an effective Cartier divisor `D ⊆ Z`, then

`(L₁ ⋯ L_d · Z) = (L₂ ⋯ L_d · D)`.

The mechanism is the exact sequence `0 ⟶ 𝒪_Z(-D) ⟶ 𝒪_Z ⟶ 𝒪_D ⟶ 0`: twisting it by
`L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_d^{⊗ n_d}` and taking Euler characteristics turns the finite difference of
the numerical function of `Z` in the first variable into the numerical function of `D`, and the
mixed finite difference that *defines* the intersection number
(`AlgebraicGeometry.Space.intersectionNumber`) then reads off the same integer on both sides.

## Main results

* `MvPolynomial.sum_neg_one_pow_mul_sub_eval_cons_eq_coeff_one`: for a polynomial `P` in `d + 1`
  variables of total degree at most `d + 1`, the `d`-fold mixed finite difference of the first
  difference `P(a, n₂, …) - P(a - 1, n₂, …)` is the coefficient of `n₁ ⋯ n_{d+1}` in `P`, for
  **every** value of `a`.
* `AlgebraicGeometry.Space.intersectionNumber_eq_of_sub_eulerCharacteristic_eq`: the numerical
  heart of Stacks 0EDK.  Once the Euler characteristics of the twists of `i_*𝒪_Z` satisfy the
  first-difference relation with those of the twists of `j_*𝒪_D`, the two intersection numbers
  agree.

Stacks 0EDK itself, with no hypothesis beyond the source's, is
`AlgebraicGeometry.Space.intersectionNumber_eq_sum_of_isEffectiveCartierDivisor` of
`StacksFrontier/AlgebraicGeometry/Spaces/IntersectionNumberCartierDivisor.lean`.

## Implementation notes

**Why `a` is taken at `0` rather than at `1`.** The intersection number is the mixed finite
difference of the numerical function at the tuple `(1, …, 1)`, so its first difference is taken
between `n₁ = 1` and `n₁ = 0`, where the third term of the twisted divisor sequence still carries
a factor `L₁|_D`.  Taking it instead between `n₁ = 0` and `n₁ = -1` makes that factor
`L₁^{⊗ 0}`, and the third term is then the twist of `j_*𝒪_D` by `L₂, …, L_d` alone — exactly the
module whose Euler characteristics define `(L₂ ⋯ L_d · D)`.  That the two differences agree is
`MvPolynomial.sum_neg_one_pow_mul_sub_eval_cons_eq_coeff_one`, whose independence of `a` is the
degree bound of Stacks 0DN4.

**What is carried, and why.**
`AlgebraicGeometry.Space.intersectionNumber_eq_of_sub_eulerCharacteristic_eq` is the numerical
step of the source's proof only, and takes its two inputs as hypotheses.

* A numerical polynomial for `Z`, as in Stacks 0DN4.  This is the hypothesis `P`, used exactly as
  in the neighbouring `AlgebraicGeometry.Space.intersectionNumber_eq_coeff`.
* The first-difference relation between the Euler characteristics of the twists of `i_*𝒪_Z` and
  of `iD_*𝒪_D`, which the source obtains from the twisted divisor exact sequence
  `0 ⟶ i_*𝒪_Z ⊗ L₁^{⊗ -1} ⊗ ⋯ ⟶ i_*𝒪_Z ⊗ ⋯ ⟶ j_*𝒪_D ⊗ ⋯ ⟶ 0` and the additivity of the Euler
  characteristic, Stacks 0DN2.

The closed-immersion and dimension hypotheses on `i` and `iD` are those of
`AlgebraicGeometry.Space.intersectionNumber` itself; they are needed to form the two
intersection numbers and are not used otherwise.

## References

* [Stacks Project, Tag 0EDK](https://stacks.math.columbia.edu/tag/0EDK)
* [Stacks Project, Tag 0EDF](https://stacks.math.columbia.edu/tag/0EDF)
* [Stacks Project, Tag 0DN2](https://stacks.math.columbia.edu/tag/0DN2)
* [Stacks Project, Tag 0DN4](https://stacks.math.columbia.edu/tag/0DN4)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
* [Stacks Project, Tag 0841](https://stacks.math.columbia.edu/tag/0841)
* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u w

/-- Inclusion-exclusion over the subsets of a finite set: the alternating sum of the indicators
of `T ⊆ S` is `1` when `T` is everything and `0` otherwise. -/
private theorem sum_neg_one_pow_mul_ite_subset {d : ℕ} (T : Finset (Fin d)) :
    ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) * (if T ⊆ S then 1 else 0) =
      if T = Finset.univ then 1 else 0 := by
  classical
  have hpow : ∀ A : Finset (Fin d),
      ∑ U ∈ A.powerset, (-1 : ℚ) ^ U.card = if A = ∅ then 1 else 0 := by
    intro A
    by_cases hA : A = ∅
    · subst hA; simp
    · rw [ite_eq_right hA]
      have h := Finset.sum_powerset_neg_one_pow_card_of_nonempty
        (Finset.nonempty_iff_ne_empty.2 hA)
      have h' := congrArg (fun z : ℤ => (z : ℚ)) h
      push_cast at h'
      exact h'
  have hstep : ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) * (if T ⊆ S then 1 else 0) =
      ∑ U : Finset (Fin d), (-1 : ℚ) ^ U.card * (if U ⊆ Tᶜ then 1 else 0) := by
    refine Fintype.sum_bijective (fun S : Finset (Fin d) => Sᶜ)
      (Function.Involutive.bijective fun S => compl_compl S) _ _ fun S => ?_
    have hcard : (Sᶜ).card = d - S.card := by
      rw [Finset.card_compl, Fintype.card_fin]
    simp only [hcard, Finset.compl_subset_compl]
  have hfilter : (Finset.univ.filter fun U : Finset (Fin d) => U ⊆ Tᶜ) = Tᶜ.powerset := by
    ext U; simp
  calc ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) * (if T ⊆ S then 1 else 0)
      = ∑ U : Finset (Fin d), (-1 : ℚ) ^ U.card * (if U ⊆ Tᶜ then 1 else 0) := hstep
    _ = ∑ U ∈ Finset.univ.filter fun U : Finset (Fin d) => U ⊆ Tᶜ, (-1 : ℚ) ^ U.card := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun U _ => by split_ifs <;> simp
    _ = ∑ U ∈ Tᶜ.powerset, (-1 : ℚ) ^ U.card := by rw [hfilter]
    _ = if Tᶜ = ∅ then 1 else 0 := hpow _
    _ = if T = Finset.univ then 1 else 0 := by simp [Finset.compl_eq_empty_iff]

namespace MvPolynomial

/-- **The mixed finite difference of a first difference, at any base point.**  For a polynomial
`P` in `d + 1` variables of total degree at most `d + 1` and any `a`, the alternating sum

`∑_{S ⊆ Fin d} (-1)^{d - |S|} (P(a, 1_S) - P(a - 1, 1_S))`

of the first differences of `P` in the variable `n₁`, evaluated at the indicator functions of the
subsets of the remaining `d` variables, is the coefficient of the squarefree monomial
`n₁ ⋯ n_{d+1}`.  In particular it does not depend on `a`.

Evaluating `n^c` at `(a, 1_S)` gives `a^{c₁}` when the support of the tail of `c` is contained in
`S` and `0` otherwise, so the alternating sum is `∑_c coeff_c P (a^{c₁} - (a-1)^{c₁})` over the
exponents `c` whose tail has full support; the degree bound forces such a `c` with `c₁ ≠ 0` to be
`(1, …, 1)`, and the factor vanishes when `c₁ = 0`. -/
theorem sum_neg_one_pow_mul_sub_eval_cons_eq_coeff_one {d : ℕ}
    (P : MvPolynomial (Fin (d + 1)) ℚ) (hP : P.totalDegree ≤ d + 1) (a : ℚ) :
    ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
        (eval (Fin.cons a fun j => if j ∈ S then (1 : ℚ) else 0) P -
          eval (Fin.cons (a - 1) fun j => if j ∈ S then (1 : ℚ) else 0) P) =
      P.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) := by
  classical
  set one : Fin (d + 1) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => 1 with hone
  set tail : (Fin (d + 1) →₀ ℕ) → Finset (Fin d) :=
    fun c => Finset.univ.filter fun j => c j.succ ≠ 0 with htail
  have hmem : ∀ (c : Fin (d + 1) →₀ ℕ) (j : Fin d), j ∈ tail c ↔ c j.succ ≠ 0 := by
    intro c j; rw [htail]; simp
  have hprod : ∀ (x : ℚ) (S : Finset (Fin d)) (c : Fin (d + 1) →₀ ℕ),
      (∏ j, (Fin.cons x (fun j => if j ∈ S then (1 : ℚ) else 0) j) ^ c j) =
        x ^ c 0 * (if tail c ⊆ S then 1 else 0) := by
    intro x S c
    rw [Fin.prod_univ_succ, Fin.cons_zero]
    congr 1
    simp only [Fin.cons_succ]
    by_cases h : tail c ⊆ S
    · rw [ite_eq_left h]
      refine Finset.prod_eq_one fun j _ => ?_
      by_cases hj : j ∈ S
      · rw [ite_eq_left hj, one_pow]
      · have hzero : c j.succ = 0 := by
          by_contra hne
          exact hj (h ((hmem c j).2 hne))
        rw [hzero, pow_zero]
    · rw [ite_eq_right h]
      obtain ⟨j, hj, hjS⟩ := Finset.not_subset.1 h
      refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
      rw [ite_eq_right hjS, zero_pow ((hmem c j).1 hj)]
  have hkey : ∀ (x : ℚ) (S : Finset (Fin d)),
      eval (Fin.cons x fun j => if j ∈ S then (1 : ℚ) else 0) P =
        ∑ c ∈ P.support, P.coeff c * (x ^ c 0 * (if tail c ⊆ S then 1 else 0)) := by
    intro x S
    rw [eval_eq']
    exact Finset.sum_congr rfl fun c _ => by rw [hprod x S c]
  have hsuppOne : tail one = Finset.univ := by
    ext j
    rw [hmem one j, hone]
    simp
  have hdeg : ∀ c ∈ P.support, tail c = Finset.univ → c 0 ≠ 0 → c = one := by
    intro c hc hfull hc0
    have hge : ∀ j : Fin d, 1 ≤ c j.succ := by
      intro j
      have hjmem : j ∈ tail c := by rw [hfull]; exact Finset.mem_univ j
      exact Nat.one_le_iff_ne_zero.2 ((hmem c j).1 hjmem)
    have hsum : c 0 + ∑ j : Fin d, c j.succ ≤ d + 1 := by
      have h := le_trans (le_totalDegree hc) hP
      rw [Finsupp.sum_fintype _ _ fun _ => rfl, Fin.sum_univ_succ] at h
      exact h
    have hlow : (d : ℕ) ≤ ∑ j : Fin d, c j.succ := by
      calc (d : ℕ) = ∑ _j : Fin d, 1 := by simp
        _ ≤ ∑ j : Fin d, c j.succ := Finset.sum_le_sum fun j _ => hge j
    have hc0' : c 0 = 1 := by omega
    have hall : ∀ j : Fin d, c j.succ = 1 := by
      intro j
      rcases Nat.lt_or_ge (c j.succ) 2 with h | h
      · have := hge j; omega
      · exfalso
        have hlt : ∑ _j : Fin d, 1 < ∑ j : Fin d, c j.succ :=
          Finset.sum_lt_sum (fun j _ => hge j) ⟨j, Finset.mem_univ j, by omega⟩
        have hconst : ∑ _j : Fin d, (1 : ℕ) = d := by simp
        omega
    refine Finsupp.ext fun j => ?_
    rw [hone, Finsupp.coe_equivFunOnFinite_symm]
    refine Fin.cases ?_ (fun l => ?_) j
    · exact hc0'
    · exact hall l
  calc ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
          (eval (Fin.cons a fun j => if j ∈ S then (1 : ℚ) else 0) P -
            eval (Fin.cons (a - 1) fun j => if j ∈ S then (1 : ℚ) else 0) P)
      = ∑ S : Finset (Fin d), ∑ c ∈ P.support,
          P.coeff c * (a ^ c 0 - (a - 1) ^ c 0) *
            ((-1 : ℚ) ^ (d - S.card) * (if tail c ⊆ S then 1 else 0)) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [hkey a S, hkey (a - 1) S, ← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring
    _ = ∑ c ∈ P.support, P.coeff c * (a ^ c 0 - (a - 1) ^ c 0) *
          ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) * (if tail c ⊆ S then 1 else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ c ∈ P.support, P.coeff c * (a ^ c 0 - (a - 1) ^ c 0) *
          (if tail c = Finset.univ then 1 else 0) :=
        Finset.sum_congr rfl fun c _ => by rw [sum_neg_one_pow_mul_ite_subset (tail c)]
    _ = ∑ c ∈ P.support, if c = one then P.coeff c else 0 := by
        refine Finset.sum_congr rfl fun c hc => ?_
        by_cases hfull : tail c = Finset.univ
        · rw [ite_eq_left hfull, mul_one]
          by_cases hc0 : c 0 = 0
          · rw [hc0, pow_zero, pow_zero, sub_self, mul_zero, ite_eq_right]
            intro hceq
            rw [hceq, hone, Finsupp.coe_equivFunOnFinite_symm] at hc0
            exact absurd hc0 one_ne_zero
          · have hceq := hdeg c hc hfull hc0
            have hc0' : c 0 = 1 := by
              rw [hceq, hone, Finsupp.coe_equivFunOnFinite_symm]
            rw [hc0', pow_one, pow_one, ite_eq_left hceq]
            ring
        · have hne : c ≠ one := fun h => hfull (by rw [h]; exact hsuppOne)
          rw [ite_eq_right hfull, mul_zero, ite_eq_right hne]
    _ = P.coeff one := by
        rw [Finset.sum_ite_eq' P.support one fun c => P.coeff c]
        by_cases hmemOne : one ∈ P.support
        · rw [ite_eq_left hmemOne]
        · rw [ite_eq_right hmemOne]
          have hz : P.coeff one = 0 := by
            by_contra hcc
            exact hmemOne (mem_support_iff.2 hcc)
          exact hz.symm

end MvPolynomial

namespace AlgebraicGeometry.Space

/-- A cohomology module over a field that vanishes is finite-dimensional, in the module universe
in which the cohomology of an algebraic space lives. -/
private theorem finiteDimensional_of_isZero_cohomology (k : Type u) [Field k]
    {M : ModuleCat.{max (u + 1) w} k} (h : IsZero M) : FiniteDimensional k M :=
  have : Subsingleton M := ModuleCat.subsingleton_of_isZero h
  have : Finite M := Finite.of_subsingleton
  inferInstance

section IntersectionNumberDivisor

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (X Z : AlgebraicSpaces B (Spec (.of k)) hk)

/-- **The numerical heart of Stacks 0EDK.**  Let `i : Z ⟶ X` be a closed subspace of dimension
`d + 1` of a proper algebraic space `X` over a field, let `iD : D ⟶ X` be a closed subspace of
dimension `d`, and let `L₁, …, L_{d+1}` be invertible `𝒪_X`-modules.  Suppose the Euler
characteristics of the twists satisfy the first-difference relation

`χ(X, i_*𝒪_Z ⊗ L₁^{⊗ 0} ⊗ ⋯) - χ(X, i_*𝒪_Z ⊗ L₁^{⊗ -1} ⊗ ⋯) = χ(X, iD_*𝒪_D ⊗ L₂ ⊗ ⋯)`

at the indicator tuples, and that a rational polynomial of total degree at most `d + 1` takes the
Euler characteristics of the twists of `i_*𝒪_Z` as its values.  Then
`(L₁ ⋯ L_{d+1} · Z) = (L₂ ⋯ L_{d+1} · D)`. -/
theorem intersectionNumber_eq_of_sub_eulerCharacteristic_eq (D : AlgebraicSpaces B
      (Spec (.of k)) hk) (d : ℕ) (f : X.1 ⟶ yoneda.obj (baseObject k B hk))
    (hf : IsProper B (Spec (.of k)) hk f) (i : Z ⟶ X)
    (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (hd : dimension B (Spec (.of k)) hk Z.1 Z.2 = d + 1) (iD : D ⟶ X)
    (hiD : IsClosedImmersion B (Spec (.of k)) hk iD.hom)
    (hdD : dimension B (Spec (.of k)) hk D.1 D.2 = d)
    (L : Fin (d + 1) → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of k)) hk X.1
        X.2).O)).property (L j)]
    [∀ n : Fin (d + 1) → ℤ, IsCoherent B (Spec (.of k)) hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
        (structureSheafPushforward B (Spec (.of k)) hk i) L n)]
    [∀ n : Fin d → ℤ, IsCoherent B (Spec (.of k)) hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
        (structureSheafPushforward B (Spec (.of k)) hk iD) (fun j => L j.succ) n)]
    (P : MvPolynomial (Fin (d + 1)) ℚ)
    (hP : ∀ n : Fin (d + 1) → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
      ((eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
          (structureSheafPushforward B (Spec (.of k)) hk i) L n) : ℤ) : ℚ))
    (hPdeg : P.totalDegree ≤ d + 1)
    (hdiff : ∀ S : Finset (Fin d),
      eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
            (structureSheafPushforward B (Spec (.of k)) hk i) L
            (Fin.cons 0 fun j => if j ∈ S then 1 else 0)) -
        eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
            (structureSheafPushforward B (Spec (.of k)) hk i) L
            (Fin.cons (-1) fun j => if j ∈ S then 1 else 0)) =
      eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
          (structureSheafPushforward B (Spec (.of k)) hk iD) (fun j => L j.succ)
          fun j => if j ∈ S then 1 else 0)) :
    intersectionNumber.{u, w} k B hk X Z (d + 1) f hf i hi hd L =
      intersectionNumber.{u, w} k B hk X D d f hf iD hiD hdD fun j => L j.succ := by
  classical
  have hcast : ∀ (m : ℤ) (S : Finset (Fin d)),
      (fun j : Fin (d + 1) =>
          (((Fin.cons m fun l => if l ∈ S then (1 : ℤ) else 0 : Fin (d + 1) → ℤ) j : ℤ) : ℚ)) =
        (Fin.cons (m : ℚ) fun l => if l ∈ S then (1 : ℚ) else 0 : Fin (d + 1) → ℚ) := by
    intro m S
    refine funext fun j => ?_
    refine Fin.cases ?_ (fun l => ?_) j
    · simp
    · simp only [Fin.cons_succ]
      split_ifs <;> simp
  have hval : ∀ (m : ℤ) (S : Finset (Fin d)),
      MvPolynomial.eval
          (Fin.cons (m : ℚ) fun l => if l ∈ S then (1 : ℚ) else 0 : Fin (d + 1) → ℚ) P =
        ((eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
            (structureSheafPushforward B (Spec (.of k)) hk i) L
            (Fin.cons m fun l => if l ∈ S then (1 : ℤ) else 0)) : ℤ) : ℚ) := by
    intro m S
    have h := hP (Fin.cons m fun l => if l ∈ S then (1 : ℤ) else 0)
    rw [hcast m S] at h
    exact h
  have hZ : ((intersectionNumber.{u, w} k B hk X Z (d + 1) f hf i hi hd L : ℤ) : ℚ) =
      P.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) :=
    intersectionNumber_eq_coeff.{u, w} k B hk X Z (d + 1) f hf i hi hd L P hP hPdeg
  have hshift := MvPolynomial.sum_neg_one_pow_mul_sub_eval_cons_eq_coeff_one P hPdeg 0
  have hmain : ((intersectionNumber.{u, w} k B hk X Z (d + 1) f hf i hi hd L : ℤ) : ℚ) =
      ((intersectionNumber.{u, w} k B hk X D d f hf iD hiD hdD fun j => L j.succ : ℤ) : ℚ) := by
    rw [hZ, ← hshift, intersectionNumber_eq_sum.{u, w} k B hk X D d f hf iD hiD hdD]
    push_cast
    refine Finset.sum_congr rfl fun S _ => ?_
    have h0 := hval 0 S
    have h1 := hval (-1) S
    push_cast at h0 h1
    rw [← hdiff S, zero_sub, h0, h1]
    push_cast
    ring
  exact Int.cast_injective hmain

end IntersectionNumberDivisor

end AlgebraicGeometry.Space

end
