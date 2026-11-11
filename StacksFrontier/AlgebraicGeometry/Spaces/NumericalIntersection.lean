module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Data.Nat.Choose.Sum
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Polynomial.Numerical
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.Spaces.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.EulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedModuleCoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite

/-!
# Numerical intersection numbers on a proper algebraic space over a field

Let `k` be a field, let `X` be a proper algebraic space over `k`, let `i : Z ⟶ X` be a closed
subspace of dimension `d` and let `L₁, …, L_d` be invertible `𝒪_X`-modules.  The intersection
number `(L₁ ⋯ L_d · Z)` is the coefficient of `n₁ ⋯ n_d` in the numerical polynomial

`χ(X, i_*𝒪_Z ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_d^{⊗ n_d})`.

The coefficient of the squarefree monomial `n₁ ⋯ n_d` in a polynomial of total degree at most
`d` is the `d`-fold mixed finite difference `∑_{S ⊆ {1, …, d}} (-1)^{d - |S|} P(1_S)` of its
values at the indicator functions `1_S`, so the intersection number is *defined* here by that
alternating sum of Euler characteristics.  It is therefore an honest integer, with no choice of
data from an existence statement and no appeal to polynomiality, and the source's own
description is recovered as a theorem.

## Main definitions

* `AlgebraicGeometry.Space.intersectionNumber`: **Stacks 0EDF**, the intersection number
  `(L₁ ⋯ L_d · Z)`, as the `d`-fold mixed finite difference of
  `n ↦ χ(X, i_*𝒪_Z ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_d^{⊗ n_d})`.
* `AlgebraicGeometry.Space.selfIntersectionNumber`: the special case `(L^d · Z)` of a single
  invertible module repeated `d` times.
* `AlgebraicGeometry.Space.twistStepIso`, `twistStepZeroIso`, `twistStepSwapIso`,
  `twistStepOneTensorIso`, `foldlTwistStepIso`, `foldlTwistStepCommIso`,
  `twistedModuleConsZeroIso` and `twistedModuleUliftIsoOfIso`: the isomorphisms of twists used to
  compare the twist by a family with the twist by the family obtained by splitting one of its
  members into a tensor product.

## Main results

* `AlgebraicGeometry.Space.intersectionNumber_eq_sum`: the defining alternating sum.

The twist `M ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_d^{⊗ n_d}` itself — `AlgebraicGeometry.Space.twistStep`,
`AlgebraicGeometry.Space.twistedModule` and `AlgebraicGeometry.Space.twistedModuleUlift` — the
direct image `AlgebraicGeometry.Space.structureSheafPushforward` of the structure sheaf along a
morphism, and the coherence of the twists of that direct image are in
`StacksFrontier/AlgebraicGeometry/Spaces/TwistedModuleCoherent.lean`.
* `AlgebraicGeometry.Space.intersectionNumber_eq_coeff`: **the source's own description of the
  intersection number.**  Whenever a rational polynomial of total degree at most `d` takes the
  Euler characteristics of the twists as its values at integral tuples, the intersection number
  is its coefficient of `n₁ ⋯ n_d`.  There is no hypothesis beyond those two, and in particular
  the existence of such a polynomial — which is Stacks 0DN4 — is not assumed.
* `AlgebraicGeometry.Space.exists_intCast_eq_coeff_one`: the coefficient of `n₁ ⋯ n_d` in any
  representing polynomial of total degree at most `d` is an integer, namely `intersectionNumber`
  itself.  Stacks 0EDG, with the representing polynomial supplied by Stacks 0DN4, is
  `AlgebraicGeometry.Space.exists_eval_eq_eulerCharacteristic_and_exists_intCast_eq_coeff_one`
  of `StacksFrontier/AlgebraicGeometry/Spaces/IntersectionNumberAdditivity.lean`.
* `MvPolynomial.sum_neg_one_pow_mul_sub_eval_cons_eq_zero`: for a polynomial in `d + 1`
  variables of total degree at most `d`, the `d`-fold mixed finite difference of its first
  difference in the remaining variable vanishes.  This is the degree count behind additivity.
* `AlgebraicGeometry.Space.intersectionNumber_eq_add_of_iso_tensorSheaf`: the intersection
  number is additive in each of its invertible modules, given a numerical polynomial for the
  split family.  Stacks 0EDH itself, with that polynomial supplied by Stacks 0DN4, is
  `AlgebraicGeometry.Space.intersectionNumber_eq_add_intersectionNumber_of_iso_tensorSheaf` of
  `StacksFrontier/AlgebraicGeometry/Spaces/IntersectionNumberAdditivity.lean`.

## Implementation notes

**Why the finite difference is the definition.**  Evaluating a monomial `n^a` at the indicator
function of `S ⊆ {1, …, d}` gives `1` precisely when the support of `a` is contained in `S`, and
`0` in every other case, so the alternating sum `∑_S (-1)^{d - |S|} P(1_S)` is the sum of the
coefficients
of the `a` whose support is all of `Fin d`; a total degree of at most `d` forces such an `a` to
be `(1, …, 1)`.  The resulting formula involves only finitely many values of the function, so it
makes sense before polynomiality is known, and it is manifestly integral, which is why the
intersection number is `ℤ`-valued here rather than `ℚ`-valued.  That monomial computation is
pure algebra and is `MvPolynomial.sum_neg_one_pow_mul_eval_indicator_eq_coeff_one` of
`StacksFrontier/Algebra/Polynomial/Numerical.lean`, where the scheme-level intersection number of
Stacks 0BEP reads it as well.

**What additivity carries, and why.**  The source proves Stacks 0EDH by applying Stacks 0DN4 to
the `d + 1` invertible modules obtained from `L₁, …, L_d` by replacing `L_{i₀}` by the pair
`L_{i₀}'', L_{i₀}'`, and reading the three intersection numbers off the resulting numerical
polynomial.  That polynomial — the numerical polynomial of **Stacks 0DN4** for the split family,
of total degree at most `d` in `d + 1` variables — is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/IntersectionNumberPolynomial.lean`, which imports this
file, so here it is the hypothesis `Q` of
`AlgebraicGeometry.Space.intersectionNumber_eq_add_of_iso_tensorSheaf`, discharged in
`StacksFrontier/AlgebraicGeometry/Spaces/IntersectionNumberAdditivity.lean`.  This is the
hypothesis `P` of the neighbouring `intersectionNumber_eq_coeff` and of
`AlgebraicGeometry.Space.intersectionNumber_eq_intersectionNumber_of_isEffectiveCartierDivisor`
one family larger, and it is used here exactly as it is used there.

Nothing else is carried.  The three comparisons between the twists by the split family and the
twists by `L`, by `L'` and by `L''` are **proved**, and this is where most of the work of the
file goes.  Only two exponents ever occur, because the intersection number is the mixed finite
difference at the indicator tuples: the comparisons are needed at exponent `1` and at exponent
`0`, so neither the multiplication of tensor powers nor its coherence (Stacks 01CU) is needed,
only

* `Stacks.SheafOfModules.Invertible.tensorProductRightUnitor`, since `L^{⊗ 0}` is the structure
  sheaf by `Stacks.SheafOfModules.Invertible.tensorPower_zero`, which makes a twisting step at
  exponent `0` the identity (`AlgebraicGeometry.Space.twistStepZeroIso`);
* `Stacks.SheafOfModules.Invertible.tensorProductAssociator` and `tensorPowerOneIso`, which turn
  a twist by `L_{i₀} ≅ L_{i₀}' ⊗ L_{i₀}''` at exponent `1` into the two successive twists by
  `L_{i₀}'` and `L_{i₀}''` (`AlgebraicGeometry.Space.twistStepOneTensorIso`);
* `Stacks.SheafOfModules.Invertible.tensorProductBraiding`, which commutes two twisting steps
  (`AlgebraicGeometry.Space.twistStepSwapIso`) and so moves the new factor from the front of the
  chain to the index `i₀`;
* `AlgebraicGeometry.Space.eulerCharacteristic_congr`, the invariance of the Euler
  characteristic under an isomorphism of its module.

The bookkeeping that assembles these is the splitting of the chain of twisting steps at the index
`i₀` — the list of indices is `List.take` of it, then `i₀`, then `List.drop` — and the two facts
that the step function only depends on the modules and exponents at the indices it visits and
that the chain preserves isomorphisms of the module it starts from.

**The dimension hypothesis.**  `AlgebraicGeometry.Space.dimension … Z = d` is carried on the
definition itself, as is the closed-immersion hypothesis on `i`; both type-check there and
neither is used in the body, which is a finite sum of Euler characteristics for every family of
`d` invertible modules.  They are the source's hypotheses and are kept so that the entity
defined is the one of the tag; the number assigned to data not satisfying them is of no
interest.

**The module universes.**  `AlgebraicGeometry.Space.eulerCharacteristic` takes its module in
`AlgebraicGeometry.Space.Modules.{u, max (u + 1) w}`, because the derived global sections of a
ringed site take values in a module universe containing the site.  The direct image of modules
along a morphism of algebraic spaces and the tensor product and tensor powers of sheaves of
modules are all available only at `AlgebraicGeometry.Space.Modules.{u, u}`, the sheafification
instances of the small étale ringed site being available for `AddCommGrpCat.{u}`.  All of the
module algebra is therefore performed at `Modules.{u, u}` and the universe of the sections is
raised exactly once, by `SheafOfModules.uliftForPresentation`, immediately before the Euler
characteristic is taken.

**Invertibility and coherence.**  Invertibility is `Stacks.SheafOfModules.IsInvertible`, which
is the spelling the small étale ringed site already uses in
`StacksFrontier.AlgebraicGeometry.Spaces.InvertibleCoherent`.

Coherence of the twists is **not** a hypothesis: the Euler characteristic of Stacks 0DN1 takes
coherence of its module as an instance, and here that instance is *discharged*, by
`AlgebraicGeometry.Space.isCoherent_twistedModuleUlift_structureSheafPushforward` of
`StacksFrontier/AlgebraicGeometry/Spaces/TwistedModuleCoherent.lean`.  Its three inputs are that a
proper algebraic space over a field is locally Noetherian (Stacks 04ZK), that the direct image
`i_*𝒪_Z` of the structure sheaf along a closed immersion is coherent
(`AlgebraicGeometry.Space.isCoherent_structureSheafPushforward`), and that the twist of a
coherent module by tensor powers of invertible modules is coherent (Stacks 07UB and 03L6).  So
`AlgebraicGeometry.Space.intersectionNumber` and
`AlgebraicGeometry.Space.selfIntersectionNumber` carry exactly the hypotheses of the source
statement and nothing else, and the same is true of
`AlgebraicGeometry.Space.intersectionNumber_eq_sum` and of
`AlgebraicGeometry.Space.intersectionNumber_eq_coeff`, whose statements name the discharged
instance explicitly rather than quantifying over it.

## References

* [Stacks Project, Tag 0EDF](https://stacks.math.columbia.edu/tag/0EDF)
* [Stacks Project, Tag 0EDG](https://stacks.math.columbia.edu/tag/0EDG)
* [Stacks Project, Tag 0EDH](https://stacks.math.columbia.edu/tag/0EDH)
* [Stacks Project, Tag 0DN4](https://stacks.math.columbia.edu/tag/0DN4)
* [Stacks Project, Tag 0DN1](https://stacks.math.columbia.edu/tag/0DN1)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04N6](https://stacks.math.columbia.edu/tag/04N6)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u w

namespace MvPolynomial

/-- **Substituting a constant for the first of `d + 1` variables**, for a polynomial of total
degree at most `d`: the resulting polynomial in `d` variables still has total degree at most
`d`, its values are the values of the original one on the corresponding hyperplane, and its
coefficient of `n₁ ⋯ n_d` is the coefficient of `x₁ ⋯ x_d` in the original — in particular
independent of the constant substituted, because the degree bound leaves a monomial whose last
`d` exponents are all nonzero no room for the first variable. -/
private theorem exists_eval_cons {d : ℕ} (Q : MvPolynomial (Fin (d + 1)) ℚ)
    (hQ : Q.totalDegree ≤ d) (a : ℚ) :
    ∃ R : MvPolynomial (Fin d) ℚ, R.totalDegree ≤ d ∧
      (∀ v : Fin d → ℚ, eval v R = eval (Fin.cons a v) Q) ∧
      R.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) =
        Q.coeff (Finsupp.equivFunOnFinite.symm (Fin.cons 0 fun _ => 1)) := by
  classical
  set tl : (Fin (d + 1) →₀ ℕ) → (Fin d →₀ ℕ) :=
    fun c => Finsupp.equivFunOnFinite.symm fun j => c j.succ with htl
  have htlapp : ∀ (c : Fin (d + 1) →₀ ℕ) (j : Fin d), tl c j = c j.succ := by
    intro c j; rw [htl]; simp
  set one : Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => 1 with hone
  set c₀ : Fin (d + 1) →₀ ℕ := Finsupp.equivFunOnFinite.symm (Fin.cons 0 fun _ => 1) with hc₀
  have hc₀zero : c₀ 0 = 0 := by rw [hc₀]; simp
  have hc₀succ : ∀ j : Fin d, c₀ j.succ = 1 := by intro j; rw [hc₀]; simp
  have hsum : ∀ c : Fin (d + 1) →₀ ℕ,
      c.sum (fun _ e => e) = c 0 + ∑ j : Fin d, c j.succ := by
    intro c
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_succ]
  refine ⟨∑ c ∈ Q.support, monomial (tl c) (Q.coeff c * a ^ c 0), ?_, ?_, ?_⟩
  · refine (totalDegree_finsetSum _ _).trans ?_
    simp only [Finset.sup_le_iff]
    intro c hc
    refine (totalDegree_monomial_le _ _).trans ?_
    have h1 : (tl c).sum (fun _ e => e) = ∑ j : Fin d, c j.succ := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      exact Finset.sum_congr rfl fun j _ => htlapp c j
    have h3 : c.sum (fun _ e => e) ≤ d := (le_totalDegree hc).trans hQ
    rw [hsum c] at h3
    refine le_trans (le_of_eq h1) ?_
    omega
  · intro v
    rw [map_sum, eval_eq']
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Fin.prod_univ_succ, Fin.cons_zero]
    simp only [Fin.cons_succ, htlapp]
    ring
  · rw [coeff_sum]
    have key : ∀ c ∈ Q.support,
        (monomial (tl c) (Q.coeff c * a ^ c 0)).coeff one =
          if c = c₀ then Q.coeff c else 0 := by
      intro c hc
      rw [coeff_monomial]
      by_cases hfull : tl c = one
      · have hd : ∑ j : Fin d, c j.succ = d := by
          have hall : ∀ j : Fin d, c j.succ = 1 := by
            intro j
            have := congrArg (fun g : Fin d →₀ ℕ => g j) hfull
            simpa [htlapp, hone] using this
          simp [hall]
        have hc0 : c 0 = 0 := by
          have h3 : c.sum (fun _ e => e) ≤ d := (le_totalDegree hc).trans hQ
          rw [hsum c, hd] at h3
          omega
        have hceq : c = c₀ := by
          refine Finsupp.ext fun p => ?_
          refine Fin.cases ?_ (fun j => ?_) p
          · rw [hc0, hc₀zero]
          · rw [hc₀succ]
            have := congrArg (fun g : Fin d →₀ ℕ => g j) hfull
            simpa [htlapp, hone] using this
        rw [ite_eq_left hfull, ite_eq_left hceq, hc0, pow_zero, mul_one]
      · have hne : c ≠ c₀ := by
          intro h
          refine hfull ?_
          refine Finsupp.ext fun j => ?_
          rw [htlapp, h, hc₀succ, hone]
          simp
        rw [ite_eq_right hfull, ite_eq_right hne]
    rw [Finset.sum_congr rfl key, Finset.sum_ite_eq' Q.support c₀ fun c => Q.coeff c]
    by_cases hmem : c₀ ∈ Q.support
    · rw [ite_eq_left hmem]
    · rw [ite_eq_right hmem]
      by_contra hcc
      exact hmem (mem_support_iff.2 fun h => hcc h.symm)

/-- **The mixed finite difference of a first difference vanishes below the degree of the
squarefree monomial.**  For a polynomial `Q` in `d + 1` variables of total degree at most `d`,
the alternating sum

`∑_{S ⊆ Fin d} (-1)^{d - |S|} (Q(1, 1_S) - Q(0, 1_S))`

of the first differences of `Q` in its first variable, taken at the indicator functions of the
subsets of the remaining `d` variables, is zero.

Each of the two mixed differences is the coefficient of `n₁ ⋯ n_d` in the restriction of `Q` to
the corresponding hyperplane, and the degree bound makes both of them the coefficient of
`x₁ ⋯ x_d` in `Q`: a monomial whose last `d` exponents are all nonzero already has degree `d`,
so the first variable cannot occur in it. -/
theorem sum_neg_one_pow_mul_sub_eval_cons_eq_zero {d : ℕ}
    (Q : MvPolynomial (Fin (d + 1)) ℚ) (hQ : Q.totalDegree ≤ d) :
    ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
        (eval (Fin.cons 1 fun j => if j ∈ S then (1 : ℚ) else 0) Q -
          eval (Fin.cons 0 fun j => if j ∈ S then (1 : ℚ) else 0) Q) = 0 := by
  obtain ⟨R₁, hR₁deg, hR₁eval, hR₁coeff⟩ := exists_eval_cons Q hQ 1
  obtain ⟨R₀, hR₀deg, hR₀eval, hR₀coeff⟩ := exists_eval_cons Q hQ 0
  have h₁ := sum_neg_one_pow_mul_eval_indicator_eq_coeff_one R₁ hR₁deg
  have h₀ := sum_neg_one_pow_mul_eval_indicator_eq_coeff_one R₀ hR₀deg
  calc ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
          (eval (Fin.cons 1 fun j => if j ∈ S then (1 : ℚ) else 0) Q -
            eval (Fin.cons 0 fun j => if j ∈ S then (1 : ℚ) else 0) Q)
      = (∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
            eval (fun j => if j ∈ S then (1 : ℚ) else 0) R₁) -
          ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
            eval (fun j => if j ∈ S then (1 : ℚ) else 0) R₀ := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [hR₁eval, hR₀eval]
        ring
    _ = 0 := by rw [h₁, h₀, hR₁coeff, hR₀coeff, sub_self]

/-- **Splitting the `d`-fold mixed finite difference on the membership of one index.**  For a
function `F` of `d + 1` variables and an index `i₀`, the alternating sum over the subsets
`S ⊆ Fin d` of

`F(1_S(i₀), 1_S) - F(0, 1_S) - F(1_S(i₀), 1_S with the i₀-th entry replaced by 0)`

is the alternating sum of the first difference `F(1, 1_S) - F(0, 1_S)`.

Pairing each subset `T` not containing `i₀` with `T ∪ {i₀}` makes the two sums agree term by
term: both pairs of terms involve only the four values of `F` at `(0, 1_T)`, `(1, 1_T)`,
`(0, 1_{T ∪ {i₀}})` and `(1, 1_{T ∪ {i₀}})`, with opposite signs on the two subsets. -/
private theorem sum_indicator_split {d : ℕ} (i₀ : Fin d) (F : (Fin (d + 1) → ℚ) → ℚ) :
    ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
        (F (Fin.cons (if i₀ ∈ S then 1 else 0) fun j => if j ∈ S then (1 : ℚ) else 0) -
          F (Fin.cons 0 fun j => if j ∈ S then (1 : ℚ) else 0) -
          F (Fin.cons (if i₀ ∈ S then 1 else 0)
            (Function.update (fun j => if j ∈ S then (1 : ℚ) else 0) i₀ 0))) =
      ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
        (F (Fin.cons 1 fun j => if j ∈ S then (1 : ℚ) else 0) -
          F (Fin.cons 0 fun j => if j ∈ S then (1 : ℚ) else 0)) := by
  classical
  have key : ∀ g : Finset (Fin d) → ℚ, ∑ S : Finset (Fin d), g S =
      ∑ T ∈ ((Finset.univ : Finset (Fin d)).erase i₀).powerset, (g T + g (insert i₀ T)) := by
    intro g
    rw [Finset.sum_add_distrib, ← Finset.sum_powerset_insert
      (Finset.notMem_erase i₀ Finset.univ) g, Finset.insert_erase (Finset.mem_univ i₀),
      Finset.powerset_univ]
  rw [key, key]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hi₀ : i₀ ∉ T := fun h => Finset.notMem_erase i₀ Finset.univ (Finset.mem_powerset.1 hT h)
  have hcard : (insert i₀ T).card = T.card + 1 := Finset.card_insert_of_notMem hi₀
  have hlt : T.card < d := by
    have h1 : T.card ≤ ((Finset.univ : Finset (Fin d)).erase i₀).card :=
      Finset.card_le_card (Finset.mem_powerset.1 hT)
    have h2 : ((Finset.univ : Finset (Fin d)).erase i₀).card = d - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, Fintype.card_fin]
    have h3 : 0 < d := i₀.pos
    omega
  have hsign : (-1 : ℚ) ^ (d - (T.card + 1)) = -(-1 : ℚ) ^ (d - T.card) := by
    have he : d - T.card = (d - (T.card + 1)) + 1 := by omega
    rw [he, pow_succ]
    ring
  have hzero : (if i₀ ∈ T then (1 : ℚ) else 0) = 0 := by rw [ite_eq_right hi₀]
  have hone : (if i₀ ∈ insert i₀ T then (1 : ℚ) else 0) = 1 :=
    ite_eq_left (Finset.mem_insert_self i₀ T)
  have hupd : Function.update (fun j => if j ∈ T then (1 : ℚ) else 0) i₀ 0 =
      fun j => if j ∈ T then (1 : ℚ) else 0 := by
    funext j
    by_cases hj : j = i₀
    · subst hj; rw [Function.update_self, ite_eq_right hi₀]
    · rw [Function.update_of_ne hj]
  have hupd' : Function.update (fun j => if j ∈ insert i₀ T then (1 : ℚ) else 0) i₀ 0 =
      fun j => if j ∈ T then (1 : ℚ) else 0 := by
    funext j
    by_cases hj : j = i₀
    · subst hj; rw [Function.update_self, ite_eq_right hi₀]
    · rw [Function.update_of_ne hj]
      congr 1
      simp [Finset.mem_insert, hj]
  rw [hcard, hsign, hzero, hone, hupd, hupd']
  ring

end MvPolynomial

namespace AlgebraicGeometry.Space

/-! ### Twisting a module by integer powers of a family of invertible modules -/

section Twist

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- Prefixing an invertible module to a family of invertible modules: every member of
`Fin.cons N L` is invertible. -/
instance isInvertible_cons {d : ℕ} (N : Modules.{u, u} B S hS F hF)
    (L : Fin d → Modules.{u, u} B S hS F hF)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property N]
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (p : Fin (d + 1)) :
    Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property
      ((Fin.cons N L : Fin (d + 1) → Modules.{u, u} B S hS F hF) p) := by
  induction p using Fin.cases with
  | zero => rw [Fin.cons_zero]; infer_instance
  | succ j => rw [Fin.cons_succ]; infer_instance

/-- Raising the universe of the sections preserves isomorphisms: the action of
`SheafOfModules.uliftForPresentation` on an isomorphism, built from
`SheafOfModules.uliftForPresentationMap` and its two functor laws. -/
def uliftForPresentationMapIso {A A' : Modules.{u, u} B S hS F hF} (e : A ≅ A') :
    SheafOfModules.uliftForPresentation.{u + 1, u, u, u, max (u + 1) w} A ≅
      SheafOfModules.uliftForPresentation.{u + 1, u, u, u, max (u + 1) w} A' where
  hom := SheafOfModules.uliftForPresentationMap.{u + 1, u, u, u, max (u + 1) w} e.hom
  inv := SheafOfModules.uliftForPresentationMap.{u + 1, u, u, u, max (u + 1) w} e.inv
  hom_inv_id := by
    rw [← SheafOfModules.uliftForPresentationMap_comp, e.hom_inv_id,
      SheafOfModules.uliftForPresentationMap_id]
  inv_hom_id := by
    rw [← SheafOfModules.uliftForPresentationMap_comp, e.inv_hom_id,
      SheafOfModules.uliftForPresentationMap_id]

/-- An isomorphism of twists, read in the universe in which the Euler characteristic is taken.
Stating it at `AlgebraicGeometry.Space.twistedModuleUlift` rather than at the unfolded
`SheafOfModules.uliftForPresentation` is what lets the coherence instances of the twists apply to
both of its sides. -/
def twistedModuleUliftIsoOfIso {d e : ℕ} (M : Modules.{u, u} B S hS F hF)
    (L : Fin d → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (n : Fin d → ℤ) (K : Fin e → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (K j)]
    (m : Fin e → ℤ)
    (iso : twistedModule B S hS F hF M L n ≅ twistedModule B S hS F hF M K m) :
    twistedModuleUlift.{u, w} B S hS F hF M L n ≅
      twistedModuleUlift.{u, w} B S hS F hF M K m :=
  uliftForPresentationMapIso.{u, w} B S hS F hF iso

/-- A twisting step preserves isomorphisms of the module being twisted. -/
def twistStepIso (L : Modules.{u, u} B S hS F hF)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property L]
    (m : ℤ) {M M' : Modules.{u, u} B S hS F hF} (e : M ≅ M') :
    twistStep B S hS F hF L m M ≅ twistStep B S hS F hF L m M' :=
  @Stacks.SheafOfModules.Invertible.tensorProductIso.{u, u + 1, u}
    (smallEtaleRingedSite B S hS F hF).C _ (smallEtaleRingedSite B S hS F hF).J
    (structurePresheaf B S hS F)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property _ _ _ _ _
        _ e (Iso.refl _)

/-- A twisting step by the zeroth tensor power is the identity: the zeroth power is the
structure sheaf and tensoring with it is the right unitor. -/
def twistStepZeroIso (L : Modules.{u, u} B S hS F hF)
    [_hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property L]
    (M : Modules.{u, u} B S hS F hF) :
    twistStep B S hS F hF L 0 M ≅ M :=
  @Stacks.SheafOfModules.Invertible.tensorProductRightUnitor.{u, u + 1, u}
    (smallEtaleRingedSite B S hS F hF).C _ (smallEtaleRingedSite B S hS F hF).J
    (structurePresheaf B S hS F)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property _ _ M

/-- Iterating twisting steps along a list preserves isomorphisms of the module. -/
def foldlTwistStepIso {d : ℕ} (L : Fin d → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (n : Fin d → ℤ) (l : List (Fin d)) :
    ∀ {M M' : Modules.{u, u} B S hS F hF}, (M ≅ M') →
      (l.foldl (fun N j => twistStep B S hS F hF (L j) (n j) N) M ≅
        l.foldl (fun N j => twistStep B S hS F hF (L j) (n j) N) M') := by
  induction l with
  | nil => exact fun e => e
  | cons j t ih => exact fun e => ih (twistStepIso B S hS F hF (L j) (n j) e)

/-- **Prefixing a trivial twist.**  The twist by the family `Fin.cons A L` at an exponent tuple
whose first entry is `0` is the twist by `L` alone. -/
def twistedModuleConsZeroIso {d : ℕ} (M : Modules.{u, u} B S hS F hF)
    (A : Modules.{u, u} B S hS F hF) (L : Fin d → Modules.{u, u} B S hS F hF)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property A]
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (n : Fin d → ℤ) :
    twistedModule B S hS F hF M (Fin.cons A L) (Fin.cons 0 n) ≅
      twistedModule B S hS F hF M L n := by
  have h : twistedModule B S hS F hF M (Fin.cons A L) (Fin.cons 0 n) =
      (List.finRange d).foldl (fun N j => twistStep B S hS F hF (L j) (n j) N)
        (twistStep B S hS F hF A 0 M) := by
    rw [twistedModule, List.finRange_succ, List.foldl_cons, List.foldl_map]
    simp only [Fin.cons_zero, Fin.cons_succ]
  rw [h, twistedModule]
  exact foldlTwistStepIso B S hS F hF L n (List.finRange d)
    (twistStepZeroIso B S hS F hF A M)


/-- Twisting by a module of the family is unchanged by replacing it with an equal one. -/
private theorem twistStep_congr {K K' : Modules.{u, u} B S hS F hF}
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property K]
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property K']
    (h : K = K') (m : ℤ) (M : Modules.{u, u} B S hS F hF) :
    twistStep B S hS F hF K m M = twistStep B S hS F hF K' m M := by
  subst h
  rfl

/-- **Two twisting steps commute**, by the associativity and the braiding of the sheaf tensor
product. -/
def twistStepSwapIso (A K : Modules.{u, u} B S hS F hF)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property A]
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property K]
    (a c : ℤ) (M : Modules.{u, u} B S hS F hF) :
    twistStep B S hS F hF A a (twistStep B S hS F hF K c M) ≅
      twistStep B S hS F hF K c (twistStep B S hS F hF A a M) :=
  @Stacks.SheafOfModules.Invertible.tensorProductAssociator.{u, u + 1, u}
      (smallEtaleRingedSite B S hS F hF).C _ (smallEtaleRingedSite B S hS F hF).J
      (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property _ _ _ _
          _ ≪≫
    (@Stacks.SheafOfModules.Invertible.tensorProductIso.{u, u + 1, u}
      (smallEtaleRingedSite B S hS F hF).C _ (smallEtaleRingedSite B S hS F hF).J
      (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property _ _ _ _
          _ _
      (Iso.refl _)
      (@Stacks.SheafOfModules.Invertible.tensorProductBraiding.{u, u + 1, u}
        (smallEtaleRingedSite B S hS F hF).C _ (smallEtaleRingedSite B S hS F hF).J
        (structurePresheaf B S hS F)
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property _ _ _
            _)) ≪≫
    (@Stacks.SheafOfModules.Invertible.tensorProductAssociator.{u, u + 1, u}
      (smallEtaleRingedSite B S hS F hF).C _ (smallEtaleRingedSite B S hS F hF).J
      (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property _ _ _ _
          _).symm

/-- A twisting step moved past a whole chain of twisting steps. -/
def foldlTwistStepCommIso {d : ℕ} (A : Modules.{u, u} B S hS F hF)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property A]
    (a : ℤ) (L : Fin d → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (n : Fin d → ℤ) (l : List (Fin d)) :
    ∀ M : Modules.{u, u} B S hS F hF,
      twistStep B S hS F hF A a (l.foldl (fun N j => twistStep B S hS F hF (L j) (n j) N) M) ≅
        l.foldl (fun N j => twistStep B S hS F hF (L j) (n j) N)
          (twistStep B S hS F hF A a M) := by
  induction l with
  | nil => exact fun M => Iso.refl _
  | cons j t ih =>
    exact fun M => (ih _).trans (foldlTwistStepIso B S hS F hF L n t
      (twistStepSwapIso B S hS F hF A (L j) a (n j) M))

/-- Dropping the first `i₀` indices of `Fin d` leaves `i₀` followed by the indices above it. -/
private theorem finRange_drop_eq_cons {d : ℕ} (i₀ : Fin d) :
    (List.finRange d).drop i₀ = i₀ :: (List.finRange d).drop (i₀ + 1) := by
  have hlen : (i₀ : ℕ) < (List.finRange d).length := by
    rw [List.length_finRange]
    exact i₀.isLt
  rw [List.drop_eq_getElem_cons hlen, List.getElem_finRange]
  congr 1

/-- **Splitting the twist at one index.**  The twist by a family of `d` invertible modules is the
chain of twisting steps at the indices above `i₀`, applied to the step at `i₀`, applied to the
chain at the indices below `i₀`. -/
private theorem twistedModule_eq_foldl_split {d : ℕ} (M : Modules.{u, u} B S hS F hF)
    (L : Fin d → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (n : Fin d → ℤ) (i₀ : Fin d) :
    twistedModule B S hS F hF M L n =
      ((List.finRange d).drop (i₀ + 1)).foldl
        (fun N j => twistStep B S hS F hF (L j) (n j) N)
        (twistStep B S hS F hF (L i₀) (n i₀)
          (((List.finRange d).take i₀).foldl
            (fun N j => twistStep B S hS F hF (L j) (n j) N) M)) := by
  have hdrop := finRange_drop_eq_cons i₀
  conv_lhs => rw [twistedModule, ← List.take_append_drop (i₀ : ℕ) (List.finRange d)]
  rw [List.foldl_append, hdrop, List.foldl_cons]


/-- Folding along a list only uses the values of the step function at the members of that
list. -/
private theorem foldl_congr_of_mem {α : Type*} {β : Type*} (f g : β → α → β)
    (l : List α) (h : ∀ a ∈ l, ∀ b, f b a = g b a) : ∀ b, l.foldl f b = l.foldl g b := by
  induction l with
  | nil => exact fun b => rfl
  | cons a t ih =>
    intro b
    rw [List.foldl_cons, List.foldl_cons, h a (List.mem_cons_self ..) b]
    exact ih (fun q hq => h q (List.mem_cons_of_mem a hq)) _

/-- Twisting along a list of indices only depends on the modules and exponents at those
indices. -/
private theorem foldl_twistStep_congr {d : ℕ} (K K' : Fin d → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (K j)]
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (K' j)]
    (m m' : Fin d → ℤ) (l : List (Fin d)) (h : ∀ j ∈ l, K j = K' j ∧ m j = m' j)
    (M : Modules.{u, u} B S hS F hF) :
    l.foldl (fun N j => twistStep B S hS F hF (K j) (m j) N) M =
      l.foldl (fun N j => twistStep B S hS F hF (K' j) (m' j) N) M :=
  foldl_congr_of_mem _ _ l
    (fun j hj N => by
      rw [(h j hj).2]
      exact twistStep_congr B S hS F hF (h j hj).1 (m' j) N) M

/-- Peeling the first twisting step off a twist by a family `Fin.cons A L`. -/
private theorem twistedModule_cons_eq {d : ℕ} (M : Modules.{u, u} B S hS F hF)
    (A : Modules.{u, u} B S hS F hF) (L : Fin d → Modules.{u, u} B S hS F hF)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property A]
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (a : ℤ) (n : Fin d → ℤ) :
    twistedModule B S hS F hF M (Fin.cons A L) (Fin.cons a n) =
      (List.finRange d).foldl (fun N j => twistStep B S hS F hF (L j) (n j) N)
        (twistStep B S hS F hF A a M) := by
  rw [twistedModule, List.finRange_succ, List.foldl_cons, List.foldl_map]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- The index `i₀` occurs neither among the indices below it nor among those above it. -/
private theorem notMem_take_and_drop {d : ℕ} (i₀ : Fin d) :
    i₀ ∉ (List.finRange d).take i₀ ∧ i₀ ∉ (List.finRange d).drop (i₀ + 1) := by
  have hdrop := finRange_drop_eq_cons i₀
  have hsplit : List.finRange d =
      (List.finRange d).take i₀ ++ i₀ :: (List.finRange d).drop (i₀ + 1) := by
    rw [← hdrop, List.take_append_drop]
  have hnd : ((List.finRange d).take i₀ ++
      i₀ :: (List.finRange d).drop (i₀ + 1)).Nodup := by
    rw [← hsplit]
    exact List.nodup_finRange d
  obtain ⟨_, hnd₂, hdisj⟩ := List.nodup_append.1 hnd
  exact ⟨fun hmem => hdisj i₀ hmem i₀ (List.mem_cons_self ..) rfl, (List.nodup_cons.1 hnd₂).1⟩

/-- **A twist by a tensor product split into two twists.**  At exponent `1`, twisting by `A` and
then by `K` is twisting by a module isomorphic to `K ⊗ A`, by the associativity of the sheaf
tensor product and the identification of the first tensor power. -/
def twistStepOneTensorIso (A K P : Modules.{u, u} B S hS F hF)
    [hA : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property A]
    [hK : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property K]
    [hPinv : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property P]
    (hiso : P ≅ ((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS F hF).O).obj K).obj A)
    (M : Modules.{u, u} B S hS F hF) :
    twistStep B S hS F hF A 1 (twistStep B S hS F hF K 1 M) ≅
      twistStep B S hS F hF P 1 M :=
  @Stacks.SheafOfModules.Invertible.tensorProductAssociator.{u, u + 1, u}
      (smallEtaleRingedSite B S hS F hF).C _ (smallEtaleRingedSite B S hS F hF).J
      (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property _ _ _ _
          _ ≪≫
    @Stacks.SheafOfModules.Invertible.tensorProductIso.{u, u + 1, u}
      (smallEtaleRingedSite B S hS F hF).C _ (smallEtaleRingedSite B S hS F hF).J
      (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property _ _ _ _
          _ _
      (Iso.refl _)
      ((@Stacks.SheafOfModules.Invertible.tensorProductIso.{u, u + 1, u}
      (smallEtaleRingedSite B S hS F hF).C _ (smallEtaleRingedSite B S hS F hF).J
      (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property _ _ _ _
          _ _
        (@Stacks.SheafOfModules.Invertible.tensorPowerOneIso.{u, u + 1, u}
      (smallEtaleRingedSite B S hS F hF).C _ (smallEtaleRingedSite B S hS F hF).J
      (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property _ _ K
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ K hK))
        (@Stacks.SheafOfModules.Invertible.tensorPowerOneIso.{u, u + 1, u}
      (smallEtaleRingedSite B S hS F hF).C _ (smallEtaleRingedSite B S hS F hF).J
      (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property _ _ A
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ A hA))) ≪≫ hiso.symm ≪≫
        (@Stacks.SheafOfModules.Invertible.tensorPowerOneIso.{u, u + 1, u}
      (smallEtaleRingedSite B S hS F hF).C _ (smallEtaleRingedSite B S hS F hF).J
      (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property _ _ P
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ P hPinv)).symm)

/-- **Splitting one factor of a twist**, granted the comparison of the two twisting steps at the
modified index: if `L'` agrees with `L` away from `i₀` and `m` agrees with `n` away from `i₀`,
the twist by `Fin.cons A L'` at `Fin.cons a m` is the twist by `L` at `n`. -/
private def twistedModuleConsSplitAux {d : ℕ} (M : Modules.{u, u} B S hS F hF) (i₀ : Fin d)
    (L L' : Fin d → Modules.{u, u} B S hS F hF) (A : Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L' j)]
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property A]
    (hagree : ∀ j, j ≠ i₀ → L' j = L j) (a : ℤ) (m n : Fin d → ℤ)
    (hmn : ∀ j, j ≠ i₀ → m j = n j)
    (hinner : ∀ N : Modules.{u, u} B S hS F hF,
      twistStep B S hS F hF A a (twistStep B S hS F hF (L' i₀) (m i₀) N) ≅
        twistStep B S hS F hF (L i₀) (n i₀) N) :
    twistedModule B S hS F hF M (Fin.cons A L') (Fin.cons a m) ≅
      twistedModule B S hS F hF M L n := by
  obtain ⟨htake, hdrop⟩ := notMem_take_and_drop i₀
  have hcongr : ∀ (l : List (Fin d)) (_ : i₀ ∉ l) (N : Modules.{u, u} B S hS F hF),
      l.foldl (fun P j => twistStep B S hS F hF (L' j) (m j) P) N =
        l.foldl (fun P j => twistStep B S hS F hF (L j) (n j) P) N :=
    fun l hl N => foldl_twistStep_congr B S hS F hF L' L m n l
      (fun j hj => have hne : j ≠ i₀ := fun h => hl (h ▸ hj); ⟨hagree j hne, hmn j hne⟩) N
  refine (eqToIso (twistedModule_cons_eq B S hS F hF M A L' a m)).trans ?_
  refine (eqToIso (twistedModule_eq_foldl_split B S hS F hF
    (twistStep B S hS F hF A a M) L' m i₀)).trans ?_
  refine ?_ ≪≫ (eqToIso (twistedModule_eq_foldl_split B S hS F hF M L n i₀)).symm
  rw [hcongr _ hdrop, hcongr _ htake]
  refine foldlTwistStepIso B S hS F hF L n _ ?_
  refine (twistStepIso B S hS F hF (L' i₀) (m i₀)
    (foldlTwistStepCommIso B S hS F hF A a L n ((List.finRange d).take i₀) M).symm).trans ?_
  exact (twistStepSwapIso B S hS F hF A (L' i₀) a (m i₀) _).symm.trans (hinner _)

/-- **A twist by a tensor product of two invertible modules splits.**  If `L'` agrees with `L`
away from `i₀`, if `L_{i₀} ≅ L'_{i₀} ⊗ A` and if the `i₀`-th exponent is `1`, the twist by
`Fin.cons A L'` with that exponent repeated in the new slot is the twist by `L`. -/
private def twistedModuleConsSplitOneIso {d : ℕ} (M : Modules.{u, u} B S hS F hF) (i₀ : Fin d)
    (L L' : Fin d → Modules.{u, u} B S hS F hF) (A : Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L' j)]
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property A]
    (hagree : ∀ j, j ≠ i₀ → L' j = L j)
    (hiso : L i₀ ≅ ((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS F hF).O).obj (L' i₀)).obj A)
    (n : Fin d → ℤ) (hn : n i₀ = 1) :
    twistedModule B S hS F hF M (Fin.cons A L') (Fin.cons (n i₀) n) ≅
      twistedModule B S hS F hF M L n :=
  twistedModuleConsSplitAux B S hS F hF M i₀ L L' A hagree (n i₀) n n (fun _ _ => rfl) fun N => by
    rw [hn]
    exact twistStepOneTensorIso B S hS F hF A (L' i₀) (L i₀) hiso N

/-- **A twist whose exponent at the modified index is zero.**  If `L'` agrees with `L` away from
`i₀` and the `i₀`-th exponent is `0`, the twist by `Fin.cons A L'` with that exponent repeated in
the new slot is the twist by `L`: all three steps at `i₀` are trivial. -/
private def twistedModuleConsSplitZeroIso {d : ℕ} (M : Modules.{u, u} B S hS F hF) (i₀ : Fin d)
    (L L' : Fin d → Modules.{u, u} B S hS F hF) (A : Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L' j)]
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property A]
    (hagree : ∀ j, j ≠ i₀ → L' j = L j) (n : Fin d → ℤ) (hn : n i₀ = 0) :
    twistedModule B S hS F hF M (Fin.cons A L') (Fin.cons (n i₀) n) ≅
      twistedModule B S hS F hF M L n :=
  twistedModuleConsSplitAux B S hS F hF M i₀ L L' A hagree (n i₀) n n (fun _ _ => rfl) fun N => by
    rw [hn]
    exact (twistStepZeroIso B S hS F hF A _).trans
      ((twistStepZeroIso B S hS F hF (L' i₀) N).trans
        (twistStepZeroIso B S hS F hF (L i₀) N).symm)

/-- **Reading the new slot as the modified factor.**  Let `L'` and `L''` agree away from `i₀`,
with `L''_{i₀} = A`.  The twist by `Fin.cons A L'` at an exponent tuple whose `i₀`-th entry is
`0` and whose new slot carries `n i₀` is the twist by `L''` at `n`. -/
private def twistedModuleConsUpdateIso {d : ℕ} (M : Modules.{u, u} B S hS F hF) (i₀ : Fin d)
    (L' L'' : Fin d → Modules.{u, u} B S hS F hF) (A : Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L' j)]
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O).property (L'' j)]
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property A]
    (hagree : ∀ j, j ≠ i₀ → L' j = L'' j) (hA : L'' i₀ = A) (n : Fin d → ℤ) :
    twistedModule B S hS F hF M (Fin.cons A L')
        (Fin.cons (n i₀) (Function.update n i₀ 0)) ≅
      twistedModule B S hS F hF M L'' n :=
  twistedModuleConsSplitAux B S hS F hF M i₀ L'' L' A hagree (n i₀)
    (Function.update n i₀ 0) n (fun _ hj => Function.update_of_ne hj _ _) fun N => by
    rw [Function.update_self]
    exact (twistStepIso B S hS F hF A (n i₀) (twistStepZeroIso B S hS F hF (L' i₀) N)).trans
      (eqToIso (twistStep_congr B S hS F hF hA.symm (n i₀) N))

end Twist

/-! ### The intersection number -/

section IntersectionNumber

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (X Z : AlgebraicSpaces B (Spec (.of k)) hk)

/-- **Stacks 0EDF.** The intersection number `(L₁ ⋯ L_d · Z)` of `d` invertible
`𝒪_X`-modules against a closed subspace `i : Z ⟶ X` of dimension `d` of a proper algebraic
space `X` over a field `k`: the coefficient of `n₁ ⋯ n_d` in the numerical polynomial
`χ(X, i_*𝒪_Z ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_d^{⊗ n_d})`, computed as the `d`-fold mixed finite difference

`∑_{T ⊆ {1, …, d}} (-1)^{d - |T|} χ(X, i_*𝒪_Z ⊗ ⨂_{j ∈ T} L_j)`

of that function.  This is an honest integer: only finitely many values of the function are
used, so neither polynomiality nor a choice of representing polynomial enters. -/
@[stacks 0EDF, sga "6 X 4.4" "defn, algebraic spaces"]
def intersectionNumber (d : ℕ) (f : X.1 ⟶ yoneda.obj (baseObject k B hk))
    (hf : IsProper B (Spec (.of k)) hk f) (i : Z ⟶ X)
    (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (_hd : dimension B (Spec (.of k)) hk Z.1 Z.2 = d)
    (L : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)] :
    ℤ :=
  letI : ∀ n : Fin d → ℤ, IsCoherent B (Spec (.of k)) hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
        (structureSheafPushforward B (Spec (.of k)) hk i) L n) := fun n =>
    isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w} k B hk X Z f hf i hi L n
  ∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) *
    eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
        (structureSheafPushforward B (Spec (.of k)) hk i) L fun j => if j ∈ T then 1 else 0)

/-- The defining alternating sum of the intersection number. -/
theorem intersectionNumber_eq_sum (d : ℕ) (f : X.1 ⟶ yoneda.obj (baseObject k B hk))
    (hf : IsProper B (Spec (.of k)) hk f) (i : Z ⟶ X)
    (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (hd : dimension B (Spec (.of k)) hk Z.1 Z.2 = d)
    (L : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)] :
    intersectionNumber.{u, w} k B hk X Z d f hf i hi hd L =
      ∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) *
        @eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
            (structureSheafPushforward B (Spec (.of k)) hk i) L
            fun j => if j ∈ T then 1 else 0)
    (isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w} k B hk X Z f hf i hi L _) :=
  rfl

/-- **Stacks 0EDF, the coefficient of `n₁ ⋯ n_d`.**  If a rational polynomial `P` in `d`
variables of total degree at most `d` takes the Euler characteristics
`χ(X, i_*𝒪_Z ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_d^{⊗ n_d})` as its values at the integral tuples, then the
intersection number `(L₁ ⋯ L_d · Z)` is the coefficient of `n₁ ⋯ n_d` in `P`.

This is the source's own description of the intersection number.  The existence of such a `P`,
which is Stacks 0DN4, is not assumed: the statement is unconditional in `P`, and the proof is
the monomial computation
`MvPolynomial.sum_neg_one_pow_mul_eval_indicator_eq_coeff_one`. -/
@[stacks 0EDF "the coefficient of n_1 ⋯ n_d", sga "6 X 4.4" "defn, algebraic spaces"]
theorem intersectionNumber_eq_coeff (d : ℕ) (f : X.1 ⟶ yoneda.obj (baseObject k B hk))
    (hf : IsProper B (Spec (.of k)) hk f) (i : Z ⟶ X)
    (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (hd : dimension B (Spec (.of k)) hk Z.1 Z.2 = d)
    (L : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)]
    (P : MvPolynomial (Fin d) ℚ)
    (hP : ∀ n : Fin d → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
      ((@eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
          (structureSheafPushforward B (Spec (.of k)) hk i) L n)
          (isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w}
            k B hk X Z f hf i hi L n) : ℤ) : ℚ))
    (hdeg : P.totalDegree ≤ d) :
    ((intersectionNumber.{u, w} k B hk X Z d f hf i hi hd L : ℤ) : ℚ) =
      P.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) := by
  let : ∀ n : Fin d → ℤ, IsCoherent B (Spec (.of k)) hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
        (structureSheafPushforward B (Spec (.of k)) hk i) L n) := fun n =>
    isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w} k B hk X Z f hf i hi L n
  have hval : ∀ T : Finset (Fin d),
      MvPolynomial.eval (fun j => if j ∈ T then (1 : ℚ) else 0) P =
        ((eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
            (structureSheafPushforward B (Spec (.of k)) hk i) L
            fun j => if j ∈ T then 1 else 0) : ℤ) : ℚ) := by
    intro T
    have h := hP fun j => if j ∈ T then (1 : ℤ) else 0
    rw [show (fun j : Fin d => (((if j ∈ T then (1 : ℤ) else 0) : ℤ) : ℚ)) =
        fun j : Fin d => if j ∈ T then (1 : ℚ) else 0 from
      funext fun j => by split_ifs <;> simp] at h
    exact h
  rw [← MvPolynomial.sum_neg_one_pow_mul_eval_indicator_eq_coeff_one P hdeg,
    intersectionNumber_eq_sum]
  push_cast
  exact Finset.sum_congr rfl fun T _ => by rw [hval T]

/-- **Integrality of the coefficient of `n₁ ⋯ n_d`.**  The coefficient of
`n₁ ⋯ n_d` in a rational polynomial of total degree at most `d` taking the Euler characteristics
`χ(X, i_*𝒪_Z ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_d^{⊗ n_d})` as its values at the integral tuples is the cast of
an integer, namely of `AlgebraicGeometry.Space.intersectionNumber`.

That coefficient is a priori only rational, and integrality is special to it: a numerical
polynomial such as `n (n - 1) / 2` has coefficients which are not integers, and it is the degree
bound that makes the coefficient of the squarefree monomial a mixed finite difference of
finitely many integer values.

Stacks 0EDG, where the representing polynomial is supplied by Stacks 0DN4, is
`AlgebraicGeometry.Space.exists_eval_eq_eulerCharacteristic_and_exists_intCast_eq_coeff_one`. -/
theorem exists_intCast_eq_coeff_one (d : ℕ) (f : X.1 ⟶ yoneda.obj (baseObject k B hk))
    (hf : IsProper B (Spec (.of k)) hk f) (i : Z ⟶ X)
    (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (hd : dimension B (Spec (.of k)) hk Z.1 Z.2 = d)
    (L : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)]
    (P : MvPolynomial (Fin d) ℚ)
    (hP : ∀ n : Fin d → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
      ((@eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
          (structureSheafPushforward B (Spec (.of k)) hk i) L n)
          (isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w}
            k B hk X Z f hf i hi L n) : ℤ) : ℚ))
    (hdeg : P.totalDegree ≤ d) :
    ∃ m : ℤ, P.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) = (m : ℚ) :=
  ⟨intersectionNumber.{u, w} k B hk X Z d f hf i hi hd L,
    (intersectionNumber_eq_coeff.{u, w} k B hk X Z d f hf i hi hd L P hP hdeg).symm⟩

/-- **Stacks 0EDF, the self-intersection notation `(L^d · Z)`.**  The intersection number of a
single invertible `𝒪_X`-module `L` repeated `d` times against a closed subspace `i : Z ⟶ X` of
dimension `d`. -/
@[stacks 0EDF "the self-intersection notation (L^d · Z)"]
def selfIntersectionNumber (d : ℕ) (f : X.1 ⟶ yoneda.obj (baseObject k B hk))
    (hf : IsProper B (Spec (.of k)) hk f) (i : Z ⟶ X)
    (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (hd : dimension B (Spec (.of k)) hk Z.1 Z.2 = d)
    (L : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property L] :
    ℤ :=
  intersectionNumber.{u, w} k B hk X Z d f hf i hi hd fun _ => L

/-- **Additivity of the intersection number, given the numerical polynomial of the split
family.**
Let `k` be a field, let `X` be a proper algebraic space over `k`, let `i : Z ⟶ X` be a closed
subspace of dimension `d` and let `L₁, …, L_d` be invertible `𝒪_X`-modules.  Let `L'` and `L''`
be two families agreeing with `L` away from one index `i₀` and satisfying
`L_{i₀} ≅ L_{i₀}' ⊗ L_{i₀}''`.  Then

`(L₁ ⋯ L_{i₀} ⋯ L_d · Z) = (L₁ ⋯ L_{i₀}' ⋯ L_d · Z) + (L₁ ⋯ L_{i₀}'' ⋯ L_d · Z)`.

The mechanism is the source's.  The Euler characteristics of the twists of `i_*𝒪_Z` by the
`d + 1` invertible modules `L_{i₀}'', L_1', …, L_d'` are the values of a rational polynomial `Q`
of total degree at most `d` in `d + 1` variables, the hypotheses `Q`, `hQ` and `hQdeg`, which
Stacks 0DN4 supplies in
`AlgebraicGeometry.Space.intersectionNumber_eq_add_intersectionNumber_of_iso_tensorSheaf`
(Stacks 0EDH); the three intersection numbers are then the
three mixed finite differences of `Q` obtained by tying the two new variables together, by
setting the second to zero, and by setting the first to zero.  Their alternating combination is
the `(d + 1)`-fold mixed finite difference of `Q`, which vanishes because the squarefree monomial
in `d + 1` variables has degree `d + 1`;
this is `MvPolynomial.sum_neg_one_pow_mul_sub_eval_cons_eq_zero`.

The three comparisons of the twists by the split family with the twists by `L`, `L'` and `L''`
are proved: at the indicator tuples only the exponents `0` and `1` occur, where the constraints
of the sheaf tensor product suffice and no multiplication of tensor powers is needed.  See the
implementation notes. -/
theorem intersectionNumber_eq_add_of_iso_tensorSheaf (d : ℕ)
    (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f)
    (i : Z ⟶ X) (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (hd : dimension B (Spec (.of k)) hk Z.1 Z.2 = d) (i₀ : Fin d)
    (L L' L'' : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)]
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L' j)]
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L'' j)]
    [∀ n : Fin d → ℤ, IsCoherent B (Spec (.of k)) hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
        (structureSheafPushforward B (Spec (.of k)) hk i) L n)]
    [∀ n : Fin d → ℤ, IsCoherent B (Spec (.of k)) hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
        (structureSheafPushforward B (Spec (.of k)) hk i) L' n)]
    [∀ n : Fin d → ℤ, IsCoherent B (Spec (.of k)) hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
        (structureSheafPushforward B (Spec (.of k)) hk i) L'' n)]
    [∀ m : Fin (d + 1) → ℤ, IsCoherent B (Spec (.of k)) hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
        (structureSheafPushforward B (Spec (.of k)) hk i) (Fin.cons (L'' i₀) L') m)]
    (hL' : ∀ j, j ≠ i₀ → L' j = L j) (hL'' : ∀ j, j ≠ i₀ → L'' j = L j)
    (hL : L i₀ ≅ (((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).obj (L' i₀)).obj (L'' i₀) :
        Modules.{u, u} B (Spec (.of k)) hk X.1 X.2))
    (Q : MvPolynomial (Fin (d + 1)) ℚ) (hQdeg : Q.totalDegree ≤ d)
    (hQ : ∀ m : Fin (d + 1) → ℤ, MvPolynomial.eval (fun p => (m p : ℚ)) Q =
      ((eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
          (structureSheafPushforward B (Spec (.of k)) hk i) (Fin.cons (L'' i₀) L') m) : ℤ) : ℚ)) :
    intersectionNumber.{u, w} k B hk X Z d f hf i hi hd L =
      intersectionNumber.{u, w} k B hk X Z d f hf i hi hd L' +
        intersectionNumber.{u, w} k B hk X Z d f hf i hi hd L'' := by
  classical
  have hsplit : ∀ S : Finset (Fin d),
      eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
            (structureSheafPushforward B (Spec (.of k)) hk i) (Fin.cons (L'' i₀) L')
            (Fin.cons (if i₀ ∈ S then 1 else 0) fun j => if j ∈ S then 1 else 0)) =
        eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
            (structureSheafPushforward B (Spec (.of k)) hk i) L
            fun j => if j ∈ S then 1 else 0) := by
    intro S
    by_cases hmem : i₀ ∈ S
    · exact eulerCharacteristic_congr.{u, w} k B hk X.1 X.2 f hf
        (twistedModuleUliftIsoOfIso.{u, w} B (Spec (.of k)) hk X.1 X.2
          (structureSheafPushforward B (Spec (.of k)) hk i) (Fin.cons (L'' i₀) L')
          (Fin.cons (if i₀ ∈ S then 1 else 0) fun j => if j ∈ S then 1 else 0) L
          (fun j => if j ∈ S then 1 else 0)
          (twistedModuleConsSplitOneIso B (Spec (.of k)) hk X.1 X.2
            (structureSheafPushforward B (Spec (.of k)) hk i) i₀ L L' (L'' i₀) hL' hL
            (fun j => if j ∈ S then 1 else 0) (by rw [ite_eq_left hmem])))
    · exact eulerCharacteristic_congr.{u, w} k B hk X.1 X.2 f hf
        (twistedModuleUliftIsoOfIso.{u, w} B (Spec (.of k)) hk X.1 X.2
          (structureSheafPushforward B (Spec (.of k)) hk i) (Fin.cons (L'' i₀) L')
          (Fin.cons (if i₀ ∈ S then 1 else 0) fun j => if j ∈ S then 1 else 0) L
          (fun j => if j ∈ S then 1 else 0)
          (twistedModuleConsSplitZeroIso B (Spec (.of k)) hk X.1 X.2
            (structureSheafPushforward B (Spec (.of k)) hk i) i₀ L L' (L'' i₀) hL'
            (fun j => if j ∈ S then 1 else 0) (by rw [ite_eq_right hmem])))
  have hsplit' : ∀ S : Finset (Fin d),
      eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
            (structureSheafPushforward B (Spec (.of k)) hk i) (Fin.cons (L'' i₀) L')
            (Fin.cons 0 fun j => if j ∈ S then 1 else 0)) =
        eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
            (structureSheafPushforward B (Spec (.of k)) hk i) L'
            fun j => if j ∈ S then 1 else 0) := fun S =>
    eulerCharacteristic_congr.{u, w} k B hk X.1 X.2 f hf
      (twistedModuleUliftIsoOfIso.{u, w} B (Spec (.of k)) hk X.1 X.2
        (structureSheafPushforward B (Spec (.of k)) hk i) (Fin.cons (L'' i₀) L')
        (Fin.cons 0 fun j => if j ∈ S then 1 else 0) L' (fun j => if j ∈ S then 1 else 0)
        (twistedModuleConsZeroIso B (Spec (.of k)) hk X.1 X.2
          (structureSheafPushforward B (Spec (.of k)) hk i) (L'' i₀) L'
          fun j => if j ∈ S then 1 else 0))
  have hsplit'' : ∀ S : Finset (Fin d),
      eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
            (structureSheafPushforward B (Spec (.of k)) hk i) (Fin.cons (L'' i₀) L')
            (Fin.cons (if i₀ ∈ S then 1 else 0)
              (Function.update (fun j => if j ∈ S then 1 else 0) i₀ 0))) =
        eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
            (structureSheafPushforward B (Spec (.of k)) hk i) L''
            fun j => if j ∈ S then 1 else 0) := fun S =>
    eulerCharacteristic_congr.{u, w} k B hk X.1 X.2 f hf
      (twistedModuleUliftIsoOfIso.{u, w} B (Spec (.of k)) hk X.1 X.2
        (structureSheafPushforward B (Spec (.of k)) hk i) (Fin.cons (L'' i₀) L')
        (Fin.cons (if i₀ ∈ S then 1 else 0)
          (Function.update (fun j => if j ∈ S then 1 else 0) i₀ 0)) L''
        (fun j => if j ∈ S then 1 else 0)
        (twistedModuleConsUpdateIso B (Spec (.of k)) hk X.1 X.2
          (structureSheafPushforward B (Spec (.of k)) hk i) i₀ L' L'' (L'' i₀)
          (fun j hj => (hL' j hj).trans (hL'' j hj).symm) rfl
          fun j => if j ∈ S then 1 else 0))
  have hiteq : ∀ (S : Finset (Fin d)) (j : Fin d),
      (((if j ∈ S then (1 : ℤ) else 0) : ℤ) : ℚ) = if j ∈ S then (1 : ℚ) else 0 := by
    intro S j; split_ifs <;> simp
  have hupdcast : ∀ (S : Finset (Fin d)) (j : Fin d),
      ((Function.update (fun l => if l ∈ S then (1 : ℤ) else 0) i₀ 0 j : ℤ) : ℚ) =
        Function.update (fun l => if l ∈ S then (1 : ℚ) else 0) i₀ 0 j := by
    intro S j
    by_cases hj : j = i₀
    · subst hj; simp
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]; exact hiteq S j
  have hval : ∀ (ε : ℤ) (v : Fin d → ℤ) (ε' : ℚ) (v' : Fin d → ℚ), (ε : ℚ) = ε' →
      (∀ j, (v j : ℚ) = v' j) →
      MvPolynomial.eval (Fin.cons ε' v') Q =
        ((eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
            (structureSheafPushforward B (Spec (.of k)) hk i) (Fin.cons (L'' i₀) L')
            (Fin.cons ε v)) : ℤ) : ℚ) := by
    intro ε v ε' v' hε hv
    have h := hQ (Fin.cons ε v)
    rwa [show (fun p : Fin (d + 1) => (((Fin.cons ε v : Fin (d + 1) → ℤ) p : ℤ) : ℚ)) =
      Fin.cons ε' v' from funext fun p => Fin.cases (by simpa using hε)
        (fun j => by simpa using hv j) p] at h
  have hA := fun S : Finset (Fin d) => hval (if i₀ ∈ S then 1 else 0)
    (fun j => if j ∈ S then 1 else 0) _ _ (hiteq S i₀) (hiteq S)
  have hB := fun S : Finset (Fin d) => hval 0 (fun j => if j ∈ S then 1 else 0) _ _
    Int.cast_zero (hiteq S)
  have hC := fun S : Finset (Fin d) => hval (if i₀ ∈ S then 1 else 0)
    (Function.update (fun j => if j ∈ S then 1 else 0) i₀ 0) _ _ (hiteq S i₀) (hupdcast S)
  have key : ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
      (MvPolynomial.eval (Fin.cons (if i₀ ∈ S then (1 : ℚ) else 0)
            fun j => if j ∈ S then (1 : ℚ) else 0) Q -
          MvPolynomial.eval (Fin.cons 0 fun j => if j ∈ S then (1 : ℚ) else 0) Q -
          MvPolynomial.eval (Fin.cons (if i₀ ∈ S then (1 : ℚ) else 0)
            (Function.update (fun j => if j ∈ S then (1 : ℚ) else 0) i₀ 0)) Q) = 0 := by
    rw [MvPolynomial.sum_indicator_split i₀ fun x => MvPolynomial.eval x Q,
      MvPolynomial.sum_neg_one_pow_mul_sub_eval_cons_eq_zero Q hQdeg]
  have expand : ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
      (MvPolynomial.eval (Fin.cons (if i₀ ∈ S then (1 : ℚ) else 0)
            fun j => if j ∈ S then (1 : ℚ) else 0) Q -
          MvPolynomial.eval (Fin.cons 0 fun j => if j ∈ S then (1 : ℚ) else 0) Q -
          MvPolynomial.eval (Fin.cons (if i₀ ∈ S then (1 : ℚ) else 0)
            (Function.update (fun j => if j ∈ S then (1 : ℚ) else 0) i₀ 0)) Q) =
      (∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
          ((eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf
            (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
              (structureSheafPushforward B (Spec (.of k)) hk i) L
              fun j => if j ∈ S then 1 else 0) : ℤ) : ℚ)) -
        (∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
          ((eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf
            (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
              (structureSheafPushforward B (Spec (.of k)) hk i) L'
              fun j => if j ∈ S then 1 else 0) : ℤ) : ℚ)) -
        ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
          ((eulerCharacteristic.{u, w} k B hk X.1 X.2 f hf
            (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
              (structureSheafPushforward B (Spec (.of k)) hk i) L''
              fun j => if j ∈ S then 1 else 0) : ℤ) : ℚ) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [hA S, hB S, hC S, hsplit S, hsplit' S, hsplit'' S]
    ring
  refine Int.cast_injective (α := ℚ) ?_
  rw [intersectionNumber_eq_sum.{u, w} k B hk X Z d f hf i hi hd L,
    intersectionNumber_eq_sum.{u, w} k B hk X Z d f hf i hi hd L',
    intersectionNumber_eq_sum.{u, w} k B hk X Z d f hf i hi hd L'']
  push_cast
  linarith [key, expand]

end IntersectionNumber

end AlgebraicGeometry.Space

end
