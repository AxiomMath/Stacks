module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ResolvingTower

/-!
# The rule of the Tate construction, and the finite Tate resolution

Over a Noetherian ring and a finite set of degree-zero variables the coefficient algebra
`MvPolynomial σ R` is Noetherian, and then every rung of the degree-by-degree construction has
finitely many variables to adjoin: in degree one a finite generating family of the kernel of the
presentation, and in degree `k + 1` a finite generating family of the cycles of degree `k` as a
module over the coefficients (`IndexedPresentation.fg_cycleModule`).

That is the rule this file builds. It is chosen, not quantified over: a rule has to be a function
of the family and the boundary it is handed, and the finite generating families exist but are not
canonical, so the choice is made once and its properties read off `Classical.choose_spec`. Where
the data is not available — a family with infinitely many variables in some degree, which the
construction never produces but a rule must still accept — the rule adjoins nothing, which
satisfies the two conditions that have to hold for every family.

Feeding the rule to `isResolvingBoundary_limitBoundary` and that to
`exists_finite_tateResolution_of_isResolvingBoundary` gives the finite assertion of
[Stacks, Tag 09PN].

## Main definitions

* `DividedPowers.TateResolution.tateRule` — the rule of the Tate construction.

## Main results

* `DividedPowers.TateResolution.isResolvingRule_tateRule` — the rule is resolving.
* `DividedPowers.TateResolution.exists_finite_tateResolution_of_tateRule` — a finite-type
  algebra over a Noetherian ring has a Tate resolution with finitely many variables in every
  degree, including degree zero.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v z

section Family

variable {P : Type v} [CommRing P]

/-- A finitely generated submodule has a finite family of its own elements, indexed by an
initial segment of the naturals, of which every element of the submodule is an explicit
combination. -/
private theorem exists_fin_family_of_fg {M : Type z} [AddCommGroup M] [Module P M]
    (N : Submodule P M) (hN : N.FG) :
    ∃ (m : ℕ) (g : ℕ → M), (∀ i : ℕ, g i ∈ N) ∧
      ∀ y ∈ N, ∃ c : ℕ → P, y = ∑ i : Fin m, c i.1 • g i.1 := by
  classical
  obtain ⟨m, v, hv⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hN
  refine ⟨m, fun i => if h : i < m then v ⟨i, h⟩ else 0, ?_, ?_⟩
  · intro i
    dsimp only
    by_cases h : i < m
    · rw [dite_eq_left h, ← hv]
      exact Submodule.subset_span ⟨⟨i, h⟩, rfl⟩
    · rw [dite_eq_right h]
      exact N.zero_mem
  · intro y hy
    rw [← hv] at hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun P).mp hy
    refine ⟨fun i => if h : i < m then c ⟨i, h⟩ else 0, ?_⟩
    rw [← hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    rw [dite_eq_left i.isLt, dite_eq_left i.isLt]

end Family

section Rule

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
  {σ : Type (max u v)} (φ : MvPolynomial σ R →ₐ[R] S) {f : ℕ → Type (max u v)}

/-- Everything the rule's choice at one family, boundary and degree has to provide: homogeneous
cycles, lying over the kernel of `φ` in degree zero, and spanning the kernel in degree zero and
the cycles in every positive degree. -/
public def GoodData (T : IndexedPresentation.{u, max u v, v} R (MvPolynomial σ R) f)
    (b : (Σ n : ℕ, f n) → T.A) (hb : ∀ j, b j ∈ T.grade j.1) (k m : ℕ) (g : ℕ → T.A) : Prop :=
  (∀ i : ℕ, g i ∈ T.grade k) ∧
  (∀ i : ℕ, T.chosenDifferential b hb (g i) = 0) ∧
  (k = 0 → ∀ i : ℕ, ∃ p : MvPolynomial σ R, φ p = 0 ∧ g i = T.coefficient p) ∧
  (k = 0 → ∀ p : MvPolynomial σ R, φ p = 0 → ∃ c : ℕ → MvPolynomial σ R,
    T.coefficient p = ∑ i : Fin m, T.coefficient (c i.1) * g i.1) ∧
  (0 < k → ∀ y : T.A, y ∈ T.grade k → T.chosenDifferential b hb y = 0 →
    ∃ c : ℕ → MvPolynomial σ R, y = ∑ i : Fin m, T.coefficient (c i.1) * g i.1)

/-- The rule's choice: a number of variables and their boundaries, meeting `GoodData` whenever
anything does, and adjoining nothing when nothing does. -/
public noncomputable def chosenData
    (T : IndexedPresentation.{u, max u v, v} R (MvPolynomial σ R) f)
    (b : (Σ n : ℕ, f n) → T.A) (hb : ∀ j, b j ∈ T.grade j.1) (k : ℕ) : ℕ × (ℕ → T.A) :=
  letI := Classical.dec (∃ z : ℕ × (ℕ → T.A), GoodData φ T b hb k z.1 z.2)
  if h : ∃ z : ℕ × (ℕ → T.A), GoodData φ T b hb k z.1 z.2 then h.choose else (0, fun _ => 0)

private theorem goodData_chosenData
    (T : IndexedPresentation.{u, max u v, v} R (MvPolynomial σ R) f)
    (b : (Σ n : ℕ, f n) → T.A) (hb : ∀ j, b j ∈ T.grade j.1) (k : ℕ)
    (h : ∃ z : ℕ × (ℕ → T.A), GoodData φ T b hb k z.1 z.2) :
    GoodData φ T b hb k (chosenData φ T b hb k).1 (chosenData φ T b hb k).2 := by
  rw [chosenData, dite_eq_left h]
  exact h.choose_spec

private theorem chosenData_of_not
    (T : IndexedPresentation.{u, max u v, v} R (MvPolynomial σ R) f)
    (b : (Σ n : ℕ, f n) → T.A) (hb : ∀ j, b j ∈ T.grade j.1) (k : ℕ)
    (h : ¬ ∃ z : ℕ × (ℕ → T.A), GoodData φ T b hb k z.1 z.2) :
    chosenData φ T b hb k = (0, fun _ => 0) := by
  rw [chosenData, dite_eq_right h]

public theorem chosenData_mem
    (T : IndexedPresentation.{u, max u v, v} R (MvPolynomial σ R) f)
    (b : (Σ n : ℕ, f n) → T.A) (hb : ∀ j, b j ∈ T.grade j.1) (k i : ℕ) :
    (chosenData φ T b hb k).2 i ∈ T.grade k := by
  by_cases h : ∃ z : ℕ × (ℕ → T.A), GoodData φ T b hb k z.1 z.2
  · exact (goodData_chosenData φ T b hb k h).1 i
  · rw [chosenData_of_not φ T b hb k h]
    exact Submodule.zero_mem _

private theorem chosenData_cycle
    (T : IndexedPresentation.{u, max u v, v} R (MvPolynomial σ R) f)
    (b : (Σ n : ℕ, f n) → T.A) (hb : ∀ j, b j ∈ T.grade j.1) (k i : ℕ) :
    T.chosenDifferential b hb ((chosenData φ T b hb k).2 i) = 0 := by
  by_cases h : ∃ z : ℕ × (ℕ → T.A), GoodData φ T b hb k z.1 z.2
  · exact (goodData_chosenData φ T b hb k h).2.1 i
  · rw [chosenData_of_not φ T b hb k h]
    exact map_zero _

private theorem chosenData_kernel
    (T : IndexedPresentation.{u, max u v, v} R (MvPolynomial σ R) f)
    (b : (Σ n : ℕ, f n) → T.A) (hb : ∀ j, b j ∈ T.grade j.1) (i : ℕ) :
    ∃ p : MvPolynomial σ R, φ p = 0 ∧ (chosenData φ T b hb 0).2 i = T.coefficient p := by
  by_cases h : ∃ z : ℕ × (ℕ → T.A), GoodData φ T b hb 0 z.1 z.2
  · exact (goodData_chosenData φ T b hb 0 h).2.2.1 rfl i
  · refine ⟨0, map_zero _, ?_⟩
    rw [chosenData_of_not φ T b hb 0 h, map_zero]

/-- **The rule of the Tate construction.** In degree one the variables kill a finite generating
family of the kernel of `φ`; in degree `k + 1` they kill a finite generating family of the
cycles of degree `k` over the coefficients. -/
public noncomputable def tateRule : BoundaryRule.{u, max u v, v} R (MvPolynomial σ R) where
  size _f b hb k := (chosenData φ _ b hb k).1
  bdry _f b hb k i := (chosenData φ _ b hb k).2 i
  bdry_mem _f b hb k i := chosenData_mem φ _ b hb k i

/-- **The rule's data exists** whenever the family has finitely many variables in each degree:
in degree zero because the kernel of `φ` is a finitely generated ideal of the Noetherian ring
`MvPolynomial σ R`, and in positive degree because the cycles of that degree are a finitely
generated module over it. -/
private theorem exists_goodData [IsNoetherianRing R] [Finite σ] (hfin : ∀ n : ℕ, Finite (f n))
    (T : IndexedPresentation.{u, max u v, v} R (MvPolynomial σ R) f)
    (b : (Σ n : ℕ, f n) → T.A) (hb : ∀ j, b j ∈ T.grade j.1) (k : ℕ) :
    ∃ z : ℕ × (ℕ → T.A), GoodData φ T b hb k z.1 z.2 := by
  let _alg : Algebra (MvPolynomial σ R) T.A :=
    coefficientAlgebra T.grade T.coefficient T.coefficient_mem_grade_zero
  have hPA : ∀ p : MvPolynomial σ R, algebraMap (MvPolynomial σ R) T.A p = T.coefficient p :=
    fun _ => rfl
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain ⟨m, q, hq1, hq2⟩ := exists_fin_family_of_fg
      (RingHom.ker (φ : MvPolynomial σ R →+* S)) (IsNoetherian.noetherian _)
    refine ⟨⟨m, fun i => T.coefficient (q i)⟩, fun i => T.coefficient_mem_grade_zero (q i),
      fun i => T.chosenDifferential_coefficient b hb (q i), fun _ i => ⟨q i, hq1 i, rfl⟩,
      fun _ p hp => ?_, fun hk => absurd hk (lt_irrefl 0)⟩
    obtain ⟨c, hc⟩ := hq2 p hp
    refine ⟨c, ?_⟩
    rw [hc, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, map_mul]
  · obtain ⟨m, g, hg1, hg2⟩ := exists_fin_family_of_fg
      (IndexedPresentation.cycleModule T b hb hPA k)
      (IndexedPresentation.fg_cycleModule T b hb hPA hfin k)
    refine ⟨⟨m, g⟩, fun i => (hg1 i).1, fun i => (hg1 i).2, fun h => absurd h (by omega),
      fun h => absurd h (by omega), fun _ y hy hdy => ?_⟩
    obtain ⟨c, hc⟩ := hg2 y ⟨hy, hdy⟩
    exact ⟨c, hc.trans <| Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, hPA]⟩

/-- **The rule of the Tate construction is resolving.** -/
public theorem isResolvingRule_tateRule [IsNoetherianRing R] [Finite σ] :
    IsResolvingRule (tateRule φ) φ where
  cycle _ b hb k i := chosenData_cycle φ _ b hb k i
  kernel _ b hb i := chosenData_kernel φ _ b hb i
  span_zero _ b hb hfin p hp :=
    (goodData_chosenData φ _ b hb 0 (exists_goodData φ hfin _ b hb 0)).2.2.2.1 rfl p hp
  span_pos _ b hb hfin k hk y hy hdy :=
    (goodData_chosenData φ _ b hb k (exists_goodData φ hfin _ b hb k)).2.2.2.2 hk y hy hdy

end Rule

section Finite

/-- **A finite-type algebra over a Noetherian ring has a Tate resolution with finitely many new
variables in every degree, including degree zero.**

This is the finite assertion of [Stacks, Tag 09PN]. The polynomial presentation of the
degree-zero part and the assembly of the resolution are
`exists_finite_tateResolution_of_isResolvingBoundary`; what is supplied here is the resolving
boundary, as the limiting boundary of the tower of `tateRule`. -/
public theorem exists_finite_tateResolution_of_tateRule {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R] [Algebra.FiniteType R S] :
    ∃ (σ : Type (max u v)) (φ : MvPolynomial σ R →ₐ[R] S) (_hφ : Function.Surjective φ)
      (T : Resolution R S σ φ),
      letI : Ring T.A := T.ring
      letI : Algebra R T.A := T.algebra
      letI : GradedAlgebra T.grade := T.graded
      letI : IsStrictlyGradedComm T.grade := T.strict
      Finite σ ∧ (∀ n : ℕ, Finite (T.polynomial.indices n)) :=
  exists_finite_tateResolution_of_isResolvingBoundary fun _ _ φ _ =>
    ⟨_, _, _, _, finite_ruleLimit (tateRule φ),
      isResolvingBoundary_limitBoundary (tateRule φ) φ (isResolvingRule_tateRule φ)⟩

end Finite

end DividedPowers.TateResolution

end
