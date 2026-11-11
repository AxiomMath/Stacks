module

public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing.CompleteNoetherian
public import StacksFrontier.RingTheory.CompleteLocalRing.Noetherian.FiniteProduct

/-!
# Complete filtrations whose graded ring is generated in bounded degree

Let `A` be a commutative ring with a decreasing multiplicative filtration
`A = F₀ ⊇ F₁ ⊇ F₂ ⊇ ⋯` that is separated (`⋂ Fₙ = 0`) and complete (a series whose `n`-th term
lies in `Fₙ` converges). This is the structure that the ring of compatible functions on the
infinitesimal thickenings of a divisor carries
(`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodFiltration`), with no hypothesis on
the divisor.

Suppose that the associated graded ring is generated in degrees `≤ c`, in the following form:
there is a finitely generated ideal `J ⊆ F₁` with

`Fₙ ⊆ J · F_{n - c} + Fₙ₊₁`  for every `n ≥ 1`.

For the formal neighbourhood of a curve this is what generation of the section ring
`⨁ₙ H⁰(C, Lⁿ)` in degrees `≤ c` gives: every section of `Lⁿ` is a sum of products of a section of
some `Lⁱ`, `1 ≤ i ≤ c`, with a section of `L^{n-i}`.

Then the step `Fₙ ⊆ J · F_{n-c}` holds on the nose, by summing the convergent series of
corrections; hence `F₁ = J`, `F_{c n} ⊆ Jⁿ ⊆ Fₙ`, so the `J`-adic topology is the topology of the
filtration and `A` is `J`-adically complete. If moreover `A / F₁` is a field, `A` is a complete
Noetherian local ring with maximal ideal `F₁` (Stacks 05GH,
`noetherian_of_isAdicComplete_fg`).

## Main definitions

* `Stacks.IsCompleteFiltration`: a decreasing, multiplicative, separated and complete filtration
  by ideals starting at the whole ring.

## Main results

* `Stacks.IsCompleteFiltration.le_mul_of_le_mul_sup`: `Fₙ ⊆ J · F_{n-c} + Fₙ₊₁` for all `n ≥ 1`
  implies `Fₙ ⊆ J · F_{n-c}` for all `n ≥ 1`.
* `Stacks.IsCompleteFiltration.eq_one_of_le_mul_sup`: `F₁ = J`.
* `Stacks.IsCompleteFiltration.le_pow_of_le_mul_sup`: `F_{c n} ⊆ Jⁿ`.
* `Stacks.IsCompleteFiltration.isAdicComplete_of_le_mul_sup`: `A` is `J`-adically complete.
* `Stacks.IsCompleteFiltration.isNoetherianCompleteLocalRing_of_le_mul_sup`: `A` is a complete
  Noetherian local ring, with maximal ideal `F₁`
  (`Stacks.IsCompleteFiltration.maximalIdeal_eq_of_le_mul_sup`).
-/

@[expose] public noncomputable section

universe u

namespace Stacks

variable {A : Type u} [CommRing A]

/-- A *complete filtration* on a commutative ring: a decreasing chain of ideals
`A = F₀ ⊇ F₁ ⊇ ⋯` that is multiplicative (`Fₘ Fₙ ⊆ Fₘ₊ₙ`), separated (`⋂ Fₙ = 0`) and complete (a
series whose `n`-th term lies in `Fₙ` converges, with partial sums converging in the filtration
topology). -/
public structure IsCompleteFiltration (F : ℕ → Ideal A) : Prop where
  /-- The filtration starts at the whole ring. -/
  zero : F 0 = ⊤
  /-- The filtration decreases. -/
  succ_le : ∀ n, F (n + 1) ≤ F n
  /-- The filtration is multiplicative. -/
  mul_le : ∀ m n, F m * F n ≤ F (m + n)
  /-- The filtration is separated. -/
  iInf_eq_bot : ⨅ n, F n = ⊥
  /-- The filtration is complete: a series whose `n`-th term lies in `Fₙ` converges. -/
  exists_sum : ∀ c : ℕ → A, (∀ n, c n ∈ F n) →
    ∃ s, ∀ n, s - ∑ e ∈ Finset.range n, c e ∈ F n

namespace IsCompleteFiltration

variable {F : ℕ → Ideal A} (hF : IsCompleteFiltration F)
include hF

/-- A complete filtration is antitone. -/
public theorem antitone {m n : ℕ} (h : m ≤ n) : F n ≤ F m := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact (hF.succ_le k).trans ih

/-- An element of every step of a complete filtration is zero. -/
public theorem eq_zero_of_forall_mem {x : A} (hx : ∀ n, x ∈ F n) : x = 0 := by
  have h : x ∈ ⨅ n, F n := Ideal.mem_iInf.2 hx
  rw [hF.iInf_eq_bot] at h
  simpa using h

/-- **Series whose terms are eventually deep converge.** If the `e`-th term of a series lies in
`F_{e - c}`, there is a sum `s` with `s - ∑_{e < N} bₑ ∈ F_{N - c}` for every `N`. -/
public theorem exists_sum_sub (c : ℕ) (b : ℕ → A) (hb : ∀ e, b e ∈ F (e - c)) :
    ∃ s, ∀ N, s - ∑ e ∈ Finset.range N, b e ∈ F (N - c) := by
  obtain ⟨s', hs'⟩ := hF.exists_sum (fun e => b (c + e)) (fun e => by
    simpa using hb (c + e))
  refine ⟨(∑ e ∈ Finset.range c, b e) + s', fun N => ?_⟩
  rcases le_or_gt N c with hN | hN
  · rw [Nat.sub_eq_zero_of_le hN, hF.zero]
    exact Submodule.mem_top
  · obtain ⟨M, rfl⟩ : ∃ M, N = c + M := ⟨N - c, by omega⟩
    rw [Finset.sum_range_add, Nat.add_sub_cancel_left]
    convert hs' M using 1
    ring

omit hF in
/-- An element of `span (range g) * I` is a combination `∑ᵢ gᵢ aᵢ` with coefficients in `I`. -/
public theorem exists_eq_sum_of_mem_span_mul {ι : Type*} [Fintype ι] (g : ι → A) (I : Ideal A)
    {x : A} (hx : x ∈ Ideal.span (Set.range g) * I) :
    ∃ a : ι → A, (∀ i, a i ∈ I) ∧ x = ∑ i, g i * a i := by
  refine Submodule.mul_induction_on hx (fun y hy z hz => ?_) (fun y z => ?_)
  · obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hy
    refine ⟨fun i => c i * z, fun i => Ideal.mul_mem_left _ _ hz, ?_⟩
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by simp only [smul_eq_mul]; ring
  · rintro ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, fun i => add_mem (ha i) (hb i), by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring⟩

omit hF in
/-- A combination `∑ᵢ gᵢ aᵢ` with coefficients in `I` lies in `span (range g) * I`. -/
public theorem sum_mem_span_mul {ι : Type*} [Fintype ι] (g : ι → A) (I : Ideal A)
    (a : ι → A) (ha : ∀ i, a i ∈ I) : ∑ i, g i * a i ∈ Ideal.span (Set.range g) * I :=
  Submodule.sum_mem _ fun i _ =>
    Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (ha i)

variable {ι : Type*} [Finite ι] (g : ι → A) (c : ℕ)

/-- **Bounded-degree generation of the graded ring holds on the nose.** If
`Fₙ ⊆ (g) · F_{n-c} + Fₙ₊₁` for every `n ≥ 1`, then `Fₙ ⊆ (g) · F_{n-c}` for every `n ≥ 1`: an
element of `Fₙ` is peeled step by step, and the coefficient series converge because the `e`-th
correction lies in `F_{n+e-c}`. -/
public theorem le_mul_of_le_mul_sup
    (hstep : ∀ n, 1 ≤ n → F n ≤ Ideal.span (Set.range g) * F (n - c) ⊔ F (n + 1))
    {n : ℕ} (hn : 1 ≤ n) : F n ≤ Ideal.span (Set.range g) * F (n - c) := by
  have := Fintype.ofFinite ι
  intro z hz
  have step : ∀ (e : ℕ) (w : A), ∃ p : (ι → A) × A, w ∈ F (n + e) →
      (∀ i, p.1 i ∈ F (n + e - c)) ∧ p.2 ∈ F (n + e + 1) ∧ w = ∑ i, g i * p.1 i + p.2 := by
    intro e w
    by_cases hw : w ∈ F (n + e)
    · obtain ⟨u, hu, r, hr, rfl⟩ := Submodule.mem_sup.1 (hstep (n + e) (by omega) hw)
      obtain ⟨a, ha, rfl⟩ := exists_eq_sum_of_mem_span_mul g _ hu
      exact ⟨(a, r), fun _ => ⟨ha, hr, rfl⟩⟩
    · exact ⟨(0, 0), fun h => absurd h hw⟩
  choose P hP using step
  obtain ⟨r, hr0, hrs⟩ : ∃ r : ℕ → A, r 0 = z ∧ ∀ e, r (e + 1) = (P e (r e)).2 :=
    ⟨fun e => Nat.rec (motive := fun _ => A) z (fun e w => (P e w).2) e, rfl, fun _ => rfl⟩
  have hr : ∀ e, r e ∈ F (n + e) := by
    intro e
    induction e with
    | zero => simpa [hr0] using hz
    | succ e ih => rw [hrs]; exact (hP e (r e) ih).2.1
  obtain ⟨a, ha_def⟩ : ∃ a : ι → ℕ → A, ∀ i e, a i e = (P e (r e)).1 i :=
    ⟨fun i e => (P e (r e)).1 i, fun _ _ => rfl⟩
  have ha : ∀ i e, a i e ∈ F (n + e - c) := fun i e => by
    rw [ha_def]; exact (hP e (r e) (hr e)).1 i
  have hstepr : ∀ e, r e = ∑ i, g i * a i e + r (e + 1) := by
    intro e
    have h := (hP e (r e) (hr e)).2.2
    rw [← hrs e] at h
    simp only [ha_def]
    exact h
  have hsum : ∀ N, z = ∑ e ∈ Finset.range N, ∑ i, g i * a i e + r N := by
    intro N
    induction N with
    | zero => simp [hr0]
    | succ N ih =>
      rw [Finset.sum_range_succ, add_assoc, ← hstepr N]
      exact ih
  have hser : ∀ i, ∃ s, ∀ N, s - ∑ e ∈ Finset.range N, a i e ∈ F (N - c) := fun i =>
    hF.exists_sum_sub c (a i) fun e => hF.antitone (by omega) (ha i e)
  choose s hs using hser
  have hsmem : ∀ i, s i ∈ F (n - c) := by
    intro i
    have h1 := hs i n
    have h2 : ∑ e ∈ Finset.range n, a i e ∈ F (n - c) :=
      Submodule.sum_mem _ fun e _ => hF.antitone (by omega) (ha i e)
    simpa using add_mem h1 h2
  have heq : z = ∑ i, g i * s i := by
    rw [← sub_eq_zero]
    refine hF.eq_zero_of_forall_mem fun M => ?_
    have hdec : z - ∑ i, g i * s i =
        r (M + c) - ∑ i, g i * (s i - ∑ e ∈ Finset.range (M + c), a i e) := by
      conv_lhs => rw [hsum (M + c)]
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      rw [Finset.sum_comm]
      ring
    rw [hdec]
    refine sub_mem (hF.antitone (by omega) (hr (M + c))) (Submodule.sum_mem _ fun i _ => ?_)
    have := hs i (M + c)
    rw [Nat.add_sub_cancel] at this
    exact Ideal.mul_mem_left _ _ this
  rw [heq]
  exact sum_mem_span_mul g _ s hsmem

/-- Under bounded-degree generation, the first step of the filtration is the ideal generated by
the chosen elements. -/
public theorem eq_one_of_le_mul_sup (hg : ∀ i, g i ∈ F 1)
    (hstep : ∀ n, 1 ≤ n → F n ≤ Ideal.span (Set.range g) * F (n - c) ⊔ F (n + 1)) :
    F 1 = Ideal.span (Set.range g) :=
  le_antisymm ((hF.le_mul_of_le_mul_sup g c hstep le_rfl).trans Ideal.mul_le_left)
    (Ideal.span_le.2 (Set.range_subset_iff.2 hg))

/-- The powers of an ideal inside `F₁` lie in the corresponding steps of the filtration. -/
public theorem pow_le (J : Ideal A) (hJ : J ≤ F 1) (n : ℕ) : J ^ n ≤ F n := by
  induction n with
  | zero => simp [hF.zero]
  | succ n ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono ih hJ).trans (hF.mul_le n 1)

/-- **The filtration is cofinal with the adic one.** Under bounded-degree generation in degrees
`≤ c`, with `1 ≤ c`, the step `F_{c n}` lies in the `n`-th power of `(g)`. -/
public theorem le_pow_of_le_mul_sup (hc : 1 ≤ c)
    (hstep : ∀ n, 1 ≤ n → F n ≤ Ideal.span (Set.range g) * F (n - c) ⊔ F (n + 1)) (n : ℕ) :
    F (c * n) ≤ Ideal.span (Set.range g) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := hF.le_mul_of_le_mul_sup g c hstep (n := c * (n + 1)) (by nlinarith)
    rw [show c * (n + 1) - c = c * n by rw [Nat.mul_succ, Nat.add_sub_cancel]] at h
    rw [pow_succ, mul_comm (Ideal.span (Set.range g) ^ n)]
    exact h.trans (Ideal.mul_mono_right ih)

/-- **Completeness for the adic topology.** Under bounded-degree generation in degrees `≤ c`,
with `1 ≤ c`, the ring is complete and separated for the `(g)`-adic topology. -/
public theorem isAdicComplete_of_le_mul_sup (hc : 1 ≤ c) (hg : ∀ i, g i ∈ F 1)
    (hstep : ∀ n, 1 ≤ n → F n ≤ Ideal.span (Set.range g) * F (n - c) ⊔ F (n + 1)) :
    IsAdicComplete (Ideal.span (Set.range g)) A := by
  set J := Ideal.span (Set.range g)
  have hJ : J ≤ F 1 := Ideal.span_le.2 (Set.range_subset_iff.2 hg)
  have hsmul : ∀ n, (J ^ n • ⊤ : Ideal A) = J ^ n := fun n => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have hH : IsHausdorff J A := ⟨fun x hx => hF.eq_zero_of_forall_mem fun n => by
    have := hx n
    rw [SModEq.sub_mem, hsmul, sub_zero] at this
    exact hF.pow_le J hJ n this⟩
  refine @IsAdicComplete.mk _ _ _ _ _ _ hH ⟨fun f hf => ?_⟩
  · have hb : ∀ e, f (e + 1) - f e ∈ F e := fun e => by
      have := (hf (Nat.le_succ e)).symm
      rw [SModEq.sub_mem, hsmul] at this
      exact hF.pow_le J hJ e this
    obtain ⟨s, hs⟩ := hF.exists_sum _ hb
    refine ⟨f 0 + s, fun n => ?_⟩
    rw [SModEq.sub_mem, hsmul]
    have h1 : f n - f (c * n) ∈ J ^ n := by
      have := hf (show n ≤ c * n by nlinarith)
      rwa [SModEq.sub_mem, hsmul] at this
    have h2 : f (c * n) - (f 0 + s) ∈ J ^ n := by
      refine hF.le_pow_of_le_mul_sup g c hc hstep n ?_
      convert neg_mem (hs (c * n)) using 1
      simp only [Finset.sum_range_sub]
      ring
    convert add_mem h1 h2 using 1
    ring

/-- **Noetherianity.** Under bounded-degree generation in degrees `≤ c`, with `1 ≤ c`, a ring
with a complete filtration whose residue ring `A / F₁` is a field is Noetherian: it is complete
for the finitely generated ideal `F₁ = (g)`, with Noetherian quotient (Stacks 05GH). -/
public theorem isNoetherianRing_of_le_mul_sup (hc : 1 ≤ c) (hg : ∀ i, g i ∈ F 1)
    (hstep : ∀ n, 1 ≤ n → F n ≤ Ideal.span (Set.range g) * F (n - c) ⊔ F (n + 1))
    (hfield : IsField (A ⧸ F 1)) : IsNoetherianRing A := by
  have hcomp := hF.isAdicComplete_of_le_mul_sup g c hc hg hstep
  refine noetherian_of_isAdicComplete_fg A (Ideal.span (Set.range g))
    ⟨(Set.finite_range g).toFinset, by simp⟩ hcomp ?_
  rw [← hF.eq_one_of_le_mul_sup g c hg hstep]
  let _ := hfield.toField
  infer_instance

/-- **Locality.** Under bounded-degree generation in degrees `≤ c`, with `1 ≤ c`, a ring with a
complete filtration whose residue ring `A / F₁` is a field is local, with maximal ideal `F₁`. -/
public theorem isLocalRing_of_le_mul_sup (hc : 1 ≤ c) (hg : ∀ i, g i ∈ F 1)
    (hstep : ∀ n, 1 ≤ n → F n ≤ Ideal.span (Set.range g) * F (n - c) ⊔ F (n + 1))
    (hfield : IsField (A ⧸ F 1)) : IsLocalRing A := by
  have hcomp := hF.isAdicComplete_of_le_mul_sup g c hc hg hstep
  have hmax : (F 1).IsMaximal := Ideal.Quotient.maximal_of_isField _ hfield
  have hjac := hcomp.le_jacobson_bot
  rw [← hF.eq_one_of_le_mul_sup g c hg hstep] at hjac
  refine IsLocalRing.of_unique_max_ideal ⟨F 1, hmax, fun M hM => ?_⟩
  exact (hmax.eq_of_le hM.ne_top (hjac.trans (sInf_le ⟨bot_le, hM⟩))).symm

/-- Under the hypotheses of `Stacks.IsCompleteFiltration.isLocalRing_of_le_mul_sup`, the maximal
ideal is `F₁`. -/
public theorem maximalIdeal_eq_of_le_mul_sup (hc : 1 ≤ c) (hg : ∀ i, g i ∈ F 1)
    (hstep : ∀ n, 1 ≤ n → F n ≤ Ideal.span (Set.range g) * F (n - c) ⊔ F (n + 1))
    (hfield : IsField (A ⧸ F 1)) :
    letI := hF.isLocalRing_of_le_mul_sup g c hc hg hstep hfield
    IsLocalRing.maximalIdeal A = F 1 := by
  let _ := hF.isLocalRing_of_le_mul_sup g c hc hg hstep hfield
  exact (IsLocalRing.eq_maximalIdeal (Ideal.Quotient.maximal_of_isField _ hfield)).symm

/-- **A complete filtration with field residue ring and graded ring generated in bounded degree
makes a complete Noetherian local ring.** -/
public theorem isNoetherianCompleteLocalRing_of_le_mul_sup (hc : 1 ≤ c) (hg : ∀ i, g i ∈ F 1)
    (hstep : ∀ n, 1 ≤ n → F n ≤ Ideal.span (Set.range g) * F (n - c) ⊔ F (n + 1))
    (hfield : IsField (A ⧸ F 1)) : IsNoetherianCompleteLocalRing A := by
  let _ := hF.isLocalRing_of_le_mul_sup g c hc hg hstep hfield
  refine ⟨hF.isNoetherianRing_of_le_mul_sup g c hc hg hstep hfield, inferInstance, ?_⟩
  have h := hF.maximalIdeal_eq_of_le_mul_sup g c hc hg hstep hfield
  rw [h, hF.eq_one_of_le_mul_sup g c hg hstep]
  exact hF.isAdicComplete_of_le_mul_sup g c hc hg hstep

end IsCompleteFiltration

end Stacks

end
