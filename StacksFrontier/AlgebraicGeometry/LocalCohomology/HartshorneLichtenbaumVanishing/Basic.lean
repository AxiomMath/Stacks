module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.HartshorneLichtenbaumVanishing.SymbolicDefect
public import StacksCore.Tactic.StacksAttribute

/-!
# Symbolic powers in a complete local domain

In a complete Noetherian local domain, the symbolic-power filtration of a one-dimensional prime
ideal is cofinal with its ordinary-power filtration. This is the commutative-algebra input to
Hartshorne–Lichtenbaum vanishing.

## Main results

* `Ideal.exists_symbolicPower_le_pow`: every positive ordinary power of the prime ideal contains
  a sufficiently high symbolic power.

## Implementation notes

The dimension of a prime ideal `p` is expressed as the Krull dimension of `A ⧸ p`. Completeness
of the local ring is expressed by `IsAdicComplete (IsLocalRing.maximalIdeal A) A`. The argument
runs through the symbolic defects `Ideal.symbolicDefect`: their tail ranges stabilise because
each defect is Artinian, and completeness forces the stable range to vanish, which is exactly
the containment sought.

## References

* [Stacks Project, Tag 0EB5](https://stacks.math.columbia.edu/tag/0EB5)
-/

@[expose] public section

namespace Ideal

variable {A : Type*} [CommRing A]

/-- A prime ideal of a complete Noetherian local ring is itself an ideal of definition for a
complete adic topology. -/
private theorem symbolicIdeal_isAdicComplete [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (p : Ideal A) [p.IsPrime] : IsAdicComplete p A :=
  isAdicComplete_of_le_of_fg_of_isAdicComplete
    (IsLocalRing.le_maximalIdeal_of_isPrime p) inferInstance
    (IsNoetherian.noetherian p)

/-- In a Noetherian domain the symbolic powers of a prime ideal intersect in zero. -/
private theorem symbolicPower_iInf_eq_bot [IsNoetherianRing A] [IsDomain A]
    (p : Ideal A) [p.IsPrime] : (⨅ n : ℕ, Ideal.symbolicPower p n) = ⊥ := by
  unfold Ideal.symbolicPower
  simp_rw [Ideal.under_def, Ideal.map_pow]
  rw [← Ideal.comap_iInf]
  have hmap : p.map (algebraMap A (Localization.AtPrime p)) ≠ ⊤ := by
    rw [Localization.AtPrime.map_eq_maximalIdeal]
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  rw [Ideal.iInf_pow_eq_bot_of_isDomain _ hmap]
  exact Ideal.comap_bot_of_injective _
    ((faithfulSMul_iff_algebraMap_injective A _).mp inferInstance)

/-- In a Noetherian domain an element lying in every positive symbolic power of a prime ideal
is zero. -/
private theorem eq_zero_of_forall_mem_symbolicPower [IsNoetherianRing A] [IsDomain A]
    (p : Ideal A) [p.IsPrime] {a : A} (h : ∀ r, a ∈ Ideal.symbolicPower p (r + 1)) : a = 0 := by
  refine Ideal.mem_bot.mp ?_
  rw [← symbolicPower_iInf_eq_bot p]
  refine Ideal.mem_iInf.mpr fun n ↦ ?_
  cases n with
  | zero =>
      rw [Ideal.symbolicPower_eq_symbolicPower', symbolicPower_zero]
      trivial
  | succ r => exact h r

/-- A sequence of elements of successively higher symbolic powers which is Cauchy for the
`p`-adic topology has its first term in `pᴺ`. -/
private theorem symbolicTailSequence_limit [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (p : Ideal A) [p.IsPrime] (N : ℕ) (f : ℕ → A)
    (hf : ∀ k, f k ∈ Ideal.symbolicPower p (N + k))
    (hc : ∀ {k l}, k ≤ l → f k - f l ∈ p ^ (N + k)) :
    f 0 ∈ p ^ N := by
  classical
  have : IsAdicComplete p A := symbolicIdeal_isAdicComplete p
  let g : ℕ → A := fun j ↦ if j < N then f 0 else f (j - N)
  have hg : ∀ {i j}, i ≤ j → g i - g j ∈ p ^ i := by
    intro i j hij
    by_cases hi : i < N
    · by_cases hj : j < N
      · simp [g, hi, hj]
      · have h : f 0 - f (j - N) ∈ p ^ N := by
          simpa using hc (k := 0) (l := j - N) (Nat.zero_le _)
        simpa [g, hi, hj] using Ideal.pow_le_pow_right (show i ≤ N by omega) h
    · have hj : ¬ j < N := by omega
      have h := hc (k := i - N) (l := j - N) (by omega)
      simpa [g, hi, hj, Nat.add_sub_of_le (show N ≤ i by omega)] using h
  have hg' : ∀ {i j}, i ≤ j → g i ≡ g j [SMOD (p ^ i • ⊤ : Submodule A A)] := by
    intro i j hij
    rw [SModEq.sub_mem]
    simpa [smul_eq_mul, Ideal.mul_top] using hg hij
  obtain ⟨a, ha⟩ := IsPrecomplete.prec (I := p) (M := A) inferInstance hg'
  have ha' : ∀ n, g n - a ∈ p ^ n := fun n ↦ by
    simpa [smul_eq_mul, Ideal.mul_top] using SModEq.sub_mem.mp (ha n)
  have hmem : ∀ r, a ∈ Ideal.symbolicPower p (r + 1) := by
    intro r
    have hfsymb : f (r + 1) ∈ Ideal.symbolicPower p (r + 1) :=
      (Ideal.symbolicPower_antitone (p := p) (by omega)) (hf (r + 1))
    have hpow : p ^ (N + (r + 1)) ≤ Ideal.symbolicPower p (r + 1) := by
      rw [Ideal.symbolicPower_eq_symbolicPower']
      exact (Ideal.pow_le_pow_right (by omega)).trans (pow_le_symbolicPower p (r + 1))
    have hdiff : g (N + (r + 1)) - a ∈ Ideal.symbolicPower p (r + 1) := hpow (ha' _)
    have hjN : ¬ N + (r + 1) < N := by omega
    have hgj : g (N + (r + 1)) = f (r + 1) := by simp [g, hjN]
    rw [hgj] at hdiff
    simpa [sub_sub_cancel] using (Ideal.symbolicPower p (r + 1)).sub_mem hfsymb hdiff
  simpa [g, eq_zero_of_forall_mem_symbolicPower p hmem] using ha' N

/-- A family of elements of the symbolic defects which is compatible under the one-step
transition maps is compatible under all transition maps. -/
private theorem symbolicDefectTransition_of_step (p : Ideal A) [p.IsPrime] (n : ℕ)
    (x : ∀ k, Ideal.symbolicDefect p (n + k))
    (hstep : ∀ k, Ideal.symbolicDefectTransition p (show n + k ≤ n + (k + 1) by omega)
      (x (k + 1)) = x k)
    {k l : ℕ} (hkl : k ≤ l) :
    Ideal.symbolicDefectTransition p (Nat.add_le_add_left hkl n) (x l) = x k := by
  induction l, hkl using Nat.le_induction with
  | base =>
      change Ideal.symbolicDefectTransition p (Nat.le_refl (n + k)) (x k) = x k
      simp [Ideal.symbolicDefectTransition]
  | succ l hkl ih =>
      calc
        Ideal.symbolicDefectTransition p (Nat.add_le_add_left (hkl.trans (Nat.le_succ l)) n)
            (x (l + 1)) =
            (Ideal.symbolicDefectTransition p (show n + k ≤ n + l by omega) ∘ₗ
              Ideal.symbolicDefectTransition p (Nat.le_succ (n + l))) (x (l + 1)) :=
                (congrArg (fun f ↦ f (x (l + 1))) (Ideal.symbolicDefectTransition_comp p
                  (show n + k ≤ n + l by omega) (Nat.le_succ (n + l)))).symm
        _ = Ideal.symbolicDefectTransition p (show n + k ≤ n + l by omega) (x l) := by
              rw [LinearMap.comp_apply, hstep l]
        _ = x k := ih

/-- For a one-dimensional prime over a complete Noetherian local domain the stable tail range of
the symbolic defects vanishes. -/
private theorem symbolicDefectTailRange_eq_bot [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (p : Ideal A) [p.IsPrime] (n : ℕ) (hn : 0 < n)
    (hp : ringKrullDim (A ⧸ p) = 1) :
    Ideal.symbolicDefectTailRange p n (Ideal.symbolicDefectCutoff p n hn hp) = ⊥ := by
  classical
  let C := fun k ↦
    { x : Ideal.symbolicDefect p (n + k) //
      x ∈ Ideal.symbolicDefectTailRange p (n + k)
        (Ideal.symbolicDefectCutoff p (n + k) (by omega) hp) }
  let cutoff : ℕ → ℕ := fun k ↦ Ideal.symbolicDefectCutoff p (n + k) (by omega) hp
  let nextSpec (k : ℕ) (x : C k) : ∃ y : C (k + 1),
      Ideal.symbolicDefectTransition p (show n + k ≤ n + (k + 1) by omega) y.1 = x.1 := by
    obtain ⟨y, hy, heq⟩ := Ideal.symbolicDefectStableRange_step_surjective p (n + k)
      (cutoff k) (cutoff (k + 1))
      (fun l hl ↦ Ideal.symbolicDefectCutoff_spec p (n + k) (by omega) hp l hl) x.1 x.2
    exact ⟨⟨y, hy⟩, heq⟩
  let next (k : ℕ) (x : C k) : C (k + 1) := Classical.choose (nextSpec k x)
  have next_eq (k : ℕ) (x : C k) :
      Ideal.symbolicDefectTransition p (show n + k ≤ n + (k + 1) by omega) (next k x).1 = x.1 :=
    Classical.choose_spec (nextSpec k x)
  by_contra hne
  obtain ⟨x₀, hx₀, hx₀ne⟩ := (Submodule.ne_bot_iff _).mp hne
  let X : (k : ℕ) → C k := Nat.rec ⟨x₀, hx₀⟩ (fun k x ↦ next k x)
  have hstep (k : ℕ) :
      Ideal.symbolicDefectTransition p (show n + k ≤ n + (k + 1) by omega) (X (k + 1)).1 =
        (X k).1 :=
    next_eq k (X k)
  let x := fun k ↦ (X k).1
  have hrepr : ∀ k, ∃ y : A, y ∈ Ideal.symbolicPower p (n + k) ∧
      Ideal.Quotient.mk (p ^ (n + k)) y = (x k).val := fun k ↦
    (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (p ^ (n + k)))
      Ideal.Quotient.mk_surjective).mp (X k).1.2
  choose y hy using hrepr
  have hcompat : ∀ {k l}, k ≤ l → y k - y l ∈ p ^ (n + k) := by
    intro k l hkl
    refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp ?_
    calc
      Ideal.Quotient.mk (p ^ (n + k)) (y k) = (x k).val := (hy k).2
      _ = Ideal.symbolicDefectTransition p (show n + k ≤ n + l by omega) (x l) :=
        congrArg Subtype.val (symbolicDefectTransition_of_step p n x hstep hkl).symm
      _ = Ideal.Quotient.mk (p ^ (n + k)) (y l) := by
        change Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (show n + k ≤ n + l by omega)) ((x l).val) = _
        rw [← (hy l).2]
        simp
  have hbase := symbolicTailSequence_limit p n y (fun k ↦ (hy k).1) hcompat
  have hxzero : (x 0).val = 0 := by
    rw [← (hy 0).2]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hbase
  exact hx₀ne (Subtype.ext (by simpa [x, X] using hxzero))

/-- **Stacks Project, Tag 0EB5.** Let `p` be a one-dimensional prime ideal in a complete
Noetherian local domain. For every `n ≥ 1`, some symbolic power `p⁽ᵐ⁾`, with `m ≥ n`, is
contained in the ordinary power `pⁿ`. -/
@[stacks 0EB5]
theorem exists_symbolicPower_le_pow [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (p : Ideal A) [p.IsPrime] (hp : ringKrullDim (A ⧸ p) = 1)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ m : ℕ, n ≤ m ∧ Ideal.symbolicPower p m ≤ p ^ n := by
  have hn0 : 0 < n := by omega
  let k := Ideal.symbolicDefectCutoff p n hn0 hp
  have hstable : Ideal.symbolicDefectTailRange p n k = ⊥ :=
    symbolicDefectTailRange_eq_bot p n hn0 hp
  have hmapzero (z : Ideal.symbolicDefect p (n + k)) :
      Ideal.symbolicDefectTransition p (Nat.le_add_right n k) z = 0 := by
    have hz : Ideal.symbolicDefectTransition p (Nat.le_add_right n k) z ∈
        Ideal.symbolicDefectTailRange p n k := LinearMap.mem_range.mpr ⟨z, rfl⟩
    rwa [hstable, Submodule.mem_bot] at hz
  refine ⟨n + k, Nat.le_add_right n k, fun x hx ↦ ?_⟩
  have hxdef : Ideal.Quotient.mk (p ^ (n + k)) x ∈ Ideal.symbolicDefect p (n + k) :=
    Ideal.mem_map_of_mem (Ideal.Quotient.mk (p ^ (n + k))) hx
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  simpa [Ideal.symbolicDefectTransition] using congrArg Subtype.val (hmapzero ⟨_, hxdef⟩)

end Ideal
