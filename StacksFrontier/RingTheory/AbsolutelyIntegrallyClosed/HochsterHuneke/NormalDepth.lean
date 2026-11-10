module

public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Regular.RegularSequence
public import StacksFrontier.RingTheory.Serre.Defs
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability

@[expose] public section

/-!
# Depth two for normal domains over a regular local ring

Let `T` be a Noetherian normal domain which is an integral extension of an integrally closed domain
`R`. If `u ≠ 0` and `v` are elements of `R` such that every prime of `R` containing both has
height at least two, then `v` is a nonzerodivisor on `T/uT`: the associated primes of `T/uT` have
height one (Stacks 031T), while by going down a prime of `T` lies over a prime of `R` of at most
the same height.

For a regular local ring `R` with a regular system of parameters `x, y, …`, every prime
containing `x` and `y` has height at least two, because `(x) ⊊ (x, y)` are primes. Hence the first
two members of a regular system of parameters form a regular sequence on every normal Noetherian
domain integral over `R`.

## Main results

* `mem_span_singleton_of_two_le_height`: `v` is a nonzerodivisor on `T/uT`.
* `IsRegularLocalRing.two_le_height_of_mem`: a prime containing the first two members of a
  regular system of parameters has height at least two.
* `isWeaklyRegular_take_two_of_isIntegrallyClosed`: the first two members of a regular system of
  parameters form a weakly regular sequence on a normal Noetherian domain integral over `R`.
-/

open IsLocalRing RingTheory.Sequence

open scoped Pointwise

/-- Let `R ⊆ T` be an integral extension of domains with `R` integrally closed and `T` Noetherian
and integrally closed. If `u ≠ 0` and every prime of `R` containing `u` and `v` has height at least
two, then `v` is a nonzerodivisor modulo `u` on `T`. -/
theorem mem_span_singleton_of_two_le_height {R T : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R]
    [IsIntegrallyClosed R] [CommRing T] [IsDomain T] [IsNoetherianRing T] [IsIntegrallyClosed T]
    [Algebra R T] [FaithfulSMul R T] [Algebra.IsIntegral R T] {u v : R} (hu : u ≠ 0)
    (huv : ∀ q : Ideal R, q.IsPrime → u ∈ q → v ∈ q → 2 ≤ q.height) {c : T}
    (hc : algebraMap R T v * c ∈ Ideal.span {algebraMap R T u}) :
    c ∈ Ideal.span {algebraMap R T u} := by
  set a := algebraMap R T u
  have ha : a ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R T)).mpr hu
  by_contra hcnot
  set m : T ⧸ Ideal.span {a} := Ideal.Quotient.mk _ c
  have hm : m ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing T m hm
  have hPmem : P ∈ associatedPrimes T (T ⧸ Ideal.span {a}) := hP
  have hPprime : P.IsPrime := hP.isPrime
  -- `P` has height one by Stacks 031T
  have hP1 : P.height = 1 :=
    ((associatedPrimes_minimal_and_height_eq_one_and_iInf_localization_eq_bot
      (FractionRing T)).1 a ha P hPmem).2
  -- `P` contains `a` and `algebraMap v`
  have haP : a ∈ P := by
    refine hP.annihilator_le (Submodule.mem_annihilator.mpr fun n _ => ?_)
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective n
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hvP : algebraMap R T v ∈ P := by
    refine hle ?_
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    change Ideal.Quotient.mk _ (algebraMap R T v) * Ideal.Quotient.mk _ c = 0
    rwa [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  -- by going down, the contraction of `P` has height at most one
  set p := P.under R
  have : P.LiesOver p := ⟨rfl⟩
  have hle' : p.height ≤ P.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P]
    exact le_self_add
  exact absurd ((huv p (Ideal.comap_isPrime _ _) haP hvP).trans (hle'.trans hP1.le)) (by norm_num)

/-- The first member of a regular system of parameters of a regular local ring is a nonzerodivisor,
and the remaining members form a weakly regular sequence modulo it. -/
private theorem isSMulRegular_and_isWeaklyRegular_of_ofList_eq {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {x : R} {rest : List R}
    (hxs : Ideal.ofList (x :: rest) = maximalIdeal R)
    (hlen : (x :: rest).length = (maximalIdeal R).spanFinrank) :
    IsSMulRegular R x ∧ IsWeaklyRegular (QuotSMulTop x R) rest := by
  obtain ⟨hreg, -⟩ :=
    (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay R).1
      _ hxs hlen
  exact (isWeaklyRegular_cons_iff R x rest).mp hreg.toIsWeaklyRegular

/-- A nonzerodivisor on a nontrivial ring is nonzero. -/
private theorem ne_zero_of_isSMulRegular_self {R : Type*} [CommRing R] [Nontrivial R] {x : R}
    (h : IsSMulRegular R x) : x ≠ 0 := by
  rintro rfl
  exact not_subsingleton R (IsSMulRegular.zero_iff_subsingleton.mp h)

/-- In a regular local ring with a regular system of parameters `x, y, …`, the parameter `y` does
not lie in `(x)`. -/
theorem IsRegularLocalRing.notMem_span_singleton_of_ofList_eq {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {x y : R} {rest : List R}
    (hxs : Ideal.ofList (x :: y :: rest) = maximalIdeal R)
    (hlen : (x :: y :: rest).length = (maximalIdeal R).spanFinrank) : y ∉ Ideal.span {x} := by
  obtain ⟨-, hrest⟩ := isSMulRegular_and_isWeaklyRegular_of_ofList_eq hxs hlen
  have hyreg := ((isWeaklyRegular_cons_iff _ y rest).mp hrest).1
  have hxm : x ∈ maximalIdeal R := hxs ▸ Ideal.subset_span (by simp)
  intro hy1
  have hy1' : y • (1 : R) ∈ x • (⊤ : Submodule R R) := by
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hy1
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨t, trivial, by
      simp [← ht, mul_comm]⟩
  have h1 := (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mp hyreg 1 hy1'
  obtain ⟨t, -, ht⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1
  exact (maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ hxm
    (isUnit_iff_exists_inv.mpr ⟨t, by simpa using ht⟩))

/-- The second member of a regular system of parameters of a regular local ring is nonzero. -/
theorem IsRegularLocalRing.ne_zero_of_ofList_eq_cons {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {x y : R} {rest : List R}
    (hxs : Ideal.ofList (x :: y :: rest) = maximalIdeal R)
    (hlen : (x :: y :: rest).length = (maximalIdeal R).spanFinrank) : y ≠ 0 := by
  rintro rfl
  exact IsRegularLocalRing.notMem_span_singleton_of_ofList_eq hxs hlen (Ideal.zero_mem _)

/-- In a regular local ring with a regular system of parameters `x, y, …`, every prime ideal
containing `x` and `y` has height at least two: `(x)` and `(x, y)` are prime ideals, and
`0 ⊊ (x) ⊊ (x, y)`. -/
theorem IsRegularLocalRing.two_le_height_of_mem {R : Type*} [CommRing R] [IsRegularLocalRing R]
    {x y : R} {rest : List R} (hxs : Ideal.ofList (x :: y :: rest) = maximalIdeal R)
    (hlen : (x :: y :: rest).length = (maximalIdeal R).spanFinrank) {q : Ideal R} [q.IsPrime]
    (hx : x ∈ q) (hy : y ∈ q) : 2 ≤ q.height := by
  have := IsRegularLocalRing.isDomain R
  obtain ⟨-, hquot⟩ :=
    (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay R).1
      _ hxs hlen
  have h1 := (hquot 1 (by simp)).1
  have h2 := (hquot 2 (by simp)).1
  simp only [List.take_succ_cons, List.take_zero] at h1 h2
  have hP1 : (Ideal.span {x} : Ideal R).IsPrime := by
    rw [← Ideal.ofList_singleton, ← Ideal.Quotient.isDomain_iff_prime]
    exact @IsRegularLocalRing.isDomain _ _ h1
  have hP2 : (Ideal.ofList [x, y]).IsPrime := by
    rw [← Ideal.Quotient.isDomain_iff_prime]
    exact @IsRegularLocalRing.isDomain _ _ h2
  have hx0 : x ≠ 0 := ne_zero_of_isSMulRegular_self
    (isSMulRegular_and_isWeaklyRegular_of_ofList_eq hxs hlen).1
  have hlt1 : (⊥ : Ideal R) < Ideal.span {x} :=
    bot_lt_iff_ne_bot.mpr fun h => hx0 (by simpa using h)
  have hle12 : Ideal.span {x} ≤ Ideal.ofList [x, y] :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.subset_span (by simp)))
  have hyP2 : y ∈ Ideal.ofList [x, y] := Ideal.subset_span (by simp)
  have hlt12 : Ideal.span {x} < Ideal.ofList [x, y] := lt_of_le_of_ne hle12 fun h =>
    IsRegularLocalRing.notMem_span_singleton_of_ofList_eq hxs hlen (h ▸ hyP2)
  have hle2q : Ideal.ofList [x, y] ≤ q :=
    Ideal.span_le.mpr fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hr
      rcases hr with rfl | rfl <;> assumption
  have : (⊥ : Ideal R).IsPrime := Ideal.isPrime_bot
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt1
  calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
    _ ≤ (⊥ : Ideal R).height + 1 + 1 := by
      gcongr
      exact bot_le
    _ ≤ (Ideal.span {x}).height + 1 := by gcongr
    _ ≤ (Ideal.ofList [x, y]).height := Ideal.height_add_one_le_of_lt_of_isPrime hlt12
    _ ≤ q.height := Ideal.height_mono hle2q

/-- The first member of a regular system of parameters of a regular local ring is nonzero. -/
theorem IsRegularLocalRing.ne_zero_of_ofList_eq {R : Type*} [CommRing R] [IsRegularLocalRing R]
    {x : R} {rest : List R} (hxs : Ideal.ofList (x :: rest) = maximalIdeal R)
    (hlen : (x :: rest).length = (maximalIdeal R).spanFinrank) : x ≠ 0 := by
  have := IsRegularLocalRing.isDomain R
  exact ne_zero_of_isSMulRegular_self (isSMulRegular_and_isWeaklyRegular_of_ofList_eq hxs hlen).1

/-- For an element `r` of `R` acting on an `R`-algebra `T`, the submodule `r • ⊤` of `T` is the
principal ideal generated by the image of `r`. -/
theorem mem_smul_top_iff_mem_span_singleton {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    (r : R) (t : T) : t ∈ r • (⊤ : Submodule R T) ↔ t ∈ Ideal.span {algebraMap R T r} := by
  rw [Submodule.mem_smul_pointwise_iff_exists, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨s, -, rfl⟩
    exact ⟨s, by rw [Algebra.smul_def, mul_comm]⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s, trivial, by rw [Algebra.smul_def, mul_comm]⟩

/-- A nonzero element of `R` is a nonzerodivisor on a domain `T` into which `R` embeds. -/
theorem isSMulRegular_of_ne_zero_of_faithfulSMul {R T : Type*} [CommRing R] [CommRing T]
    [IsDomain T] [Algebra R T] [FaithfulSMul R T] {x : R} (hx : x ≠ 0) : IsSMulRegular T x := by
  have hx' : algebraMap R T x ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R T)).mpr hx
  intro a b h
  simp only [Algebra.smul_def] at h
  exact mul_left_cancel₀ hx' h

/-- **The first two members of a regular system of parameters form a regular sequence on a
normal domain.** Let `R` be a regular local ring with a regular system of parameters `xs`, and let
`T` be a Noetherian normal domain which is an integral extension of `R`. Then the first two members
of `xs` form a weakly regular sequence on `T`. -/
theorem isWeaklyRegular_take_two_of_isIntegrallyClosed {R T : Type*} [CommRing R]
    [IsRegularLocalRing R] [CommRing T] [IsDomain T] [IsNoetherianRing T] [IsIntegrallyClosed T]
    [Algebra R T] [FaithfulSMul R T] [Algebra.IsIntegral R T] {xs : List R}
    (hxs : Ideal.ofList xs = maximalIdeal R) (hlen : xs.length = (maximalIdeal R).spanFinrank) :
    IsWeaklyRegular T (xs.take 2) := by
  have := IsRegularLocalRing.isDomain R
  have := isIntegrallyClosed_of_isRegularLocalRing R
  match xs, hxs, hlen with
  | [], _, _ => exact IsWeaklyRegular.nil R T
  | [x], hxs, hlen =>
    simp only [List.take_succ_cons]
    exact (isWeaklyRegular_singleton_iff T x).mpr
      (isSMulRegular_of_ne_zero_of_faithfulSMul (IsRegularLocalRing.ne_zero_of_ofList_eq hxs hlen))
  | x :: y :: rest, hxs, hlen =>
    simp only [List.take_succ_cons, List.take_zero]
    have hx0 := IsRegularLocalRing.ne_zero_of_ofList_eq hxs hlen
    refine (isWeaklyRegular_cons_iff T x [y]).mpr ⟨isSMulRegular_of_ne_zero_of_faithfulSMul hx0,
      (isWeaklyRegular_singleton_iff _ y).mpr ?_⟩
    refine (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr fun m hm => ?_
    rw [mem_smul_top_iff_mem_span_singleton] at hm ⊢
    rw [Algebra.smul_def] at hm
    exact mem_span_singleton_of_two_le_height hx0
      (fun q hq hxq hyq => IsRegularLocalRing.two_le_height_of_mem hxs hlen hxq hyq) hm
