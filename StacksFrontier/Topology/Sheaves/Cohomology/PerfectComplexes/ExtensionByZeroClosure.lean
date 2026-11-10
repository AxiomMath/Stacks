module

public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.ExtensionByZeroSums

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite ExtensionByZeroModules

universe u

namespace Stacks.Cohomology.LeftDualPerfect

variable {T : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology T) RingCat.{u})
  (P : CochainComplex (SheafOfModules.{u} O) ℤ) {I : ℤ → Type u} (U : ∀ n, I n → Opens T)
  (ιP : ∀ n α, extUnit O (U n α) ⟶ P.X n)

/-- The cofan presenting the term `P^n` as a sum of extensions by zero. -/
abbrev cofanP (n : ℤ) : Cofan (fun α => extUnit O (U n α)) := Cofan.mk (P.X n) (ιP n)

/-- The indices of degree `n` in a finite set of indices of all degrees. -/
def fib (S : Finset (Σ n, I n)) (n : ℤ) : Finset (I n) :=
  S.preimage (Sigma.mk n) (Set.injOn_of_injective sigma_mk_injective)

omit O P U ιP in
/-- An index `α` of degree `n` lies in `fib S n` if and only if `⟨n, α⟩` lies in `S`. -/
theorem mem_fib {S : Finset (Σ n, I n)} {n : ℤ} {α : I n} : α ∈ fib S n ↔ ⟨n, α⟩ ∈ S :=
  Finset.mem_preimage

open Classical in
omit O P U ιP in
/-- The degree-`n` indices of `S` are among the degree-`n` indices of `S ∪ S'`. -/
theorem fib_subset_union_left (S S' : Finset (Σ n, I n)) (n : ℤ) :
    fib S n ⊆ fib (S ∪ S') n := fun _ hα =>
  mem_fib.2 (Finset.mem_union_left _ (mem_fib.1 hα))

open Classical in
omit O P U ιP in
/-- A finite set `S'` of indices of degree `n` is contained in the degree-`n` indices of `S`
with `S'` adjoined in degree `n`. -/
theorem subset_fib_union_map (S : Finset (Σ n, I n)) (n : ℤ) (S' : Finset (I n)) :
    S' ⊆ fib (S ∪ S'.map ⟨Sigma.mk n, sigma_mk_injective⟩) n := fun _ hα =>
  mem_fib.2 (Finset.mem_union_right _ (Finset.mem_map_of_mem _ hα))

open Classical in
omit O P U ιP in
/-- Adjoining indices of degree `m` to `S` does not change its indices of a degree `n ≠ m`. -/
theorem mem_fib_union_map {S : Finset (Σ n, I n)} {n m : ℤ} (hnm : n ≠ m) {S' : Finset (I m)}
    {α : I n} (hα : α ∈ fib (S ∪ S'.map ⟨Sigma.mk m, sigma_mk_injective⟩) n) : α ∈ fib S n := by
  rcases Finset.mem_union.1 (mem_fib.1 hα) with h | h
  · exact mem_fib.2 h
  · obtain ⟨β, -, hβ⟩ := Finset.mem_map.1 h
    exact absurd (congrArg Sigma.fst hβ).symm hnm

/-- Every section of a zero sheaf of modules vanishes. -/
theorem eq_zero_of_isZero {M : SheafOfModules.{u} O} (hM : IsZero M) {Z : Opens T}
    (x : M.val.obj (op Z)) : x = 0 :=
  congrArg (fun φ : M ⟶ M => φ.val.app (op Z) x) (hM.eq_of_src (𝟙 M) 0)

/-- The invariant of the closure construction: over an open `Z ∋ y`, a finite set `S` of
generators of the terms of `P`, of degrees `≥ L`, spans the restrictions of the given sections,
and the differentials of the generators of degree `n ∈ [L, m]` lie in the span in degree
`n + 1`. -/
def ClosureInv (L m : ℤ) {V : Opens T} (y : T) {ι : Type*} (deg : ι → ℤ)
    (s : ∀ i, (P.X (deg i)).val.obj (op V)) : Prop :=
  ∃ (Z : Opens T) (hZ : Z ≤ V), y ∈ Z ∧ ∃ S : Finset (Σ n, I n),
    (∀ x ∈ S, Z ≤ imTop (U x.1 x.2)) ∧ (∀ x ∈ S, L ≤ x.1) ∧
    (∀ i, InSpan O (U (deg i)) (cofanP O P U ιP (deg i)) Z (fib S (deg i)) (resS _ hZ (s i))) ∧
    ∀ n, L ≤ n → n ≤ m → ∀ α ∈ fib S n,
      InSpan O (U (n + 1)) (cofanP O P U ιP (n + 1)) Z (fib S (n + 1))
        ((P.d n (n + 1)).val.app (op Z) (elemSecD O (U n) (cofanP O P U ιP n) α Z))

open Classical in
/-- If every index of `S` has image containing `Z` and every index of `S'`, of degree `m`, has
image containing `Z' ≤ Z`, then every index of `S` with `S'` adjoined in degree `m` has image
containing `Z'`. -/
theorem hall_union_map {Z' Z : Opens T} (hZ' : Z' ≤ Z) {S : Finset (Σ n, I n)}
    (hS : ∀ x ∈ S, Z ≤ imTop (U x.1 x.2)) (m : ℤ) {S' : Finset (I m)}
    (hS' : ∀ α ∈ S', Z' ≤ imTop (U m α)) :
    ∀ x ∈ S ∪ S'.map ⟨Sigma.mk m, sigma_mk_injective⟩, Z' ≤ imTop (U x.1 x.2) := by
  intro x hx
  rcases Finset.mem_union.1 hx with h | h
  · exact hZ'.trans (hS x h)
  · obtain ⟨β, hβ, rfl⟩ := Finset.mem_map.1 h
    exact hS' β hβ

/-- If every index of `S` has image containing `Z`, then so does every index of `fib S n`. -/
theorem fib_le {Z : Opens T} {S : Finset (Σ n, I n)} (hS : ∀ x ∈ S, Z ≤ imTop (U x.1 x.2))
    (n : ℤ) : ∀ α ∈ fib S n, Z ≤ imTop (U n α) := fun α hα => hS ⟨n, α⟩ (mem_fib.1 hα)

/-- Finitely many sections of the terms of `P` in degrees `≥ L` over `V ∋ y` satisfy `ClosureInv`
with `m = L - 1`, in which the condition on differentials is vacuous. -/
theorem closureInv_base (hc : ∀ n, IsColimit (cofanP O P U ιP n)) (L : ℤ) {V : Opens T} (y : T)
    (hy : y ∈ V) {ι : Type*} [Finite ι] (deg : ι → ℤ) (s : ∀ i, (P.X (deg i)).val.obj (op V))
    (hL : ∀ i, L ≤ deg i) : ClosureInv O P U ιP L (L - 1) y deg s := by
  classical
  have := Fintype.ofFinite ι
  have key : ∀ A : Finset ι, ∃ (Z : Opens T) (hZ : Z ≤ V), y ∈ Z ∧ ∃ S : Finset (Σ n, I n),
      (∀ x ∈ S, Z ≤ imTop (U x.1 x.2)) ∧ (∀ x ∈ S, L ≤ x.1) ∧
      ∀ i ∈ A, InSpan O (U (deg i)) (cofanP O P U ιP (deg i)) Z (fib S (deg i))
        (resS _ hZ (s i)) := by
    intro A
    induction A using Finset.induction_on with
    | empty => exact ⟨V, le_rfl, hy, ∅, by simp, by simp, by simp⟩
    | insert i A hi ih =>
      obtain ⟨Z, hZ, hyZ, S, hS, hSL, hA⟩ := ih
      obtain ⟨Z', hZ', hyZ', S', hS'⟩ := exists_nhd_inSpan O (U (deg i))
        (cofanP O P U ιP (deg i)) (hc _) (resS _ hZ (s i)) y hyZ
      have hall := hall_union_map U hZ' hS (deg i) hS'.1
      refine ⟨Z', hZ'.trans hZ, hyZ', _, hall, fun x hx => ?_, fun j hj => ?_⟩
      · rcases Finset.mem_union.1 hx with h | h
        · exact hSL x h
        · obtain ⟨β, -, rfl⟩ := Finset.mem_map.1 h
          exact hL i
      · rw [← resS_resS _ hZ' hZ]
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact hS'.mono O _ _ (subset_fib_union_map _ _ _) (fib_le U hall _)
        · exact ((hA j hj).res O _ _ hZ').mono O _ _ (fib_subset_union_left _ _ _)
            (fib_le U hall _)
  obtain ⟨Z, hZ, hyZ, S, hS, hSL, hA⟩ := key Finset.univ
  exact ⟨Z, hZ, hyZ, S, hS, hSL, fun i => hA i (Finset.mem_univ i),
    fun n hn hn' => absurd (hn.trans hn') (by omega)⟩

/-- If `ClosureInv` holds up to degree `m ≥ L - 1`, then it holds up to degree `m + 1`. -/
theorem closureInv_succ (hc : ∀ n, IsColimit (cofanP O P U ιP n)) (L m : ℤ) (hm : L - 1 ≤ m)
    {V : Opens T} {y : T} {ι : Type*} {deg : ι → ℤ} {s : ∀ i, (P.X (deg i)).val.obj (op V)}
    (h : ClosureInv O P U ιP L m y deg s) : ClosureInv O P U ιP L (m + 1) y deg s := by
  classical
  obtain ⟨Z, hZ, hyZ, S, hS, hSL, hfam, hd⟩ := h
  obtain ⟨Z', hZ', hyZ', S', hS'Z, hS'⟩ := exists_nhd_inSpan_finset O (U (m + 1 + 1))
    (cofanP O P U ιP (m + 1 + 1)) (hc _) (fib S (m + 1))
    (fun α => (P.d (m + 1) (m + 1 + 1)).val.app (op Z)
      (elemSecD O (U (m + 1)) (cofanP O P U ιP (m + 1)) α Z)) y hyZ
  have hall := hall_union_map U hZ' hS (m + 1 + 1) hS'Z
  refine ⟨Z', hZ'.trans hZ, hyZ', _, hall, fun x hx => ?_, fun i => ?_,
    fun n hn hnm α hα => ?_⟩
  · rcases Finset.mem_union.1 hx with h | h
    · exact hSL x h
    · obtain ⟨β, -, rfl⟩ := Finset.mem_map.1 h
      simp only [Function.Embedding.coeFn_mk]
      omega
  · rw [← resS_resS]
    exact ((hfam i).res O _ _ hZ').mono O _ _ (fib_subset_union_left _ _ _) (fib_le U hall _)
  · have hα' : α ∈ fib S n := mem_fib_union_map (by omega) hα
    have hZα : Z ≤ imTop (U n α) := fib_le U hS n α hα'
    have e : (P.d n (n + 1)).val.app (op Z') (elemSecD O (U n) (cofanP O P U ιP n) α Z') =
        resS (P.X (n + 1)) hZ' ((P.d n (n + 1)).val.app (op Z)
          (elemSecD O (U n) (cofanP O P U ιP n) α Z)) :=
      (congrArg ((P.d n (n + 1)).val.app (op Z'))
        (resS_elemSecD O (U n) (cofanP O P U ιP n) α hZ' hZα).symm).trans
        (resS_app (P.d n (n + 1)) hZ' _).symm
    rw [e]
    by_cases hn' : n ≤ m
    · exact ((hd n hn hn' α hα').res O _ _ hZ').mono O _ _ (fib_subset_union_left _ _ _)
        (fib_le U hall _)
    · obtain rfl : n = m + 1 := by omega
      exact (hS' α hα').mono O _ _ (subset_fib_union_map _ _ _) (fib_le U hall _)

/-- **The finite subcomplex generated by finitely many sections, locally.** Let `P` be a complex
of sheaves of modules whose terms are presented as sums of extensions by zero of structure
sheaves, with `P^n = 0` for `n > b`, and let finitely many sections of the terms of `P` in
degrees `≥ L` be given near `y`. Then over some open `Z ∋ y` there is a finite set `S` of
generators, all of degree `≥ L` and all defined over `Z`, spanning the restrictions of the
given sections and such that the differential of each generator lies in the span of the
generators of the next degree. -/
theorem exists_closed_span (hc : ∀ n, IsColimit (cofanP O P U ιP n)) (b L : ℤ)
    (hb : ∀ n, b < n → IsZero (P.X n)) {V : Opens T} (y : T) (hy : y ∈ V) {ι : Type*}
    [Finite ι] (deg : ι → ℤ) (s : ∀ i, (P.X (deg i)).val.obj (op V)) (hL : ∀ i, L ≤ deg i) :
    ∃ (Z : Opens T) (hZ : Z ≤ V), y ∈ Z ∧ ∃ S : Finset (Σ n, I n),
      (∀ x ∈ S, Z ≤ imTop (U x.1 x.2)) ∧ (∀ x ∈ S, L ≤ x.1) ∧
      (∀ i, InSpan O (U (deg i)) (cofanP O P U ιP (deg i)) Z (fib S (deg i)) (resS _ hZ (s i))) ∧
      ∀ n, ∀ α ∈ fib S n,
        InSpan O (U (n + 1)) (cofanP O P U ιP (n + 1)) Z (fib S (n + 1))
          ((P.d n (n + 1)).val.app (op Z) (elemSecD O (U n) (cofanP O P U ιP n) α Z)) := by
  have hinv : ∀ m (hm : L - 1 ≤ m), ClosureInv O P U ιP L m y deg s := fun m hm =>
    Int.leInduction (closureInv_base O P U ιP hc L y hy deg s hL)
      (fun k hk ih => closureInv_succ O P U ιP hc L k hk ih) m hm
  obtain ⟨Z, hZ, hyZ, S, hS, hSL, hfam, hd⟩ := hinv (max b (L - 1)) (le_max_right _ _)
  refine ⟨Z, hZ, hyZ, S, hS, hSL, hfam, fun n α hα => ?_⟩
  by_cases hn : n ≤ max b (L - 1)
  · exact hd n (hSL ⟨n, α⟩ (mem_fib.1 hα)) hn α hα
  · have h0 : (P.d n (n + 1)).val.app (op Z) (elemSecD O (U n) (cofanP O P U ιP n) α Z) = 0 :=
      eq_zero_of_isZero O (hb (n + 1) (by omega)) _
    rw [h0]
    exact inSpan_zero O _ _ (fib_le U hS _)

end Stacks.Cohomology.LeftDualPerfect
