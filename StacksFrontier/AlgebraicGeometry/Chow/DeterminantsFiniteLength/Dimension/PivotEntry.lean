module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.DimensionLeOne
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Reindex
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Spanning
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.LinearCupProduct

/-!
# Pivot entries of admissible sequences

Auxiliary results for Tag 02P9: a nonzero socle element and the length of the quotient by
it, deletion of an entry from an admissible sequence, adjacent swaps, and the pivot entry
at which a given element first appears in the span of an admissible sequence.
-/

@[expose] public section

noncomputable section

namespace Module.FiniteLength
universe u v w

lemma finite_determinant_of_spanning
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) (e : AdmissibleSequence R M)
    (he : Submodule.span R (Set.range e.1) = ⊤) :
    Module.Finite (IsLocalRing.ResidueField R) (determinant R M) :=
  Module.Finite.of_fg_top
    (span_symbol_eq_top hM e he ▸ Submodule.fg_span (Set.finite_singleton (symbol e)))

lemma exists_nonzero_socle_element
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M)
    (hMne : Nontrivial M) :
    ∃ f : M, f ≠ 0 ∧ ∀ r, r ∈ IsLocalRing.maximalIdeal R → r • f = 0 := by
  obtain ⟨s, hshead, hslast⟩ := isFiniteLength_iff_exists_compositionSeries.mp hM
  have hlenpos : 0 < s.length := by
    have hp : (0 : ℕ∞) < Module.length R M := Module.length_pos
    rw [← Module.length_compositionSeries s hshead hslast] at hp
    exact ENat.natCast_lt_natCast.mp hp
  let i : Fin s.length := ⟨0, hlenpos⟩
  let S : Submodule R M := s i.succ
  have hhead : s i.castSucc = ⊥ := by
    simpa [i, RelSeries.head] using hshead
  have hstep : s i.castSucc ⋖ s i.succ := s.step i
  have hcover : (⊥ : Submodule R M) ⋖ S := by
    rw [← hhead]
    change s i.castSucc ⋖ s i.succ
    exact hstep
  have hsimple : IsSimpleModule R S := by
    rw [isSimpleModule_iff_isAtom]
    exact (bot_covBy_iff).mp hcover
  have hSbot : S ≠ ⊥ := by
    intro h
    have := hcover.lt
    simp [h] at this
  obtain ⟨f, hfS, hf0⟩ := S.ne_bot_iff.mp hSbot
  have hAnn : Module.annihilator R S = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (IsSimpleModule.annihilator_isMaximal (R := R) (M := S))
  refine ⟨f, hf0, fun r hr => ?_⟩
  have hrS : r ∈ Module.annihilator R S := by rw [hAnn]; exact hr
  have hkill := (Module.mem_annihilator.mp hrS) ⟨f, hfS⟩
  exact congrArg Subtype.val hkill

lemma socle_quotient_length
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M)
    (f : M) (hf : f ≠ 0)
    (hkill : ∀ r, r ∈ IsLocalRing.maximalIdeal R → r • f = 0) :
    IsFiniteLength R (M ⧸ (R ∙ f)) ∧
      moduleLength R (M ⧸ (R ∙ f)) + 1 = moduleLength R M := by
  let S : Submodule R M := R ∙ f
  have hmax : S ≠ ⊥ := by
    intro h
    have hf' : f ∈ S := Submodule.mem_span_singleton_self f
    rw [h, Submodule.mem_bot] at hf'
    exact hf hf'
  have hsimple : IsSimpleModule R S := by
    rw [isSimpleModule_iff_isAtom]
    apply isAtom_iff_le_of_ge.mpr
    refine ⟨hmax, ?_⟩
    intro T hT hTS
    obtain ⟨z, hz, hzne⟩ := T.ne_bot_iff.mp hT
    obtain ⟨a, hza⟩ := Submodule.mem_span_singleton.mp (hTS hz)
    have hunit : IsUnit a := by
      by_contra ha
      have ha' : a ∈ IsLocalRing.maximalIdeal R := ha
      apply hzne
      rw [← hza, hkill a ha']
    obtain ⟨u, rfl⟩ := hunit
    have hfT : f ∈ T := by
      have hz' : (↑u⁻¹ : R) • z ∈ T := T.smul_mem _ hz
      rw [← hza] at hz'
      simpa [smul_smul, Units.inv_mul, one_smul] using hz'
    apply Submodule.span_le.mpr
    intro z hz
    have hzf : z = f := by simpa using hz
    simpa [hzf] using hfT
  have hSlen : Module.length R S = 1 := Module.length_eq_one (R := R) (M := S)
  have hQfin : IsFiniteLength R (M ⧸ S) :=
    IsFiniteLength.of_surjective hM S.mkQ_surjective
  have hlen' := Module.length_eq_add_of_exact S.subtype S.mkQ (S.subtype_injective)
    S.mkQ_surjective (LinearMap.exact_subtype_mkQ S)
  have hlen : Module.length R M = 1 + Module.length R (M ⧸ S) := by
    rw [hlen', hSlen]
  refine ⟨hQfin, ?_⟩
  change (Module.length R (M ⧸ S)).toNat + 1 = (Module.length R M).toNat
  rw [hlen]
  rw [ENat.toNat_add (by simp) (Module.length_ne_top_iff.mpr hQfin)]
  simp only [ENat.toNat_one]
  omega

/-- Deleting an entry whose image under `q` is that of an earlier element keeps `q`-images of
earlier spans inside the earlier spans of the remaining entries. -/
private theorem map_spanBefore_succAbove_le
    {R : Type u} {M : Type v} {Q : Type w} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]
    {n : ℕ} (q : M →ₗ[R] Q) (e : Fin (n + 1) → M) (i : Fin (n + 1)) (y : M)
    (hqy : q (e i) = q y) (hy : y ∈ spanBefore (R := R) e i) (j : Fin n) :
    (spanBefore (R := R) e (i.succAbove j)).map q ≤
      spanBefore (R := R) (fun k : Fin n => q (e (i.succAbove k))) j := by
  classical
  have hprior (k : Fin (n + 1)) (hk : k < i.succAbove j) (hki : k ≠ i) :
      ∃ j' : Fin n, j' < j ∧ i.succAbove j' = k := by
    obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hki
    refine ⟨j', ?_, hj'⟩
    apply (Fin.succAbove_lt_succAbove_iff).mp
    rwa [hj']
  rw [spanBefore, Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro y ⟨z, ⟨k, hk, rfl⟩, rfl⟩
  by_cases hki : k = i
  · subst k
    have hi_lt : i < i.succAbove j := hk
    have hbefore : (spanBefore (R := R) e i).map q ≤
        spanBefore (R := R) (fun k : Fin n => q (e (i.succAbove k))) j := by
      rw [spanBefore, Submodule.map_span]
      apply Submodule.span_le.mpr
      rintro y ⟨z, ⟨k, hkp, rfl⟩, rfl⟩
      obtain ⟨j', hj', hidx⟩ := hprior k (lt_trans hkp hi_lt) (ne_of_lt hkp)
      exact Submodule.subset_span ⟨j', hj', by simp [hidx]⟩
    rw [hqy]
    exact hbefore (Submodule.mem_map.mpr ⟨y, hy, rfl⟩)
  · obtain ⟨j', hj', hidx⟩ := hprior k hk hki
    exact Submodule.subset_span ⟨j', hj', by simp [hidx]⟩

lemma admissible_delete_quotient
    {R : Type u} {M : Type v} {Q : Type w} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]
    {n : ℕ} (q : M →ₗ[R] Q) (f : M) (hqf : q f = 0)
    (e : Fin (n + 1) → M) (he : IsAdmissibleSequence (R := R) e)
    (i : Fin (n + 1)) (unit : Rˣ) (x : M)
    (hi : e i = (unit : R) • f + x)
    (hx : x ∈ spanBefore (R := R) e i) :
    IsAdmissibleSequence (R := R) (fun j : Fin n => q (e (i.succAbove j))) := by
  intro j r hr
  have hqi : q (e i) = q x := by rw [hi, map_add, map_smul, hqf]; simp
  simpa using map_spanBefore_succAbove_le q e i x hqi hx j
    (Submodule.mem_map_of_mem (he (i.succAbove j) r hr))

/-- The span of the entries before an index is contained in any longer initial span. -/
private lemma spanBefore_le_initialSpan
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {n : ℕ} (e : Fin n → M) (a : Fin n) {k : ℕ} (hak : a.val < k) :
    spanBefore (R := R) e a ≤ initialSpan (R := R) e k := by
  rw [spanBefore_eq_initialSpan]
  exact initialSpan_mono e (le_of_lt hak)
/-- The span of the whole sequence is its initial span at the full length. -/
lemma span_range_eq_initialSpan
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {n : ℕ} (e : Fin n → M) :
    Submodule.span R (Set.range e) = initialSpan (R := R) e n :=
  (initialSpan_all e).symm
/-- Updating an entry leaves the initial spans below its index alone. -/
lemma initialSpan_update_eq_of_le
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {n : ℕ} (e : Fin n → M) (a : Fin n) (replacement : M) {k : ℕ}
    (hk : k ≤ a.val) :
    initialSpan (R := R) e k =
      initialSpan (R := R) (Function.update e a replacement) k :=
  (initialSpan_update_le e a replacement hk).symm
/-- Replacing an entry by a unit multiple of it modulo the earlier entries leaves every
initial span alone. -/
lemma initialSpan_update_eq
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] {n : ℕ} (e : Fin n → M)
    (a : Fin n) (unit : Rˣ) (replacement x : M)
    (ha : e a = (unit : R) • replacement + x)
    (hx : x ∈ spanBefore (R := R) e a) {k : ℕ} (_hak : a.val < k) :
    initialSpan (R := R) e k =
      initialSpan (R := R) (Function.update e a replacement) k :=
  (initialSpan_update e a replacement x unit ha hx k).symm
def swapAdjacent {R : Type u} {M : Type v} [Ring R] [AddCommGroup M]
    [Module R M] {n : ℕ} (e : Fin n → M) (a b : Fin n) : Fin n → M :=
  Function.update (Function.update e b (e a)) a (e b)

lemma initialSpan_swapAdjacent_eq_before
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {n : ℕ} (e : Fin n → M) (a b : Fin n) (hba : b.val + 1 = a.val)
    {k : ℕ} (hk : k ≤ b.val) :
    initialSpan (R := R) e k = initialSpan (R := R) (swapAdjacent (R := R) e a b) k := by
  refine initialSpan_congr fun i hi => ?_
  have hia : i ≠ a := by rintro rfl; omega
  have hib : i ≠ b := by rintro rfl; omega
  simp [swapAdjacent, hia, hib]

lemma initialSpan_swapAdjacent_eq_after
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {n : ℕ} (e : Fin n → M) (a b : Fin n) (hba : b.val + 1 = a.val)
    {k : ℕ} (hk : a.val < k) :
    initialSpan (R := R) e k = initialSpan (R := R) (swapAdjacent (R := R) e a b) k := by
  have hab : b.val < a.val := by omega
  have hne : b ≠ a := by
    intro h
    have := congrArg Fin.val h
    omega
  apply le_antisymm <;> apply Submodule.span_le.mpr <;>
    rintro y ⟨i, hi, rfl⟩
  · by_cases hia : i = a
    · subst i
      exact Submodule.subset_span ⟨b, lt_trans hab hk,
        by simp [swapAdjacent, hne]⟩
    · by_cases hib : i = b
      · subst i
        exact Submodule.subset_span ⟨a, hk, by simp [swapAdjacent]⟩
      · exact Submodule.subset_span ⟨i, hi, by simp [swapAdjacent, hia, hib]
          ⟩
  · by_cases hia : i = a
    · subst i
      exact Submodule.subset_span ⟨b, lt_trans hab hk,
        by simp [swapAdjacent]⟩
    · by_cases hib : i = b
      · subst i
        exact Submodule.subset_span ⟨a, hk, by simp [swapAdjacent, hne]⟩
      · exact Submodule.subset_span ⟨i, hi, by simp [swapAdjacent, hia, hib]
          ⟩

lemma exists_pivot_unit_entry
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] {n : ℕ} (e : Fin n → M)
    (he : IsAdmissibleSequence (R := R) e) (f : M) (hf0 : f ≠ 0)
    (hf : f ∈ Submodule.span R (Set.range e)) :
    ∃ (i : Fin n) (unit : Rˣ) (x : M),
      e i = (unit : R) • f + x ∧
      x ∈ spanBefore (R := R) e i ∧
      f ∈ initialSpan (R := R) e (i.val + 1) ∧
      f ∉ spanBefore (R := R) e i := by
  classical
  have hrange : e '' {j : Fin n | j.val < n} = Set.range e := by
    ext y
    simp [Fin.is_lt]
  have hex : ∃ k, f ∈ initialSpan (R := R) e k := by
    refine ⟨n, ?_⟩
    rwa [initialSpan, hrange]
  let k := Nat.find hex
  have hk : f ∈ initialSpan (R := R) e k := Nat.find_spec hex
  have hkn : k ≤ n := Nat.find_min' hex (by
    rwa [initialSpan, hrange])
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    have hfzero : f = 0 := by
      simpa [initialSpan, hk0] using hk
    exact hf0 hfzero
  let i : Fin n := ⟨k - 1, by omega⟩
  have hik : i.val + 1 = k := by dsimp [i]; omega
  have hxmin : f ∉ initialSpan (R := R) e i.val :=
    Nat.find_min hex (by dsimp [i]; omega)
  have hkip : f ∈ initialSpan (R := R) e (i.val + 1) := by
    simpa [hik] using hk
  have hki : f ∈ Submodule.span R (insert (e i) (e '' Set.Iio i)) := by
    rwa [initialSpan_succ] at hkip
  obtain ⟨r, y, hy, hfy⟩ := Submodule.mem_span_insert.mp hki
  have hr : IsUnit r := by
    by_contra hr
    have hrmax : r ∈ IsLocalRing.maximalIdeal R := hr
    apply hxmin
    rw [hfy]
    exact (spanBefore (R := R) e i).add_mem (he i r hrmax) hy
  obtain ⟨unit, rfl⟩ := hr
  let x : M := -((↑unit⁻¹ : R) • y)
  have hmul : (↑unit⁻¹ : R) • f = e i + (↑unit⁻¹ : R) • y := by
    rw [hfy, smul_add, smul_smul, Units.inv_mul, one_smul]
  have hdecomp : e i = (↑unit⁻¹ : R) • f + x := by
    dsimp [x]
    calc
      e i = e i + (↑unit⁻¹ : R) • y - (↑unit⁻¹ : R) • y := by simp
      _ = (↑unit⁻¹ : R) • f - (↑unit⁻¹ : R) • y := by rw [← hmul]
      _ = (↑unit⁻¹ : R) • f + -((↑unit⁻¹ : R) • y) := by rw [sub_eq_add_neg]
  refine ⟨i, unit⁻¹, x, hdecomp, ?_, ?_, ?_⟩
  · dsimp [x]
    exact (spanBefore (R := R) e i).neg_mem
      ((spanBefore (R := R) e i).smul_mem _ hy)
  · exact hkip
  · simpa [initialSpan, spanBefore, Set.Iio] using hxmin

structure PivotUnitEntry {R : Type u} {M : Type v}
    [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    {n : ℕ} (e : Fin n → M) (f : M) where
  i : Fin n
  unit : Rˣ
  x : M
  decomp : e i = (unit : R) • f + x
  earlier : x ∈ spanBefore (R := R) e i
  pivotMem : f ∈ initialSpan (R := R) e (i.val + 1)
  pivotMin : f ∉ spanBefore (R := R) e i

noncomputable def pivotUnitEntry_swapAdjacent_of_outside
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] {n : ℕ} {e : Fin n → M} {f : M}
    (p : PivotUnitEntry (R := R) e f) (a b : Fin n)
    (hba : b.val + 1 = a.val)
    (hout : p.i.val < b.val ∨ a.val < p.i.val) :
    PivotUnitEntry (R := R) (swapAdjacent (R := R) e a b) f := by
  have hbefore : spanBefore (R := R) e p.i =
      spanBefore (R := R) (swapAdjacent (R := R) e a b) p.i := by
    rw [spanBefore_eq_initialSpan, spanBefore_eq_initialSpan]
    rcases hout with hlt | hgt
    · exact initialSpan_swapAdjacent_eq_before e a b hba (by omega)
    · exact initialSpan_swapAdjacent_eq_after e a b hba hgt
  have hpivot : initialSpan (R := R) e (p.i.val + 1) =
      initialSpan (R := R) (swapAdjacent (R := R) e a b) (p.i.val + 1) := by
    rcases hout with hlt | hgt
    · exact initialSpan_swapAdjacent_eq_before e a b hba (by omega)
    · exact initialSpan_swapAdjacent_eq_after e a b hba (by omega)
  have hia : p.i ≠ a := by
    intro h
    have := congrArg Fin.val h
    rcases hout with hlt | hgt <;> omega
  have hib : p.i ≠ b := by
    intro h
    have := congrArg Fin.val h
    rcases hout with hlt | hgt <;> omega
  refine ⟨p.i, p.unit, p.x, ?_, hbefore ▸ p.earlier,
    hpivot ▸ p.pivotMem, ?_⟩
  · simpa [swapAdjacent, hia, hib] using p.decomp
  · exact fun hf => p.pivotMin (hbefore.symm ▸ hf)

lemma pivotIndex_swapAdjacent_bounds
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] {n : ℕ} (e : Fin n → M) (f : M)
    (p : PivotUnitEntry (R := R) e f) (a b : Fin n)
    (hba : b.val + 1 = a.val) (hlow : b.val ≤ p.i.val)
    (hpi : p.i.val ≤ a.val)
    (p' : PivotUnitEntry (R := R) (swapAdjacent (R := R) e a b) f) :
    b.val ≤ p'.i.val ∧ p'.i.val ≤ a.val := by
  constructor
  · by_contra h
    have hk : p'.i.val + 1 ≤ b.val := by omega
    have hsame := initialSpan_swapAdjacent_eq_before (R := R) e a b hba
      (k := p'.i.val + 1) (by omega)
    have hf : f ∈ initialSpan (R := R) e (p'.i.val + 1) := hsame.symm ▸ p'.pivotMem
    have hle : initialSpan (R := R) e (p'.i.val + 1) ≤
        spanBefore (R := R) e p.i := by
      rw [spanBefore_eq_initialSpan]
      exact initialSpan_mono e (by omega)
    exact p.pivotMin (hle hf)
  · by_contra h
    have hpi' : a.val + 1 ≤ p'.i.val := by omega
    have hle : initialSpan (R := R) e (p.i.val + 1) ≤
        initialSpan (R := R) e (a.val + 1) := initialSpan_mono e (by omega)
    have hsame := initialSpan_swapAdjacent_eq_after (R := R) e a b hba
      (k := a.val + 1) (by omega)
    have hf : f ∈ initialSpan (R := R) (swapAdjacent (R := R) e a b)
        (a.val + 1) := hsame ▸ hle p.pivotMem
    have hle' : initialSpan (R := R) (swapAdjacent (R := R) e a b) (a.val + 1) ≤
        spanBefore (R := R) (swapAdjacent (R := R) e a b) p'.i := by
      rw [spanBefore_eq_initialSpan]
      exact initialSpan_mono _ (by omega)
    exact p'.pivotMin (hle' hf)

lemma pivotUnitEntry_update
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] {n : ℕ} {e : Fin n → M} {f : M}
    (p : PivotUnitEntry (R := R) e f) (a : Fin n) (unit : Rˣ)
    (replacement x : M) (ha : e a = (unit : R) • replacement + x)
    (hx : x ∈ spanBefore (R := R) e a) :
    ∃ p' : PivotUnitEntry (R := R) (Function.update e a replacement) f,
      p'.i = p.i ∧
      (p.i = a → p'.unit = unit⁻¹ * p.unit) ∧
      (p.i ≠ a → p'.unit = p.unit) := by
  classical
  let e' := Function.update e a replacement
  have hcut (k : ℕ) : initialSpan (R := R) e k = initialSpan (R := R) e' k := by
    by_cases hak : a.val < k
    · simpa [e'] using initialSpan_update_eq e a unit replacement x ha hx hak
    · exact initialSpan_update_eq_of_le e a replacement (Nat.le_of_not_gt hak)
  by_cases hia : p.i = a
  · let x' := (↑unit⁻¹ : R) • (p.x - x)
    let unit' := unit⁻¹ * p.unit
    have hbefore : spanBefore (R := R) e a = spanBefore (R := R) e' a := by
      rw [spanBefore_eq_initialSpan, spanBefore_eq_initialSpan]
      exact hcut a.val
    have hx' : x' ∈ spanBefore (R := R) e' a := by
      have hxold : x' ∈ spanBefore (R := R) e a :=
        (spanBefore (R := R) e a).smul_mem _
          ((spanBefore (R := R) e a).sub_mem (by simpa [hia] using p.earlier) hx)
      exact hbefore ▸ hxold
    have hrep : replacement = (↑unit⁻¹ : R) • (e a - x) := by
      calc
        replacement = (↑unit⁻¹ : R) • ((↑unit : R) • replacement) := by simp [smul_smul]
        _ = (↑unit⁻¹ : R) • (e a - x) := by rw [ha]; simp
    have hpdiff : e a - x = (↑p.unit : R) • f + (p.x - x) := by
      have hpdecomp : e a = (↑p.unit : R) • f + p.x := by
        simpa [hia] using p.decomp
      rw [hpdecomp]
      abel
    have hdecomp : e' a = (↑unit' : R) • f + x' := by
      rw [show e' a = replacement by simp [e']]
      calc
        replacement = (↑unit⁻¹ : R) • ((↑p.unit : R) • f + (p.x - x)) := by rw [hrep, hpdiff]
        _ = (↑unit' : R) • f + x' := by
          simp [x', unit', smul_add, smul_smul, Units.val_mul]
    have hmem : f ∈ initialSpan (R := R) e' (a.val + 1) :=
      (hcut (a.val + 1)) ▸ (by simpa [hia] using p.pivotMem)
    have hmin : f ∉ spanBefore (R := R) e' a := by
      intro hf
      apply p.pivotMin
      have hfOld : f ∈ spanBefore (R := R) e a := hbefore.symm ▸ hf
      simpa [hia] using hfOld
    refine ⟨⟨a, unit', x', hdecomp, hx', hmem, hmin⟩, hia.symm, ?_, ?_⟩
    · intro h
      subst a
      rfl
    · intro h
      exact (h hia).elim
  · let p' : PivotUnitEntry (R := R) e' f := {
      i := p.i
      unit := p.unit
      x := p.x
      decomp := by
        simp [e', hia, p.decomp]
      earlier := by
        rw [spanBefore_eq_initialSpan]
        rw [← hcut p.i.val, ← spanBefore_eq_initialSpan]
        exact p.earlier
      pivotMem := (hcut (p.i.val + 1)) ▸ p.pivotMem
      pivotMin := by
        intro hf
        apply p.pivotMin
        rw [spanBefore_eq_initialSpan]
        rw [hcut p.i.val]
        simpa [spanBefore_eq_initialSpan] using hf
    }
    exact ⟨p', rfl, (by intro h; exact (hia h).elim), (by intro _; rfl)⟩

lemma map_spanBefore_le_of_pivot
    {R : Type u} {M : Type v} {Q : Type w} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]
    {n : ℕ} (q : M →ₗ[R] Q) (f : M) (hqf : q f = 0)
    (e : Fin (n + 1) → M) (p : PivotUnitEntry (R := R) e f)
    (j : Fin n) :
    (spanBefore (R := R) e (p.i.succAbove j)).map q ≤
      spanBefore (R := R) (fun k : Fin n => q (e (p.i.succAbove k))) j := by
  refine map_spanBefore_succAbove_le q e p.i p.x ?_ p.earlier j
  rw [p.decomp, map_add, map_smul, hqf]
  simp

lemma pivotUnitEntry_index_eq
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] {n : ℕ} {e : Fin n → M} {f : M}
    (p p' : PivotUnitEntry (R := R) e f) : p.i = p'.i := by
  have key (p p' : PivotUnitEntry (R := R) e f) (hlt : p.i.val < p'.i.val) : False :=
    p'.pivotMin (initialSpan_mono e (Nat.succ_le_of_lt hlt) p.pivotMem)
  by_contra hne
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
  exacts [key p p' hlt, key p' p hlt]

lemma pivotUnitEntry_residue_eq
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] {n : ℕ} {e : Fin n → M} {f : M}
    (p p' : PivotUnitEntry (R := R) e f) :
    IsLocalRing.residue R (p.unit : R) = IsLocalRing.residue R (p'.unit : R) := by
  have hi : p.i = p'.i := pivotUnitEntry_index_eq p p'
  have hidx : p'.i = p.i := hi.symm
  by_contra hres
  have hdiff : IsLocalRing.residue R ((p.unit : R) - (p'.unit : R)) ≠ 0 := by
    rw [map_sub]
    intro hz
    apply hres
    exact sub_eq_zero.mp hz
  have hnot : (p.unit : R) - (p'.unit : R) ∉ IsLocalRing.maximalIdeal R := by
    intro hmem
    exact hdiff ((IsLocalRing.residue_eq_zero_iff _).2 hmem)
  have hunit : IsUnit ((p.unit : R) - (p'.unit : R)) := by
    by_contra h
    exact hnot h
  obtain ⟨a, ha⟩ := hunit
  have hcoeff : ((p.unit : R) - (p'.unit : R)) • f = p'.x - p.x := by
    have hp' : e p.i = (p'.unit : R) • f + p'.x := by
      simpa [hidx] using p'.decomp
    have hpUnit : (p.unit : R) • f = e p.i - p.x := by
      rw [p.decomp]
      abel
    have hp'Unit : (p'.unit : R) • f = e p.i - p'.x := by
      rw [hp']
      abel
    calc
      ((p.unit : R) - (p'.unit : R)) • f =
          (p.unit : R) • f - (p'.unit : R) • f := by rw [sub_smul]
      _ = (e p.i - p.x) - (e p.i - p'.x) := by
        rw [hpUnit, hp'Unit]
      _ = p'.x - p.x := by abel
  have hxy : p'.x - p.x ∈ spanBefore (R := R) e p.i :=
    (spanBefore (R := R) e p.i).sub_mem (by simpa [hidx] using p'.earlier) p.earlier
  have hfprev : f ∈ spanBefore (R := R) e p.i := by
    have hmem := (spanBefore (R := R) e p.i).smul_mem
      (↑a⁻¹ : R) hxy
    have hmem' : (↑a⁻¹ : R) •
        (((p.unit : R) - (p'.unit : R)) • f) ∈ spanBefore (R := R) e p.i := by
      rwa [hcoeff]
    have hmul1 : (↑a⁻¹ : R) * ((p.unit : R) - (p'.unit : R)) = 1 := by
      rw [← ha]
      change (↑(a⁻¹ * a) : R) = 1
      exact congrArg (fun z : Rˣ => (z : R)) (inv_mul_cancel a)
    simpa only [smul_smul, hmul1, one_smul] using hmem'
  exact p.pivotMin hfprev

noncomputable def choosePivotEntry
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] {n : ℕ} (e : Fin n → M)
    (he : IsAdmissibleSequence (R := R) e) (f : M) (hf0 : f ≠ 0)
    (hspan : f ∈ Submodule.span R (Set.range e)) : PivotUnitEntry (R := R) e f := by
  let hexists := exists_pivot_unit_entry e he f hf0 hspan
  let i := Classical.choose hexists
  have hrest := Classical.choose_spec hexists
  let unit := Classical.choose hrest
  have hrest' := Classical.choose_spec hrest
  let x := Classical.choose hrest'
  have hparts := Classical.choose_spec hrest'
  exact ⟨i, unit, x, hparts.1, hparts.2.1, hparts.2.2.1, hparts.2.2.2⟩

end Module.FiniteLength

end
