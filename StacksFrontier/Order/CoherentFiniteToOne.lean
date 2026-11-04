module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.SetTheory.Cardinal.Aleph

/-!
# A coherent family of finite-to-one functions on an uncountable well-order

Let `I` be a well-ordered type each of whose proper initial segments is countable — the
motivating example is the type of countable ordinals. This file builds, by recursion along `I`,
a family of functions `F a : I → ℕ` indexed by `a : I` such that

* `F a` is **finite-to-one on the initial segment below `a`**, and
* the family is **coherent**: `F a` and `F c` agree below `c` outside a finite set, for `c < a`.

When `I` is in addition uncountable and every countable subset of `I` is bounded, no single
function `g : I → ℕ` agrees with every `F a` below `a` outside a finite set: such a `g` would be
finite-to-one on every initial segment, hence finite-to-one, and would therefore exhibit `I` as
a countable union of finite sets.

That last statement is the point of the construction. The family is a nontrivial *coherent
sequence*: its germs are compatible but not uniformizable.

## Main definitions

* `Stacks.Coherent.F`: the family, defined by well-founded recursion along `I`.

## Main results

* `Stacks.Coherent.finite_fibre_F`: `F a` is finite-to-one below `a`.
* `Stacks.Coherent.finite_ne_F`: the family is coherent.
* `Stacks.Coherent.not_uniformizable`: no single function into a countable type uniformizes the
  family.

## Implementation notes

The recursion distinguishes three cases at `a`, by the shape of the initial segment below it.
If that segment is empty the value is `0`. If it has a greatest element `pred a` the value is
copied from `F (pred a)` below `pred a` and is `0` at `pred a` itself; copying rather than
modifying keeps the coherence at a successor *exact*, which is what makes the successor step of
both inductions trivial.

The limit case is the only one with content. A monotone cofinal sequence `seq a : ℕ → I` below
`a` exists because the segment is countable with no greatest element — enumerate the segment and
take running maxima — and `γ` below `a` lies below `seq a n` for a least `n`, its *block index*.
Copying the value of the stage at that block would be coherent but need not be finite-to-one,
since infinitely many blocks contribute to one fibre; taking instead the **maximum of that value
and the block index** forces the value at `γ` to be at least its block index, so a fibre meets
only the first finitely many blocks. Coherence survives this modification because below a fixed
`c < a` only the finitely many blocks up to the one containing `c` occur, and because `F c` is
itself finite-to-one below `c`, so `F c` exceeds the relevant bound outside a finite set and the
maximum is attained by the copied value there.

Coherence is therefore proved *after* finite-to-oneness and uses it; both are proved by
well-founded induction along `I`, and the limit step of the coherence induction compares `F a`
and `F c` through the single intermediate stage `seq a N` for an `N` with `c < seq a N`.

The hypotheses on `I` are carried as explicit arguments rather than as instances: the
countability of initial segments and the boundedness of countable subsets are properties of the
intended instance, the countable ordinals, which no typeclass in the library names.
-/

@[expose] public noncomputable section

attribute [local instance] Classical.propDecidable

namespace Stacks.Coherent

universe u v

variable {I : Type u} [LinearOrder I] [WellFoundedLT I]

/-! ### Cofinal sequences below a point -/

/-- A monotone sequence below `a` which is cofinal there: every point below `a` is strictly
below one of its terms. -/
def IsCofinalSeq (a : I) (b : ℕ → I) : Prop :=
  (∀ n, b n < a) ∧ Monotone b ∧ ∀ γ < a, ∃ n, γ < b n

omit [WellFoundedLT I] in
/-- A point below which the initial segment is countable, nonempty and has no greatest element
admits a monotone cofinal sequence. -/
theorem exists_isCofinalSeq {a : I} (hc : (Set.Iio a).Countable) (hne : (Set.Iio a).Nonempty)
    (hnomax : ∀ γ < a, ∃ δ, γ < δ ∧ δ < a) : ∃ b : ℕ → I, IsCofinalSeq a b := by
  classical
  obtain ⟨e, he⟩ := hc.exists_eq_range hne
  have hmem : ∀ n, e n < a := by
    intro n
    have hn : e n ∈ Set.Iio a := by rw [he]; exact Set.mem_range_self n
    exact hn
  refine ⟨fun n ↦ ((Finset.range (n + 1)).image e).max'
    ⟨e 0, Finset.mem_image_of_mem e (Finset.mem_range.mpr n.succ_pos)⟩, ?_, ?_, ?_⟩
  · intro n
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp (Finset.max'_mem
      ((Finset.range (n + 1)).image e)
      ⟨e 0, Finset.mem_image_of_mem e (Finset.mem_range.mpr n.succ_pos)⟩)
    have hlt : ((Finset.range (n + 1)).image e).max'
        ⟨e 0, Finset.mem_image_of_mem e (Finset.mem_range.mpr n.succ_pos)⟩ < a := hk ▸ hmem k
    exact hlt
  · intro m n hmn
    refine Finset.max'_le _ _ _ fun y hy ↦ ?_
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    refine Finset.le_max' _ _ (Finset.mem_image.mpr ⟨k, ?_, rfl⟩)
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) (by omega))
  · intro γ hγ
    obtain ⟨δ, hγδ, hδa⟩ := hnomax γ hγ
    have hδ : δ ∈ Set.range e := by rw [← he]; exact hδa
    obtain ⟨k, hk⟩ := hδ
    exact ⟨k, lt_of_lt_of_le hγδ
      (hk ▸ Finset.le_max' _ _ (Finset.mem_image.mpr ⟨k, by simp, rfl⟩))⟩

/-- `a` is a *limit point* when there is a monotone cofinal sequence below it. -/
def IsLimitPt (a : I) : Prop := ∃ b : ℕ → I, IsCofinalSeq a b

/-- The chosen monotone cofinal sequence below a limit point. -/
def seq (a : I) : ℕ → I := if h : IsLimitPt a then h.choose else fun _ ↦ a

omit [WellFoundedLT I] in
/-- The chosen sequence below a limit point is cofinal there. -/
theorem isCofinalSeq_seq {a : I} (h : IsLimitPt a) : IsCofinalSeq a (seq a) := by
  rw [seq, dif_pos h]
  exact h.choose_spec

/-- `a` has a *predecessor* when the initial segment below it has a greatest element. -/
def HasPred (a : I) : Prop := ∃ c, c < a ∧ ∀ d, d < a → d ≤ c

/-- The greatest element below `a`, when there is one. -/
def pred (a : I) : I := if h : HasPred a then h.choose else a

omit [WellFoundedLT I] in
/-- The predecessor lies below the point. -/
theorem pred_lt {a : I} (h : HasPred a) : pred a < a := by
  rw [pred, dif_pos h]
  exact h.choose_spec.1

omit [WellFoundedLT I] in
/-- Every point below `a` is at most the predecessor of `a`. -/
theorem le_pred {a : I} (h : HasPred a) {d : I} (hd : d < a) : d ≤ pred a := by
  rw [pred, dif_pos h]
  exact h.choose_spec.2 d hd

omit [WellFoundedLT I] in
/-- A point which is neither a limit point nor a successor has nothing below it, provided
initial segments are countable. -/
theorem Iio_eq_empty_of_not {a : I} (hc : (Set.Iio a).Countable) (hl : ¬ IsLimitPt a)
    (hp : ¬ HasPred a) : Set.Iio a = ∅ := by
  by_contra hne
  refine hl (exists_isCofinalSeq hc (Set.nonempty_iff_ne_empty.mpr hne) fun γ hγ ↦ ?_)
  by_contra hno
  refine hp ⟨γ, hγ, fun d hd ↦ ?_⟩
  by_contra hdγ
  exact hno ⟨d, lt_of_not_ge hdγ, hd⟩

/-! ### The family -/

/-- One step of the recursion defining `Stacks.Coherent.F`. At a limit point the value at `γ`
is the maximum of the value of the stage at the block of `γ` and the index of that block; at a
successor it is copied from the predecessor. -/
def step (a : I) (ih : ∀ b, b < a → I → ℕ) : I → ℕ := fun γ ↦
  if hl : IsLimitPt a then
    if hγ : ∃ n, γ < seq a n then
      max (ih (seq a (Nat.find hγ)) ((isCofinalSeq_seq hl).1 _) γ) (Nat.find hγ)
    else 0
  else if hp : HasPred a then
    if γ < pred a then ih (pred a) (pred_lt hp) γ else 0
  else 0

/-- The coherent family of finite-to-one functions: `F a` is finite-to-one below `a`, and the
family is coherent. -/
def F : I → I → ℕ := wellFounded_lt.fix step

/-- The defining equation of `Stacks.Coherent.F`. -/
theorem F_eq (a : I) : F a = step a fun b _ ↦ F b :=
  wellFounded_lt.fix_eq step a

/-- The value of the family at a limit point: the maximum of the value of the stage at the block
of the argument and the index of that block. -/
theorem F_limit {a : I} (hl : IsLimitPt a) {γ : I} (hγ : ∃ n, γ < seq a n) :
    F a γ = max (F (seq a (Nat.find hγ)) γ) (Nat.find hγ) := by
  rw [F_eq a, step, dif_pos hl, dif_pos hγ]

/-- The value of the family at a successor, below the predecessor: copied from there. -/
theorem F_pred {a : I} (hl : ¬ IsLimitPt a) (hp : HasPred a) {γ : I} (hγ : γ < pred a) :
    F a γ = F (pred a) γ := by
  rw [F_eq a, step, dif_neg hl, dif_pos hp, if_pos hγ]

omit [WellFoundedLT I] in
/-- At a limit point, lying below some term of the cofinal sequence is lying below the point. -/
theorem exists_lt_seq_iff {a : I} (hl : IsLimitPt a) (γ : I) :
    (∃ n, γ < seq a n) ↔ γ < a :=
  ⟨fun ⟨n, hn⟩ ↦ hn.trans ((isCofinalSeq_seq hl).1 n), (isCofinalSeq_seq hl).2.2 γ⟩

/-! ### Finite-to-oneness -/

/-- **`F a` is finite-to-one below `a`.** -/
theorem finite_fibre_F (hcnt : ∀ a : I, (Set.Iio a).Countable) (a : I) :
    ∀ n : ℕ, {γ : I | γ < a ∧ F a γ = n}.Finite := by
  induction a using WellFoundedLT.induction with
  | ind a ih =>
  intro n
  by_cases hl : IsLimitPt a
  · refine Set.Finite.subset
      (Set.Finite.biUnion (Set.finite_le_nat n) fun k _ ↦
        Set.Finite.biUnion (Set.finite_le_nat n) fun j _ ↦
          ih (seq a k) ((isCofinalSeq_seq hl).1 k) j) ?_
    rintro γ ⟨hγa, hγn⟩
    have hex : ∃ m, γ < seq a m := (exists_lt_seq_iff hl γ).mpr hγa
    rw [F_limit hl hex] at hγn
    exact Set.mem_biUnion (show Nat.find hex ≤ n by omega)
      (Set.mem_biUnion (show F (seq a (Nat.find hex)) γ ≤ n by omega)
        ⟨Nat.find_spec hex, rfl⟩)
  · by_cases hp : HasPred a
    · refine Set.Finite.subset
        ((ih (pred a) (pred_lt hp) n).union (Set.finite_singleton (pred a))) ?_
      rintro γ ⟨hγa, hγn⟩
      by_cases hγp : γ < pred a
      · exact Or.inl ⟨hγp, (F_pred hl hp hγp).symm.trans hγn⟩
      · exact Or.inr (le_antisymm (le_pred hp hγa) (le_of_not_gt hγp))
    · refine Set.Finite.subset Set.finite_empty ?_
      rintro γ ⟨hγa, -⟩
      have : γ ∈ Set.Iio a := hγa
      rw [Iio_eq_empty_of_not (hcnt a) hl hp] at this
      exact this.elim

/-- Below `a` the function `F a` takes each value under a given bound on a finite set. -/
theorem finite_lt_F (hcnt : ∀ a : I, (Set.Iio a).Countable) (a : I) (N : ℕ) :
    {γ : I | γ < a ∧ F a γ < N}.Finite := by
  refine Set.Finite.subset (Set.Finite.biUnion (Set.finite_lt_nat N) fun j _ ↦
    finite_fibre_F hcnt a j) ?_
  rintro γ ⟨hγa, hγN⟩
  exact Set.mem_biUnion hγN ⟨hγa, rfl⟩

/-! ### Coherence -/

/-- **The family is coherent.** `F a` and `F c` agree below `c` outside a finite set whenever
`c < a`. -/
theorem finite_ne_F (hcnt : ∀ a : I, (Set.Iio a).Countable) (a : I) :
    ∀ c < a, {γ : I | γ < c ∧ F a γ ≠ F c γ}.Finite := by
  induction a using WellFoundedLT.induction with
  | ind a ih =>
  intro c hca
  by_cases hl : IsLimitPt a
  · obtain ⟨N, hN⟩ := (isCofinalSeq_seq hl).2.2 c hca
    have hda : seq a N < a := (isCofinalSeq_seq hl).1 N
    have hEk : ∀ k ∈ {k : ℕ | k ≤ N},
        {γ : I | γ < seq a k ∧ F (seq a N) γ ≠ F (seq a k) γ}.Finite := by
      intro k hk
      rcases lt_or_eq_of_le ((isCofinalSeq_seq hl).2.1 (show k ≤ N from hk)) with h | h
      · exact ih (seq a N) hda (seq a k) h
      · refine Set.Finite.subset Set.finite_empty ?_
        rintro γ ⟨-, hne⟩
        exact absurd (by rw [h]) hne
    refine Set.Finite.subset
      ((Set.Finite.biUnion (Set.finite_le_nat N) hEk).union
        ((ih (seq a N) hda c hN).union (finite_lt_F hcnt c N))) ?_
    rintro γ ⟨hγc, hne⟩
    have hex : ∃ n, γ < seq a n := ⟨N, hγc.trans hN⟩
    have hmN : Nat.find hex ≤ N := Nat.find_le (hγc.trans hN)
    have hγm : γ < seq a (Nat.find hex) := Nat.find_spec hex
    by_contra hmem
    simp only [Set.mem_union, not_or] at hmem
    obtain ⟨h1, h2, h3⟩ := hmem
    have e1 : F (seq a N) γ = F (seq a (Nat.find hex)) γ := by
      by_contra hne1
      exact h1 (Set.mem_biUnion (show Nat.find hex ≤ N from hmN) ⟨hγm, hne1⟩)
    have e2 : F (seq a N) γ = F c γ := by
      by_contra hne2
      exact h2 ⟨hγc, hne2⟩
    have e3 : N ≤ F c γ := by
      by_contra hlt
      exact h3 ⟨hγc, lt_of_not_ge hlt⟩
    rw [F_limit hl hex, ← e1, e2, max_eq_left (hmN.trans e3)] at hne
    exact hne rfl
  · by_cases hp : HasPred a
    · rcases eq_or_lt_of_le (le_pred hp hca) with h | h
      · refine Set.Finite.subset Set.finite_empty ?_
        rintro γ ⟨hγc, hne⟩
        have hγp : γ < pred a := h ▸ hγc
        have heq := F_pred hl hp hγp
        rw [← h] at heq
        exact absurd heq hne
      · refine Set.Finite.subset (ih (pred a) (pred_lt hp) c h) ?_
        rintro γ ⟨hγc, hne⟩
        exact ⟨hγc, by rwa [F_pred hl hp (hγc.trans h)] at hne⟩
    · refine Set.Finite.subset Set.finite_empty ?_
      rintro γ ⟨hγc, -⟩
      have : c ∈ Set.Iio a := hca
      rw [Iio_eq_empty_of_not (hcnt a) hl hp] at this
      exact this.elim

/-! ### Non-uniformizability -/

omit [WellFoundedLT I] in
/-- **A countable subset of `I` is bounded above**, when `I` is uncountable and every initial
segment of `I` is countable. -/
theorem exists_gt_of_countable [Uncountable I] (hcnt : ∀ a : I, (Set.Iio a).Countable)
    (s : Set I) (hs : s.Countable) : ∃ a : I, ∀ x ∈ s, x < a := by
  by_contra hno
  simp only [not_exists, not_forall] at hno
  have hcov : (⋃ x ∈ s, Set.Iic x) = Set.univ := by
    refine Set.eq_univ_of_forall fun y ↦ ?_
    obtain ⟨x, hxs, hxy⟩ := hno y
    exact Set.mem_biUnion hxs (le_of_not_gt hxy)
  refine absurd ?_ ((Set.not_countable_univ_iff (α := I)).mpr inferInstance)
  rw [← hcov]
  refine hs.biUnion fun x _ ↦ ?_
  have hIic : Set.Iic x = Set.Iio x ∪ {x} := by
    ext y
    simp [Set.mem_Iic, le_iff_lt_or_eq]
  exact hIic ▸ (hcnt x).union (Set.countable_singleton x)

omit [WellFoundedLT I] in
/-- A function on `I` all of whose fibres below every point are finite has finite fibres, when
every countable subset of `I` is bounded. -/
theorem finite_fibre_of_finite_fibre_Iio {K : Type v}
    (hbdd : ∀ s : Set I, s.Countable → ∃ a : I, ∀ x ∈ s, x < a) {g : I → K}
    (hg : ∀ (a : I) (n : K), {γ : I | γ < a ∧ g γ = n}.Finite) (n : K) :
    {γ : I | g γ = n}.Finite := by
  by_contra hinf
  have hinf' : Set.Infinite {γ : I | g γ = n} := hinf
  obtain ⟨e⟩ : Nonempty (ℕ ↪ {γ : I | g γ = n}) := ⟨hinf'.natEmbedding _⟩
  obtain ⟨a, ha⟩ := hbdd (Set.range fun k : ℕ ↦ (e k : I)) (Set.countable_range _)
  refine Set.infinite_range_of_injective
    (f := fun k : ℕ ↦ (e k : I)) (fun k l hkl ↦ e.injective (Subtype.ext hkl))
    ((hg a n).subset ?_)
  rintro x ⟨k, rfl⟩
  exact ⟨ha _ ⟨k, rfl⟩, (e k).2⟩

/-- **The family is not uniformizable.** On an uncountable well-order whose initial segments are
countable, no single function `g : I → K` into a countable type agrees, after relabelling the
values of the family by an injection `f : ℕ → K`, with every `F a` below `a` outside a finite set.
-/
theorem not_uniformizable [Uncountable I] {K : Type v} [Countable K]
    (hcnt : ∀ a : I, (Set.Iio a).Countable)
    (f : ℕ → K) (hf : Function.Injective f) (g : I → K) :
    ¬ ∀ a : I, {γ : I | γ < a ∧ f (F a γ) ≠ g γ}.Finite := by
  intro hunif
  have hg : ∀ (a : I) (k : K), {γ : I | γ < a ∧ g γ = k}.Finite := by
    intro a k
    by_cases hk : ∃ n, f n = k
    · obtain ⟨n, hn⟩ := hk
      refine Set.Finite.subset ((hunif a).union (finite_fibre_F hcnt a n)) ?_
      rintro γ ⟨hγa, hγk⟩
      by_cases h : f (F a γ) = g γ
      · exact Or.inr ⟨hγa, hf (by rw [h, hγk, ← hn])⟩
      · exact Or.inl ⟨hγa, h⟩
    · refine Set.Finite.subset (hunif a) ?_
      rintro γ ⟨hγa, hγk⟩
      exact ⟨hγa, by rw [hγk]; exact fun h ↦ hk ⟨F a γ, h⟩⟩
  have huniv : (Set.univ : Set I).Countable := by
    have he : (⋃ k : K, {γ : I | g γ = k}) = Set.univ :=
      Set.eq_univ_of_forall fun γ ↦ Set.mem_iUnion.mpr ⟨g γ, rfl⟩
    exact he ▸ Set.countable_iUnion fun k ↦
      (finite_fibre_of_finite_fibre_Iio (exists_gt_of_countable hcnt) hg k).countable
  exact (Set.not_countable_univ_iff.mpr inferInstance) huniv

end Stacks.Coherent

end
