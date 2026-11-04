module

import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.ENatToNat
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.Depth.Criteria
import StacksFrontier.RingTheory.Depth.Dimension
public import StacksFrontier.RingTheory.RegularLocalRing.Criteria
public import StacksFrontier.RingTheory.Serre.Reduced
import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.Depth.Nakayama
public import StacksFrontier.RingTheory.CohenMacaulay.RegularSequence.ReesExchange

/-!
# A regular sequence in `B` coming from a map of local rings

Last part of the proof of `exists_isRegular_map_length_eq_ringKrullDim` (Stacks 06LC): regular
sequences shorter than the depth extend, the quotient of a Cohen–Macaulay local ring by a regular
element of its maximal ideal is Cohen–Macaulay, and the induction on `dim B`.

## Main results

* `exists_smulRegular_of_regular_lt_depth`, `exists_isRegular_cons_head_of_maximal`: extending
  regular sequences in the maximal ideal.
* `cohenMacaulay_quotient_span_singleton_of_isSMulRegular`: Cohen–Macaulayness descends to the
  quotient by a regular element.
* `exists_list_isRegular_map_of_ringKrullDim_eq`: the inductive engine.
* `exists_isRegular_map_length_eq_ringKrullDim`: Stacks 06LC.
-/

@[expose] public section

/-- If a regular sequence in the maximal ideal is shorter than the depth of `R`, then some
element of the maximal ideal acts regularly on the corresponding quotient, so the sequence
can be extended. -/
theorem exists_smulRegular_of_regular_lt_depth {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (rs : List R) (hrsm : ∀ x ∈ rs, x ∈ IsLocalRing.maximalIdeal R)
    (hrsR : RingTheory.Sequence.IsRegular R rs)
    (hlt : (rs.length : ℕ∞) < Module.depthSup R (IsLocalRing.maximalIdeal R) R) :
    ∃ x ∈ IsLocalRing.maximalIdeal R,
      IsSMulRegular (R ⧸ Ideal.ofList rs • (⊤ : Submodule R R)) x := by
  -- Assembly: the depth-additivity positivity
  -- `depth_pos_quot_of_length_lt_depth` gives `0 < depth (R ⧸ ofList rs • ⊤)`, and the
  -- helper `exists_smulRegular_of_depth_pos` extracts a regular element of m_R.
  exact exists_smulRegular_of_depth_pos (depth_pos_quot_of_length_lt_depth rs hrsm hrsR hlt)

/-- **Iteration: a prescribed regular head extends to length `k ≤ depth R`.**
Given an `R`-regular element `r ∈ m_R` and `1 ≤ k ≤ depth R m_R R`, there is an
`R`-regular sequence in `m_R` of length exactly `k` whose head is `r`.

INFORMAL PROOF.
Induct on `k` upward from `k = 1`.
- Base `k = 1`: `[r]` is `R`-regular (`isRegular_cons_iff ⟨hr, IsRegular.nil⟩`, using
  `Nontrivial R`), all entries `r ∈ m_R` by `hrm`.
- Step `k → k+1` (`k+1 ≤ depth R`): we have `r :: us` `R`-regular of length `k`.  Since
  `(k : ℕ∞) < (k+1 : ℕ∞) ≤ depth R`, `exists_smulRegular_of_regular_lt_depth`
  applied to `rs = r :: us` gives `a ∈ m_R` with `IsSMulRegular (R ⧸ ofList (r::us) • ⊤) a`.
  As `a ∈ m_R` is a non-unit, `IsRegular (R ⧸ ofList (r::us) • ⊤) [a]` holds (the
  appended-ideal properness, via `isRegular_cons_iff` +
  `nontrivial_quotSMulTop_of_mem_maximalIdeal`).
  Then `isRegular_snoc_iff` gives `IsRegular R ((r :: us) ++ [a])`, a length-`(k+1)`
  sequence with head `r`.  Take `us' = us ++ [a]`. -/
theorem exists_isRegular_cons_head_length_of_le_depth {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {r : R} (hr : IsSMulRegular R r) (hrm : r ∈ IsLocalRing.maximalIdeal R) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : (k : ℕ∞) ≤ Module.depthSup R (IsLocalRing.maximalIdeal R) R) :
    ∃ us : List R,
      (∀ x ∈ us, x ∈ IsLocalRing.maximalIdeal R) ∧
        RingTheory.Sequence.IsRegular R (r :: us) ∧ (r :: us).length = k := by
  induction k, hk1 using Nat.le_induction with
  | base =>
    refine ⟨[], by simp, ?_, by simp⟩
    rw [RingTheory.Sequence.isRegular_cons_iff]
    have : Nontrivial (QuotSMulTop r R) := nontrivial_quotSMulTop_of_mem_maximalIdeal R hrm
    exact ⟨hr, RingTheory.Sequence.IsRegular.nil _ _⟩
  | succ k hk1
    ih =>
    have hk' : (k : ℕ∞) ≤ Module.depthSup R (IsLocalRing.maximalIdeal R) R := by
      refine le_trans ?_ hk
      exact_mod_cast Nat.le_succ k
    obtain ⟨us, husmem, husreg, huslen⟩ := ih hk'
    -- length of r :: us is k
    have hlt : ((r :: us).length : ℕ∞) < Module.depthSup R (IsLocalRing.maximalIdeal R) R := by
      rw [huslen]
      refine lt_of_lt_of_le ?_ hk
      exact_mod_cast Nat.lt_succ_self k
    have hmem : ∀ x ∈ (r :: us), x ∈ IsLocalRing.maximalIdeal R := by
      intro x hx
      rcases List.mem_cons.mp hx with h | h
      · rw [h]; exact hrm
      · exact husmem x h
    obtain ⟨a, ham, hareg⟩ := exists_smulRegular_of_regular_lt_depth (r :: us) hmem husreg hlt
    -- All entries of `(r :: us) ++ [a]` lie in `m_R`.
    have hmem' : ∀ x ∈ ((r :: us) ++ [a]), x ∈ IsLocalRing.maximalIdeal R := by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hmem x h
      · rw [List.mem_singleton.mp h]; exact ham
    -- Properness: `ofList ((r::us) ++ [a]) ⊆ m_R ≠ ⊤`, so its `• ⊤` is proper.
    have hprop : Ideal.ofList ((r :: us) ++ [a]) • (⊤ : Submodule R R) ≠ ⊤ := by
      rw [smul_eq_mul, Ideal.mul_top]
      intro h
      have hle : Ideal.ofList ((r :: us) ++ [a]) ≤ IsLocalRing.maximalIdeal R := by
        rw [Ideal.ofList, Ideal.span_le]
        intro x hx
        exact hmem' x hx
      rw [h] at hle
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp hle)
    -- Assemble `IsRegular R ((r :: us) ++ [a])` directly via `isRegular_iff` +
    -- `isWeaklyRegular_append_iff` (avoiding the not-yet-in-scope `isRegular_snoc_iff`).
    have hsnoc : RingTheory.Sequence.IsRegular R ((r :: us) ++ [a]) := by
      rw [RingTheory.Sequence.isRegular_iff]
      refine ⟨?_, hprop.symm⟩
      rw [RingTheory.Sequence.isWeaklyRegular_append_iff]
      rw [RingTheory.Sequence.isRegular_iff] at husreg
      refine ⟨husreg.left, ?_⟩
      rw [RingTheory.Sequence.isWeaklyRegular_cons_iff']
      exact ⟨hareg, RingTheory.Sequence.IsWeaklyRegular.nil _ _⟩
    refine ⟨us ++ [a], ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact husmem x h
      · rw [List.mem_singleton.mp h]; exact ham
    · simpa using hsnoc
    · simp only [List.length_cons, List.length_append, List.length_nil]
      simp only [List.length_cons] at huslen
      omega

/-- **Depth drops by at most one modulo a regular element (Stacks 00LK / 00LF).**
For an `R`-regular element `r ∈ m_R`, `depth R m_R R ≤ depth R m_R N + 1` where
`N = QuotSMulTop r R`.

INFORMAL PROOF.  Let `d = depth R`.  `d ≠ ⊤` (regular
sequence lengths are bounded by `supportDim R = ringKrullDim R < ⊤`).  If `d = 0` the
goal `0 ≤ depth N + 1` is trivial.  Else `1 ≤ d`; the iteration
(`exists_isRegular_cons_head_length_of_le_depth` with `k = d`) gives an `R`-regular
`r :: us` in `m_R` of length `d`.  `isRegular_cons_iff` peels `r`: `us` is `N`-regular
in `m_R` of length `d - 1`, so `↑us.length ≤ depth N`, i.e. `↑(d-1) ≤ depth N`,
whence `d = (d-1) + 1 ≤ depth N + 1`. -/
@[ega "0 16.4.6" "(ii)", sga "2 XII 3.4" "partial"]
theorem depth_self_le_depth_quotSMulTop_succ {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {r : R} (hr : IsSMulRegular R r) (hrm : r ∈ IsLocalRing.maximalIdeal R) :
    Module.depthSup R (IsLocalRing.maximalIdeal R) R ≤
      Module.depthSup R (IsLocalRing.maximalIdeal R) (QuotSMulTop r R) + 1 := by
  -- Assembly of the iteration (`exists_isRegular_cons_head_length_of_le_depth`) and
  -- `isRegular_cons_iff`.
  classical
  set m := IsLocalRing.maximalIdeal R with hm
  set N := QuotSMulTop r R with hN
  -- depth R ≠ ⊤ (lengths bounded by supportDim R = ringKrullDim R; see `depth_self_ne_top`).
  have hdepthR_fin : Module.depthSup R m R ≠ ⊤ := depth_self_ne_top
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hdepthR_fin
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- d = 0: goal trivial
    rw [← hd, hd0]; simp
  · -- 1 ≤ d ≤ depth R; build r :: us of length d
    have hk : (d : ℕ∞) ≤ Module.depthSup R m R := by rw [← hd]
    obtain ⟨us, husmem, husreg, huslen⟩ :=
      exists_isRegular_cons_head_length_of_le_depth hr hrm d hdpos hk
    -- peel r: us is N-regular in m
    rw [RingTheory.Sequence.isRegular_cons_iff] at husreg
    obtain ⟨_, husNreg⟩ := husreg
    -- us.length = d - 1, so us.length + 1 = d
    have huslen2 : us.length + 1 = d := by simpa using huslen
    -- ↑us.length ≤ depth N
    have hle : (us.length : ℕ∞) ≤ Module.depthSup R m N := by
      rw [Module.depthSup]
      exact le_sSup ⟨us, rfl, husmem, husNreg⟩
    -- assemble: depth R = ↑d = ↑(us.length + 1) = ↑us.length + 1 ≤ depth N + 1
    rw [← hd, ← huslen2]
    push_cast
    gcongr

/-- **The Stacks 00LK exchange: prescribing the head of a maximal regular sequence.**
If `ss` is a *maximal* `R`-regular sequence in `m_R` (length equal to
`Module.depthSup R m_R R`) and `r ∈ m_R` is `R`-regular, then there is an `R`-regular
sequence in `m_R` of the same length whose head is `r`.

INFORMAL PROOF.  Let `N = QuotSMulTop r R`.  The two depth-drop inequalities
`depth_quotSMulTop_succ_le_depth` and `depth_self_le_depth_quotSMulTop_succ` give
`depth N + 1 = depth R`.  Since
`ss.length = depth R` is finite, `depth R ≠ ⊤`, so `depth N ≠ ⊤`.  Depth attainment
for `N` (`exists_isRegular_length_eq_depth_of_depth_ne_top`) gives an `N`-regular
sequence `us` in `m_R` of length `depth N`.  Then `isRegular_cons_iff` with `⟨hr, hus⟩`
makes `r :: us` an `R`-regular sequence in `m_R`, with all entries in `m_R` (`r ∈ m_R`
by `hrm`, the rest by `us`), and `(r :: us).length = depth N + 1 = depth R = ss.length`.
Take `ts' := us`.  No Cohen–Macaulay hypothesis is used. -/
theorem exists_isRegular_cons_head_of_maximal {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {ss : List R}
    (hssmax : (ss.length : ℕ∞) = Module.depthSup R (IsLocalRing.maximalIdeal R) R) {r : R}
    (hr : IsSMulRegular R r) (hrm : r ∈ IsLocalRing.maximalIdeal R) :
    ∃ ts' : List R,
      (∀ x ∈ ts', x ∈ IsLocalRing.maximalIdeal R) ∧
        RingTheory.Sequence.IsRegular R (r :: ts') ∧ (r :: ts').length = ss.length := by
  -- Assembly of the two depth-drop inequalities and depth attainment for N.
  classical
  set m := IsLocalRing.maximalIdeal R with hm
  set N := QuotSMulTop r R with hN
  -- `N` is a finite `R`-module and nontrivial (`r ∈ m_R` is a non-unit, so `r • ⊤ ≠ ⊤`).
  -- (`QuotSMulTop r R = R ⧸ r • ⊤`; nontriviality follows because `r` is a non-unit.)
  -- The two depth-drop inequalities: depth N + 1 = depth R.
  have hL1 : Module.depthSup R m N + 1 ≤ Module.depthSup R m R :=
    depth_quotSMulTop_succ_le_depth hr hrm
  have hL2 : Module.depthSup R m R ≤ Module.depthSup R m N + 1 :=
    depth_self_le_depth_quotSMulTop_succ hr hrm
  have hdrop : Module.depthSup R m N + 1 = Module.depthSup R m R := le_antisymm hL1 hL2
  -- depth R = ss.length is finite, hence depth N ≠ ⊤.
  have hdepthR_fin : Module.depthSup R m R ≠ ⊤ := by
    rw [← hssmax]; exact ENat.natCast_ne_top _
  have hdepthN_fin : Module.depthSup R m N ≠ ⊤ := by
    intro htop
    rw [htop] at hdrop
    simp at hdrop
    exact hdepthR_fin hdrop.symm
  -- `N` nontrivial: needed for depth attainment.  `N = QuotSMulTop r R` with `r ∈ m_R`
  -- a non-unit, so `r • ⊤ ≠ ⊤`, hence `N ≠ 0`.
  have hNnt : Nontrivial N := nontrivial_quotSMulTop_of_mem_maximalIdeal R hrm
  -- depth attainment for N: an N-regular sequence `us` in m of length depth N.
  obtain ⟨us, husmem, husreg, huslen⟩ :=
    exists_isRegular_length_eq_depth_of_depth_ne_top (M := N) hdepthN_fin
  -- Assemble `r :: us`.
  refine ⟨us, husmem, ?_, ?_⟩
  · -- `IsRegular R (r :: us)` via `isRegular_cons_iff ⟨hr, husreg⟩`.
    rw [RingTheory.Sequence.isRegular_cons_iff]
    exact ⟨hr, husreg⟩
  · -- Length: `(r :: us).length = us.length + 1`; `↑us.length = depth N`;
    -- `depth N + 1 = depth R = ss.length` (as ℕ∞ then ℕ).
    have hlen_enat : ((r :: us).length : ℕ∞) = (ss.length : ℕ∞) := by
      rw [List.length_cons, Nat.cast_add, Nat.cast_one, huslen, hdrop, ← hssmax]
    exact_mod_cast hlen_enat

/-- **Snoc characterization of regular sequences.**
Appending `a` to a regular sequence `rs` keeps it regular iff `[a]` is a regular
sequence on the iterated quotient `R ⧸ ofList rs • ⊤`.

On properness: the second conjunct must be `IsRegular (R ⧸ ofList rs • ⊤) [a]`, **not** the bare
`IsSMulRegular (R ⧸ ofList rs • ⊤) a`.  `RingTheory.Sequence.IsRegular` carries the
properness field `⊤ ≠ ofList _ • ⊤`; with only `IsSMulRegular` on the RHS the iff
fails (e.g. `R = ℤ, rs = [], a = 1`: RHS holds but `IsRegular ℤ [1]` is false since
`ofList [1] = ⊤`).  Using `IsRegular (R ⧸ ofList rs • ⊤) [a]` restores the
appended-ideal properness on both sides (note `ofList [a] • ⊤ ≠ ⊤` in the quotient
`R ⧸ ofList rs • ⊤` is equivalent to `ofList (rs ++ [a]) • ⊤ ≠ ⊤` in `R`).

INFORMAL PROOF.  Induction on `rs` using `RingTheory.Sequence.isRegular_cons_iff`
and the module identification `R ⧸ ofList (b :: bs) • ⊤ ≅ (QuotSMulTop b R) ⧸ ofList bs • ⊤`.
No depth or Cohen–Macaulayness is involved. -/
theorem isRegular_snoc_iff {R : Type*} [CommRing R] (rs : List R) (a : R) :
    RingTheory.Sequence.IsRegular R (rs ++ [a]) ↔
      RingTheory.Sequence.IsRegular R rs ∧
        RingTheory.Sequence.IsRegular (R ⧸ Ideal.ofList rs • (⊤ : Submodule R R)) [a] :=
  isRegular_snoc_iff_mod (M := R) rs a

/-- **CM ⇒ maximal regular sequence of length `dim R` with prescribed head `r`**
(Stacks 00LK).  In a Noetherian Cohen–Macaulay local ring `R`,
every regular element `r ∈ m_R` is the head of an `R`-regular sequence in `m_R`
whose total length equals `ringKrullDim R`.

*Proof.*  Depth attainment
(`exists_isRegular_length_eq_depth_of_cohenMacaulay`) produces an `R`-regular
sequence `ss` in `m_R` with `ss.length = depth R m_R R`.  The exchange
(`exists_isRegular_cons_head_of_maximal`, Stacks 00LK) turns `ss` into a regular
sequence `r :: ts'` of the same length with head `r`.  Finally CM evaluates the
length: `depth R m_R R = supportDim R R = ringKrullDim R`
(`IsCohenMacaulayLocalRing` unfolding + `supportDim_self_eq_ringKrullDim`). -/
@[ega "0 16.5.9" "special case"]
theorem exists_isRegular_cons_length_eq_ringKrullDim_of_cohenMacaulay {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (hCM : IsCohenMacaulayLocalRing R) {r : R}
    (hr : IsSMulRegular R r) (hrm : r ∈ IsLocalRing.maximalIdeal R) :
    ∃ ts : List R,
      (∀ x ∈ ts, x ∈ IsLocalRing.maximalIdeal R) ∧
        RingTheory.Sequence.IsRegular R (r :: ts) ∧
        ((r :: ts).length : WithBot ℕ∞) = ringKrullDim R := by
  -- Assembly of depth attainment, the exchange and the CM length evaluation.
  -- Depth attainment: an `R`-regular sequence `ss` in `m_R` of length `depth R m_R R`.
  obtain ⟨ss, _, _, hsslen⟩ := exists_isRegular_length_eq_depth_of_cohenMacaulay hCM
  -- The exchange (Stacks 00LK): prescribe `r` as head, same length.
  obtain ⟨ts', hts'mem, hts'reg, hts'len⟩ := exists_isRegular_cons_head_of_maximal hsslen hr hrm
  refine ⟨ts', hts'mem, hts'reg, ?_⟩
  -- Length evaluation: `(r :: ts').length = ss.length` (Nat), `(ss.length : ℕ∞) =
  -- depth R m_R R`, and CM gives `depth R m_R R = supportDim R R = ringKrullDim R`.
  have hsd : Module.supportDim R R = ringKrullDim R := Module.supportDim_self_eq_ringKrullDim R
  rw [Module.supportDim] at hsd
  unfold IsCohenMacaulayLocalRing IsCohenMacaulayModule at hCM
  rw [← hsd, ← hCM, ← hsslen, hts'len]
  rfl

/-- If `R` is a Noetherian Cohen–Macaulay local ring and `r` is a nonzerodivisor in the maximal
ideal, then `QuotSMulTop r R` admits a regular sequence in the maximal ideal whose length is at
least the support dimension of `QuotSMulTop r R`. Take the length-`d` regular sequence `r :: ts`
from `exists_isRegular_cons_length_eq_ringKrullDim_of_cohenMacaulay`, peel `r` off with
`isRegular_cons_iff` to get the `N`-regular tail `ts`, and compare lengths via
`supportDim_quotSMulTop_succ_eq_supportDim` / `supportDim_self_eq_ringKrullDim`. -/
theorem exists_isRegular_quotSMulTop_length_ge_supportDim_of_cohenMacaulay {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (hCM : IsCohenMacaulayLocalRing R) {r : R}
    (hr : IsSMulRegular R r) (hrm : r ∈ IsLocalRing.maximalIdeal R) :
    ∃ rs : List R,
      (∀ x ∈ rs, x ∈ IsLocalRing.maximalIdeal R) ∧
        RingTheory.Sequence.IsRegular (QuotSMulTop r R) rs ∧
        Module.supportDim R (QuotSMulTop r R) ≤ (↑rs.length : WithBot ℕ∞) := by
  -- Assembly: obtain the length-`d` regular sequence `r :: ts`, peel `r`.
  obtain ⟨ts, htsmem, htsreg, htslen⟩ :=
    exists_isRegular_cons_length_eq_ringKrullDim_of_cohenMacaulay hCM hr hrm
  -- Peel `r` off `r :: ts` to expose the `N = QuotSMulTop r R`-regular tail `ts`.
  rw [RingTheory.Sequence.isRegular_cons_iff] at htsreg
  obtain ⟨_, htail⟩ := htsreg
  refine ⟨ts, htsmem, htail, ?_⟩
  -- Length comparison: `supportDim N + 1 = ringKrullDim R = (r :: ts).length = ts.length + 1`.
  have hsuppN : Module.supportDim R (QuotSMulTop r R) + 1 = Module.supportDim R R := by
    simpa using Module.supportDim_quotSMulTop_succ_eq_supportDim (R := R) (M := R) hr hrm
  have hself : Module.supportDim R R = ringKrullDim R := Module.supportDim_self_eq_ringKrullDim R
  -- From `htslen : ((r :: ts).length : WithBot ℕ∞) = ringKrullDim R` and the two
  -- equalities above, cancel the `+1` to get `supportDim N = ↑ts.length`, hence `≤`.
  have hlen_eq : Module.supportDim R (QuotSMulTop r R) = (↑ts.length : WithBot ℕ∞) := by
    have hcons : ((r :: ts).length : WithBot ℕ∞) = (↑ts.length : WithBot ℕ∞) + 1 := by
      push_cast [List.length_cons]; ring
    have hsumeq : Module.supportDim R (QuotSMulTop r R) + 1 = (↑ts.length : WithBot ℕ∞) + 1 := by
      rw [hsuppN, hself, ← htslen, hcons]
    exact ENat.WithBot.add_natCast_cancel.mp hsumeq
  rw [hlen_eq]

/-- For a Cohen-Macaulay local ring `R` and a regular element `r` of the maximal ideal, the
dimension of the support of `R ⧸ rR` is at most its depth. -/
theorem supportDim_le_depth_quotSMulTop_of_cohenMacaulay {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (hCM : IsCohenMacaulayLocalRing R) {r : R}
    (hr : IsSMulRegular R r) (hrm : r ∈ IsLocalRing.maximalIdeal R) :
    Module.supportDim R (QuotSMulTop r R) ≤
      (↑(Module.depthSup R (IsLocalRing.maximalIdeal R) (QuotSMulTop r R)) : WithBot ℕ∞) := by
  -- Obtain the `N`-regular sequence of
  -- `exists_isRegular_quotSMulTop_length_ge_supportDim_of_cohenMacaulay`, then `le_sSup`
  -- into the depth index set gives `↑rs.length ≤ depth R m_R N`; chain with
  -- `supportDim R N ≤ ↑rs.length`.
  obtain ⟨rs, hmem, hreg, hlen⟩ :=
    exists_isRegular_quotSMulTop_length_ge_supportDim_of_cohenMacaulay hCM hr hrm
  have hle :
    (↑rs.length : ℕ∞) ≤ Module.depthSup R (IsLocalRing.maximalIdeal R) (QuotSMulTop r R) := by
    rw [Module.depthSup]
    exact le_sSup ⟨rs, rfl, hmem, hreg⟩
  exact hlen.trans (by exact_mod_cast hle)

/-- For `r : R`, `r • ⊤` is the principal ideal `span {r}`. -/
private theorem smul_top_eq_span_singleton {R : Type*} [CommRing R] (r : R) :
    open Pointwise in r • (⊤ : Submodule R R) = Ideal.span {r} := by
  rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]

/-- The `R ⧸ span {r}`-linear equivalence `QuotSMulTop r R ≃ R ⧸ span {r}`. -/
private def quotSMulTopEquivQuotSpan {R : Type*} [CommRing R] (r : R) :
    QuotSMulTop r R ≃ₗ[R ⧸ Ideal.span {r}] R ⧸ Ideal.span {r} :=
  { Submodule.quotEquivOfEq _ _ (smul_top_eq_span_singleton r) with
    map_smul' := by
      rintro c x
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      induction x using Quotient.inductionOn' with
      | _ x =>
        simp only [RingHom.id_apply]; rfl }

/-- Regularity of a sequence on `QuotSMulTop r R` is unchanged by pushing it along
`R → R ⧸ span {r}`. -/
private theorem isRegular_map_algebraMap_quotSMulTop_iff {R : Type*} [CommRing R] (r : R)
    (rs : List R) :
    RingTheory.Sequence.IsRegular (QuotSMulTop r R)
        (rs.map (algebraMap R (R ⧸ Ideal.span {r}))) ↔
      RingTheory.Sequence.IsRegular (QuotSMulTop r R) rs := by
  set S := R ⧸ Ideal.span {r}
  set M := QuotSMulTop r R
  have hcarrier :
    ∀ (J : Ideal R) (x : M),
      x ∈ (Ideal.map (algebraMap R S) J) • (⊤ : Submodule S M) ↔
        x ∈ J • (⊤ : Submodule R M) := by
    intro J x
    have hclosed :
      ∀ (c : S) (y : M), y ∈ J • (⊤ : Submodule R M) → c • y ∈ J • (⊤ : Submodule R M) := by
      intro c y hy
      refine Submodule.smul_induction_on hy ?_ ?_
      · intro a ha n _; rw [smul_comm]; exact Submodule.smul_mem_smul ha Submodule.mem_top
      · intro p q hp hq; rw [smul_add]; exact Submodule.add_mem _ hp hq
    constructor
    · intro hx
      refine Submodule.smul_induction_on hx ?_ (fun a b ha hb => Submodule.add_mem _ ha hb)
      intro s hs m _
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hs
      · rintro y ⟨a, ha, rfl⟩; rw [algebraMap_smul]
        exact Submodule.smul_mem_smul ha Submodule.mem_top
      · simp
      · intro a b _ _ ha hb; rw [add_smul]; exact Submodule.add_mem _ ha hb
      · intro c a _ hca; rw [smul_assoc]; exact hclosed c _ hca
    · intro hx
      refine Submodule.smul_induction_on hx ?_ (fun a b ha hb => Submodule.add_mem _ ha hb)
      intro s hs m _
      rw [← algebraMap_smul S s m]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hs) Submodule.mem_top
  rw [RingTheory.Sequence.isRegular_iff, RingTheory.Sequence.isRegular_iff,
    RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff]
  refine and_congr_right fun _ => not_congr ?_
  rw [← Ideal.map_ofList]
  simp only [Submodule.ext_iff, Submodule.mem_top, true_iff]
  exact forall_congr' (hcarrier _)

open Pointwise in
/-- **Base change: Cohen–Macaulayness of `R ⧸ span{r}` as `depth = supportDim` over `R`**
(Stacks 00LF, restriction-of-scalars bookkeeping).  For `r ∈ m_R`, the ring
`R ⧸ span{r}` is Cohen–Macaulay iff the depth (along `m_R`) and support dimension of
the `R`-module `N = QuotSMulTop r R` agree.

INFORMAL PROOF.  Let `π : R → R ⧸ span{r}` be the quotient map and
`N = QuotSMulTop r R = R ⧸ (r • ⊤)`; since `r • (⊤ : Submodule R R) = span{r}`,
`N ≅ R ⧸ span{r}` as `R`-modules.  `IsCohenMacaulayLocalRing (R ⧸ span{r})` unfolds
(via `isCohenMacaulayLocalRing_iff_isCohenMacaulayModule_self`) to
`↑(depth (R⧸span{r}) m_{R⧸span{r}} (R⧸span{r})) = supportDim (R⧸span{r}) (R⧸span{r})`.
Restriction of scalars along the surjection `π` matches:
* `depth (R⧸span{r}) m_{R⧸span{r}} (R⧸span{r}) = depth R m_R N` — the index sets of
  regular sequences correspond by lifting along `π` (`m_{R⧸span{r}} = π(m_R)`, and the
  `R`- and `R⧸span{r}`-actions on any `R⧸span{r}`-module agree);
* `supportDim (R⧸span{r}) (R⧸span{r}) = supportDim R N` — `Module.support` over the
  quotient ring corresponds to the closed subset of `Spec R` of primes containing
  `span{r}`, an order isomorphism preserving Krull dimension.
Cite: `isCohenMacaulayLocalRing_iff_isCohenMacaulayModule_self`,
`Module.supportDim_self_eq_ringKrullDim`, `RingTheory.Sequence.isRegular_cons_iff`,
restriction-of-scalars support/depth compatibility. -/
@[ega "IV 5.7.10" "special case"]
theorem cohenMacaulay_quot_iff_depth_eq_supportDim {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {r : R} (hrm : r ∈ IsLocalRing.maximalIdeal R)
    [IsLocalRing (R ⧸ Ideal.span {r})] :
    IsCohenMacaulayLocalRing (R ⧸ Ideal.span {r}) ↔
      (↑(Module.depthSup R (IsLocalRing.maximalIdeal R) (QuotSMulTop r R)) : WithBot ℕ∞) =
        Module.supportDim R (QuotSMulTop r R) := by
  classical
  -- Membership in the maximal ideal of `R/span{r}` lifts/descends along `π`.
  have mem_max_iff :
    ∀ (x : R),
      Ideal.Quotient.mk (Ideal.span {r}) x ∈ IsLocalRing.maximalIdeal (R ⧸ Ideal.span {r}) ↔
        x ∈ IsLocalRing.maximalIdeal R := by
    intro x
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk _)
      Ideal.Quotient.mk_surjective]
    exact Ideal.mem_quotient_iff_mem (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hrm))
  -- DEPTH transport: `depth (R/span{r}) m_{R/span{r}} (R/span{r}) = depth R m_R N`.
  have hdepth :
    Module.depthSup (R ⧸ Ideal.span {r}) (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {r}))
        (R ⧸ Ideal.span {r}) =
      Module.depthSup R (IsLocalRing.maximalIdeal R) (QuotSMulTop r R) := by
    -- Step A: replace `R/span{r}` by `N` via `quotSMulTopEquivQuotSpan r`.
    have hA :
      Module.depthSup (R ⧸ Ideal.span {r}) (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {r}))
          (R ⧸ Ideal.span {r}) =
        Module.depthSup (R ⧸ Ideal.span {r}) (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {r}))
          (QuotSMulTop r R) := by
      simp_rw [Module.depthSup, ← LinearEquiv.isRegular_congr (quotSMulTopEquivQuotSpan r)]
    -- Step B: transport from `R/span{r}`-scalars to `R`-scalars on the module `N`.
    have hB :
      Module.depthSup (R ⧸ Ideal.span {r}) (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {r}))
          (QuotSMulTop r R) =
        Module.depthSup R (IsLocalRing.maximalIdeal R) (QuotSMulTop r R) := by
      rw [Module.depthSup, Module.depthSup]
      congr 1
      ext n
      constructor
      · rintro ⟨ss, hlen, hmem, hreg⟩
        choose lift hlift using fun (y : R ⧸ Ideal.span {r}) => Ideal.Quotient.mk_surjective y
        refine ⟨ss.map lift, ?_, ?_, ?_⟩
        · simpa using hlen
        · intro x hx
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          rw [← mem_max_iff, hlift y]
          exact hmem y hy
        · have hmap : (ss.map lift).map (algebraMap R (R ⧸ Ideal.span {r})) = ss := by
            simp [Function.comp_def, Ideal.Quotient.algebraMap_eq, hlift]
          rwa [← isRegular_map_algebraMap_quotSMulTop_iff r, hmap]
      · rintro ⟨rs, hlen, hmem, hreg⟩
        refine ⟨rs.map (algebraMap R (R ⧸ Ideal.span {r})), ?_, ?_, ?_⟩
        · simpa using hlen
        · intro y hy
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
          rw [Ideal.Quotient.algebraMap_eq, mem_max_iff]
          exact hmem x hx
        · rwa [isRegular_map_algebraMap_quotSMulTop_iff r]
    rw [hA, hB]
  -- SUPPORT transport: `supportDim R N = supportDim (R/span{r}) (R/span{r})`.
  have hsupp :
    Module.supportDim R (QuotSMulTop r R) =
      Module.supportDim (R ⧸ Ideal.span {r}) (R ⧸ Ideal.span {r}) := by
    have hann : Module.annihilator R (QuotSMulTop r R) = Ideal.span {r} := by
      change Module.annihilator R (R ⧸ (r • (⊤ : Submodule R R))) = Ideal.span {r}
      rw [smul_top_eq_span_singleton, Ideal.annihilator_quotient]
    rw [Module.supportDim_self_eq_ringKrullDim, ringKrullDim_quotient]
    change Order.krullDim ↑(Module.support R (QuotSMulTop r R)) = _
    rw [Module.support_eq_zeroLocus, hann]
  -- Assemble: unfold CM and rewrite both invariants.
  rw [isCohenMacaulayLocalRing_iff_isCohenMacaulayModule_self, IsCohenMacaulayModule, hdepth, ←
    Module.supportDim, hsupp]

/-- The quotient of a Cohen-Macaulay local ring by a regular element of its maximal ideal is
again a Cohen-Macaulay local ring. -/
@[ega "0 16.4.10" "(i), special case", ega "0 16.5.5" "special case", ega "0 16.5.6" "special case"]
theorem cohenMacaulay_quotient_span_singleton_of_isSMulRegular {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (hCM : IsCohenMacaulayLocalRing R) {r : R}
    (hr : IsSMulRegular R r) (hrm : r ∈ IsLocalRing.maximalIdeal R)
    [IsLocalRing (R ⧸ Ideal.span {r})] : IsCohenMacaulayLocalRing (R ⧸ Ideal.span {r}) := by
  -- Reduce to `depth = supportDim` for the R-module `N = QuotSMulTop r R` (base change),
  -- then prove equality by antisymmetry: `depth ≤ supportDim` (general, 00LK) and
  -- `supportDim ≤ depth` (the CM manufacturing direction, 00LF/00N6).
  rw [cohenMacaulay_quot_iff_depth_eq_supportDim hrm]
  exact
    le_antisymm (depth_le_supportDim_self_quot hrm)
      (supportDim_le_depth_quotSMulTop_of_cohenMacaulay hCM hr hrm)

open scoped Pointwise in
/-- **Inductive engine for Stacks 06LC.**
For every `d`, every Noetherian Cohen–Macaulay local ring `B` of dimension `d`
admitting a ring hom `φ : A →+* B` with `m_B = sqrt(φ(m_A) B)` has a list
`f : List A` of length `d` whose `φ`-images form a regular sequence in `B`.
`B` (and `A`, `φ`) are quantified *inside*, so the IH at `d = n` can be applied
to the quotient ring `B ⧸ span{φ f₀}`.

INFORMAL PROOF (induction on `d`).
* **Base `d = 0`.**  Take `f = []`.  `[].length = 0`, and
  `RingTheory.Sequence.IsRegular B []` holds because `B` is nontrivial
  (`RingTheory.Sequence.IsRegular.nil`; `B` is a nonzero local ring).

* **Step `d = n + 1`.**  Apply `exists_mem_maximalIdeal_isSMulRegular_map` to get
  `f₀ ∈ m_A` with `φ f₀ ∈ m_B` a non-zero-divisor, `IsSMulRegular B (φ f₀)`.
  Let `B' = B ⧸ span{φ f₀}` (equivalently the module `QuotSMulTop (φ f₀) B`).
  Then:
  - `B'` is Noetherian (quotient of a Noetherian ring);
  - `B'` is local: `φ f₀ ∈ m_B` makes `span{φ f₀}` a proper ideal contained in
    `m_B`, so the quotient is local with maximal ideal the image of `m_B`;
  - `B'` is Cohen–Macaulay of dimension `n`: cutting a CM ring by a single
    non-zero-divisor in the maximal ideal drops both depth and dimension by one
    and preserves CM (the dimension drop is `ringKrullDim B ≤ ringKrullDim B' +1`
    from `ringKrullDim_le_ringKrullDim_quotSMulTop_succ` together with the
    reverse inequality for a non-zero-divisor, pinning `dim B' = n`);
  - the radical hypothesis is inherited by the composite
    `A →φ B →(quot) B'`: `m_{B'}` is the image of `m_B = sqrt(φ(m_A)B)`, which is
    `sqrt((quot∘φ)(m_A) B')`.
  By the induction hypothesis (`d = n`) applied to `B'` and the composite map,
  there is `f : List A` with `f.length = n` and
  `RingTheory.Sequence.IsRegular B' (f.map (quot∘φ))`.  Then `f₀ :: f` works:
  its length is `n + 1`, and by `isRegular_cons_iff`,
  `IsRegular B ((φ f₀) :: (f.map φ))` follows from `IsSMulRegular B (φ f₀)`
  (first conjunct) and `IsRegular (QuotSMulTop (φ f₀) B) (f.map φ)` (second
  conjunct), the latter being exactly the IH output transported across the
  identification `QuotSMulTop (φ f₀) B ≃ B'` of `B`-modules. -/
@[ega "0 16.5.9" "special case"]
theorem exists_list_isRegular_map_of_ringKrullDim_eq (d : ℕ) :
    ∀ {A : Type*} {B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
      [IsNoetherianRing B],
      IsCohenMacaulayLocalRing B →
        ∀ (φ : A →+* B),
          IsLocalRing.maximalIdeal B = (Ideal.map φ (IsLocalRing.maximalIdeal A)).radical →
            ringKrullDim B = (d : WithBot ℕ∞) →
            ∃ f : List A, f.length = d ∧ RingTheory.Sequence.IsRegular B (f.map φ) := by
  induction d with
  | zero =>
    intro A B _ _ _ _ _ hCM φ h hdim
    -- Base case: `f = []`.  Length 0 = d.  `IsRegular B []` from nontriviality
    -- (B is nontrivial as a local ring).
    refine ⟨[], rfl, ?_⟩
    simpa using RingTheory.Sequence.IsRegular.nil B B
  | succ n ih =>
    intro A B _ _ _ _ _ hCM φ h hdim
    -- Inductive step.  Produce the regular image `f₀`.
    obtain ⟨f₀, hf₀mA, hf₀mB, hf₀reg⟩ := exists_mem_maximalIdeal_isSMulRegular_map hCM φ h n hdim
    -- `φ f₀` is a non-zero-divisor on `B`.
    have hf₀nzd : φ f₀ ∈ nonZeroDivisors B := by
      rw [mem_nonZeroDivisors_iff]
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · apply hf₀reg; simpa [smul_eq_mul] using hx
      · apply hf₀reg; simp only [smul_eq_mul, mul_zero]; rw [mul_comm]; exact hx
    -- The quotient ring `B' = B ⧸ span{φ f₀}`.
    set I : Ideal B := Ideal.span {φ f₀} with hI
    -- `span{φ f₀}` is a proper ideal (it is contained in `m_B` since `φ f₀ ∈ m_B`).
    have hIproper : I ≠ ⊤ :=
      -- `span {φ f₀} ≤ m_B ≠ ⊤`.
      ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal B).ne_top
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hf₀mB))
    -- `B'` is nontrivial, hence local (quotient of a local ring by a proper ideal).
    have hnt : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIproper
    have hlocal : IsLocalRing (B ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    -- `B'` is Cohen–Macaulay (cutting by the regular element `φ f₀ ∈ m_B`).
    have hCM' : IsCohenMacaulayLocalRing (B ⧸ I) :=
      -- `I` is `Ideal.span {φ f₀}` definitionally; supply the local instance `hlocal`.
      cohenMacaulay_quotient_span_singleton_of_isSMulRegular (R := B) hCM hf₀reg hf₀mB
    -- `ringKrullDim B' = n` (dimension drops by exactly one).
    have hdim' : ringKrullDim (B ⧸ I) = (n : WithBot ℕ∞) := by
      -- Combine the two dimension inequalities and cancel `+1`.
      have hle2 : ringKrullDim B ≤ ringKrullDim (B ⧸ I) + 1 := by
        have := ringKrullDim_le_ringKrullDim_quotSMulTop_succ (R := B) hf₀mB
        rwa [smul_top_eq_span_singleton] at this
      have heq : ringKrullDim (B ⧸ I) + 1 = ringKrullDim B :=
        le_antisymm (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hf₀nzd) hle2
      rw [hdim] at heq
      -- heq : ringKrullDim (B ⧸ I) + 1 = ↑(n+1).  Cancel `+1`.
      have hcast :
        ringKrullDim (B ⧸ I) + ((1 : ℕ) : WithBot ℕ∞) =
          (n : WithBot ℕ∞) + ((1 : ℕ) : WithBot ℕ∞) := by
        have h1 : ((1 : ℕ) : WithBot ℕ∞) = (1 : WithBot ℕ∞) := by
          push_cast; ring
        rw [h1, heq]; push_cast; ring
      exact ENat.WithBot.add_natCast_cancel.mp hcast
    -- The radical hypothesis is inherited by the composite `A → B → B'`.
    have hrad' :
      IsLocalRing.maximalIdeal (B ⧸ I) =
        (Ideal.map ((Ideal.Quotient.mk I).comp φ) (IsLocalRing.maximalIdeal A)).radical := by
      -- `ψ := Ideal.Quotient.mk I` is surjective.
      have hψsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
      -- `I ≤ map φ m_A` since `φ f₀ ∈ map φ m_A`.
      have hIle : I ≤ Ideal.map φ (IsLocalRing.maximalIdeal A) := by
        rw [hI, Ideal.span_le, Set.singleton_subset_iff]
        exact Ideal.mem_map_of_mem φ hf₀mA
      -- `m_{B⧸I} = map ψ m_B`, then push the radical through `ψ`, whose kernel `I` lies in
      -- `map φ m_A`.
      rw [← IsLocalRing.map_maximalIdeal_of_surjective _ hψsurj, h,
        Ideal.map_radical_of_surjective hψsurj (Ideal.mk_ker.trans_le hIle), Ideal.map_map]
    -- Apply the induction hypothesis to `B'` and the composite map.
    obtain ⟨g, hglen, hgreg⟩ := ih (B := B ⧸ I) hCM' ((Ideal.Quotient.mk I).comp φ) hrad' hdim'
    -- Assemble `f₀ :: g`.
    refine ⟨f₀ :: g, by simp [hglen], ?_⟩
    -- `(f₀ :: g).map φ = φ f₀ :: g.map φ`; use
    -- `isRegular_cons_iff` to split into `IsSMulRegular B (φ f₀)` (= `hf₀reg`) and
    -- `IsRegular (QuotSMulTop (φ f₀) B) (g.map φ)`, the latter being `hgreg`
    -- transported across `QuotSMulTop (φ f₀) B ≃ₗ B ⧸ span{φ f₀}` and
    -- `g.map ((mk I).comp φ) = (g.map φ).map (mk I)`.
    rw [List.map_cons, RingTheory.Sequence.isRegular_cons_iff]
    refine ⟨hf₀reg, ?_⟩
    -- Convert `hgreg` (over `B⧸I`) to a statement over `QuotSMulTop (φ f₀) B`.
    have hmapeq : g.map ((Ideal.Quotient.mk I).comp φ) = (g.map φ).map (algebraMap B (B ⧸ I)) := by
      rw [List.map_map]; rfl
    rw [hmapeq] at hgreg
    have hcongr :=
      (LinearEquiv.isRegular_congr (quotSMulTopEquivQuotSpan (φ f₀)) _).mpr hgreg
    exact (isRegular_map_algebraMap_quotSMulTop_iff (φ f₀) (g.map φ)).mp hcongr

-- needed: `exists_isRegular_map_length_eq_ringKrullDim` cannot synthesize `Decidable ¬0 ≤ none` in
-- `ℕ∞` unless the instance is unfolded at `default` transparency
set_option backward.isDefEq.respectTransparency false in
/-- The main theorem (Stacks Tag 06LC).  Reduce to the engine lemma at `d` the finite value
of `ringKrullDim B`. -/
@[stacks 06LC]
theorem exists_isRegular_map_length_eq_ringKrullDim {A B : Type*} [CommRing A] [CommRing B]
  [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing B] (hCM : IsCohenMacaulayLocalRing B) (φ : A →+* B)
    (h : IsLocalRing.maximalIdeal B = (Ideal.map φ (IsLocalRing.maximalIdeal A)).radical) :
    ∃ f : List A,
      (f.length : WithBot ℕ∞) = ringKrullDim B ∧ RingTheory.Sequence.IsRegular B (f.map φ) := by
  -- `B` is a nonzero Noetherian local ring, so `ringKrullDim B` is a finite
  -- natural number: `ringKrullDim B ≠ ⊤` (`ringKrullDim_ne_top`) and
  -- `0 ≤ ringKrullDim B`, so there is `d : ℕ` with `ringKrullDim B = d`.
  -- Apply `exists_list_isRegular_map_of_ringKrullDim_eq d` to get `f : List A` with `f.length = d`
  -- and the regular-sequence property; then `(f.length : WithBot ℕ∞) = d = ringKrullDim B`.
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim B = (d : WithBot ℕ∞) := by
    have hne_top : ringKrullDim B ≠ ⊤ := ringKrullDim_ne_top
    have hnonneg : 0 ≤ ringKrullDim B := ringKrullDim_nonneg_of_nontrivial
    match hk : ringKrullDim B with
    | ⊥ =>
      rw [hk] at hnonneg
      exact absurd hnonneg (by decide)
    | (⊤ : ℕ∞) => exact absurd hk hne_top
    | ((n : ℕ) : ℕ∞) => exact ⟨n, rfl⟩
  obtain ⟨f, hlen, hreg⟩ := exists_list_isRegular_map_of_ringKrullDim_eq d hCM φ h hd
  exact ⟨f, by rw [hlen, hd], hreg⟩

end
