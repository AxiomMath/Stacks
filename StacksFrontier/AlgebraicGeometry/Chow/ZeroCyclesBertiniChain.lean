module

public import StacksFrontier.AlgebraicGeometry.Chow.ZeroCyclesBertiniCutStep

/-!
# The iterated Bertini cut in the proof of Stacks 0FH5

Iterating the Bertini step `Stacks.Chow.BertiniChain.exists_cut_step` `d` times produces
sections `s_1, …, s_d` of the linear system `V_n` of sections of `ℒ^{⊗ n}` vanishing on `Z` such
that, for every `j ≤ d`, the intersection `H_1 ∩ ⋯ ∩ H_j` is smooth over `k` off `Z` and its
points off `Z` have `δ`-dimension at most `d - j`, and each `s_{j+1}` vanishes at no generic point
of `H_1 ∩ ⋯ ∩ H_j` off `Z`. At each step any further property expressible by avoiding one proper
subspace of `V_n` may be imposed as well.

## Main results

* `Stacks.Chow.BertiniChain.familyCut_snoc`: `H_1 ∩ ⋯ ∩ H_{j+1} = (H_1 ∩ ⋯ ∩ H_j) ∩ H_{j+1}`.
* `Stacks.Chow.BertiniChain.exists_chain`: the iterated cut.

## References

* [Stacks Project, Tag 0FH5](https://stacks.math.columbia.edu/tag/0FH5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Stacks.Ample
open Stacks.SectionsVanishingOnSubscheme

universe u

namespace Stacks.Chow.BertiniChain

attribute [local instance] Stacks.SectionsVanishingOnSubscheme.isInvertible_of_isInvertibleModule

section Family

variable {X : Scheme.{u}} (M : X.Modules) [IsInvertibleModule X M]

/-- The intersection of the empty family of divisors is the whole scheme. -/
theorem familyCut_elim0 (s : Fin 0 → Γ(M, ⊤)) : familyCut M s = ⊥ := by
  rw [familyCut]
  exact iSup_of_empty _

/-- `H_1 ∩ ⋯ ∩ H_{j+1} = (H_1 ∩ ⋯ ∩ H_j) ∩ H_{j+1}`. -/
theorem familyCut_snoc {j : ℕ} (s : Fin j → Γ(M, ⊤)) (v : Γ(M, ⊤)) :
    familyCut M (Fin.snoc s v : Fin (j + 1) → Γ(M, ⊤)) =
      familyCut M s ⊔ Stacks.Divisors.zeroScheme X M v := by
  refine le_antisymm (iSup_le fun i => ?_) (sup_le (iSup_le fun i => ?_) ?_)
  · induction i using Fin.lastCases with
    | last => rw [Fin.snoc_last]; exact le_sup_right
    | cast i =>
      rw [Fin.snoc_castSucc]
      exact le_sup_of_le_left (le_iSup (fun l => Stacks.Divisors.zeroScheme X M (s l)) i)
  · refine le_iSup_of_le i.castSucc ?_
    rw [Fin.snoc_castSucc]
  · refine le_iSup_of_le (Fin.last j) ?_
    rw [Fin.snoc_last]

/-- The prefixes of `Fin.snoc s v` of length at most `j` are those of `s`. -/
theorem prefixFamily_snoc {α : Type*} {j : ℕ} (s : Fin j → α) (v : α) {i : ℕ} (hi : i ≤ j) :
    prefixFamily (Fin.snoc s v : Fin (j + 1) → α) i (hi.trans (Nat.le_succ j)) =
      prefixFamily s i hi :=
  funext fun l => Fin.snoc_castSucc (i := Fin.castLE hi l) ..

/-- The prefix of full length is the family itself. -/
theorem prefixFamily_self {α : Type*} {j : ℕ} (s : Fin j → α) :
    prefixFamily s j le_rfl = s :=
  rfl

end Family

variable {k : Type u} [Field k] [Infinite k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] [IsProper f] (I : X.IdealSheafData) (L : X.Modules)
    [IsInvertibleModule X L] (m : ℤ) [FiniteDimensional k (vanishingSections k f I L m)]

/-- The global sections underlying a family of members of `V_n`. -/
abbrev secs {j : ℕ} (s : Fin j → vanishingSections k f I L m) :
    Fin j → Γ(tensorPowModule X L m, ⊤) :=
  fun l => ((s l : Stacks.Bertini.globalSections k f (tensorPowModule X L m)) :
    Γ(tensorPowModule X L m, ⊤))

/-- The global section underlying a member of `V_n`. -/
abbrev sec (v : vanishingSections k f I L m) : Γ(tensorPowModule X L m, ⊤) :=
  ((v : Stacks.Bertini.globalSections k f (tensorPowModule X L m)) :
    Γ(tensorPowModule X L m, ⊤))

omit [Infinite k] [Smooth f] [IsProper f] [FiniteDimensional k (vanishingSections k f I L m)] in
/-- The sections underlying `Fin.snoc s v` are `Fin.snoc` of those underlying `s` and `v`. -/
theorem secs_snoc {j : ℕ} (s : Fin j → vanishingSections k f I L m)
    (v : vanishingSections k f I L m) :
    secs f I L m (Fin.snoc s v : Fin (j + 1) → _) =
      Fin.snoc (α := fun _ => Γ(tensorPowModule X L m, ⊤)) (secs f I L m s) (sec f I L m v) := by
  funext l
  induction l using Fin.lastCases with
  | last => rw [Fin.snoc_last]; exact congrArg (sec f I L m) (Fin.snoc_last _ _)
  | cast l => rw [Fin.snoc_castSucc]; exact congrArg (sec f I L m) (Fin.snoc_castSucc _ _ _)

omit [Infinite k] [Smooth f] [IsProper f] [FiniteDimensional k (vanishingSections k f I L m)] in
/-- The prefixes of length at most `j` of the sections underlying `Fin.snoc s v` are those of the
sections underlying `s`. -/
theorem prefixFamily_secs_snoc {j : ℕ} (s : Fin j → vanishingSections k f I L m)
    (v : vanishingSections k f I L m) {i : ℕ} (hi : i ≤ j) :
    prefixFamily (secs f I L m (Fin.snoc s v : Fin (j + 1) → _)) i (hi.trans (Nat.le_succ j)) =
      prefixFamily (secs f I L m s) i hi := by
  rw [secs_snoc]
  exact prefixFamily_snoc _ _ hi

omit [Infinite k] [Smooth f] [IsProper f] [FiniteDimensional k (vanishingSections k f I L m)] in
/-- The cut by the sections underlying `Fin.snoc s v` is the cut by those underlying `s`,
intersected with the zero scheme of `v`. -/
theorem familyCut_secs_snoc {j : ℕ} (s : Fin j → vanishingSections k f I L m)
    (v : vanishingSections k f I L m) :
    familyCut _ (secs f I L m (Fin.snoc s v : Fin (j + 1) → _)) =
      familyCut _ (secs f I L m s) ⊔
        Stacks.Divisors.zeroScheme X (tensorPowModule X L m) (sec f I L m v) := by
  rw [secs_snoc]
  exact familyCut_snoc _ _ _

omit [Infinite k] [Smooth f] [IsProper f] [FiniteDimensional k (vanishingSections k f I L m)] in
/-- For `i < j`, the `i`-th section underlying `Fin.snoc s v` is the `i`-th section underlying
`s`. -/
theorem secs_snoc_castSucc {j : ℕ} (s : Fin j → vanishingSections k f I L m)
    (v : vanishingSections k f I L m) (i : ℕ) (hi : i < j + 1) (hij : i < j) :
    secs f I L m (Fin.snoc s v : Fin (j + 1) → _) ⟨i, hi⟩ = secs f I L m s ⟨i, hij⟩ := by
  rw [secs_snoc, show (⟨i, hi⟩ : Fin (j + 1)) = (⟨i, hij⟩ : Fin j).castSucc from rfl,
    Fin.snoc_castSucc]

omit [Infinite k] [Smooth f] [IsProper f] [FiniteDimensional k (vanishingSections k f I L m)] in
/-- The last section underlying `Fin.snoc s v` is the section underlying `v`. -/
theorem secs_snoc_last {j : ℕ} (s : Fin j → vanishingSections k f I L m)
    (v : vanishingSections k f I L m) (hi : j < j + 1) :
    secs f I L m (Fin.snoc s v : Fin (j + 1) → _) ⟨j, hi⟩ = sec f I L m v := by
  rw [secs_snoc, show (⟨j, hi⟩ : Fin (j + 1)) = Fin.last j from rfl, Fin.snoc_last]

/-- **The iterated Bertini cut.** Over an infinite field, with `X` smooth and proper over `k`,
`V_n` generating `ℒ^{⊗ n}` off `Z` and `X ∖ Z → 𝐏(V_n)` an immersion in every basis, and with all
points of `X` off `Z` of `δ`-dimension at most `d`, there are `d` members of `V_n` such that for
every `j ≤ d` the cut `H_1 ∩ ⋯ ∩ H_j` is smooth over `k` off `Z` with points off `Z` of
`δ`-dimension at most `d - j`, and `s_{j+1}` does not vanish at its generic points off `Z`. An
additional property `Q` of the chosen prefixes is carried along, provided it can be kept at each
step by avoiding a proper subspace. -/
theorem exists_chain (h : GeneratesOffSupport k f I L m)
    (himm : ∀ (N : ℕ) (b : Module.Basis (Fin (N + 1)) k (vanishingSections k f I L m)),
      IsImmersion (toProjectiveSpaceOfVanishingSections k f b h))
    (d : ℕ) (hdim0 : DimBoundOff f I ⊥ d)
    (Q : ∀ j : ℕ, (Fin j → vanishingSections k f I L m) → Prop) (hQ0 : Q 0 Fin.elim0)
    (hQ : ∀ j < d, ∀ s, Q j s → ∃ P : Submodule k (vanishingSections k f I L m), P ≠ ⊤ ∧
      ∀ v ∉ P, Q (j + 1) (Fin.snoc s v)) :
    ∃ s : Fin d → vanishingSections k f I L m, Q d s ∧
      (∀ (j : ℕ) (hj : j ≤ d),
        SmoothOffSupport f I (familyCut _ (prefixFamily (secs f I L m s) j hj))) ∧
      (∀ (j : ℕ) (hj : j ≤ d),
        DimBoundOff f I (familyCut _ (prefixFamily (secs f I L m s) j hj)) ((d : ℤ) - j)) ∧
      (∀ (j : ℕ) (hj : j < d),
        NonvanishingAtGenericOff I (familyCut _ (prefixFamily (secs f I L m s) j hj.le))
          (tensorPowModule X L m) (secs f I L m s ⟨j, hj⟩)) := by
  suffices H : ∀ j ≤ d, ∃ s : Fin j → vanishingSections k f I L m, Q j s ∧
      (∀ (i : ℕ) (hi : i ≤ j),
        SmoothOffSupport f I (familyCut _ (prefixFamily (secs f I L m s) i hi))) ∧
      (∀ (i : ℕ) (hi : i ≤ j),
        DimBoundOff f I (familyCut _ (prefixFamily (secs f I L m s) i hi)) ((d : ℤ) - i)) ∧
      (∀ (i : ℕ) (hi : i < j),
        NonvanishingAtGenericOff I (familyCut _ (prefixFamily (secs f I L m s) i hi.le))
          (tensorPowModule X L m) (secs f I L m s ⟨i, hi⟩)) from H d le_rfl
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨Fin.elim0, hQ0, fun i hi => ?_, fun i hi => ?_, fun i hi => absurd hi (by lia)⟩
    · obtain rfl : i = 0 := by lia
      rw [familyCut_elim0]
      exact smoothOffSupport_bot f I
    · obtain rfl : i = 0 := by lia
      rw [familyCut_elim0]
      simpa using hdim0
  | succ j ih =>
    intro hj
    obtain ⟨s, hQs, hsm, hdim, hnv⟩ := ih (by lia)
    obtain ⟨P, hP, hPQ⟩ := hQ j (by lia) s hQs
    have hsmj := hsm j le_rfl
    have hdimj := hdim j le_rfl
    rw [prefixFamily_self] at hsmj hdimj
    obtain ⟨v, hvP, hvsm, hvdim, hvnv⟩ := exists_cut_step f I L m _ hsmj _ hdimj h himm
      (fun _ : Unit => P) (fun _ => hP)
    refine ⟨Fin.snoc s v, hPQ v (hvP ()), fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · rcases Nat.le_succ_iff.1 hi with hij | rfl
      · rw [prefixFamily_secs_snoc f I L m s v hij]
        exact hsm i hij
      · rw [prefixFamily_self, familyCut_secs_snoc]
        exact hvsm
    · rcases Nat.le_succ_iff.1 hi with hij | rfl
      · rw [prefixFamily_secs_snoc f I L m s v hij]
        exact hdim i hij
      · rw [prefixFamily_self, familyCut_secs_snoc]
        convert hvdim using 1
        push_cast
        ring
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hij | rfl
      · rw [prefixFamily_secs_snoc f I L m s v hij.le, secs_snoc_castSucc f I L m s v i hi hij]
        exact hnv i hij
      · rw [prefixFamily_secs_snoc f I L m s v le_rfl, prefixFamily_self,
          secs_snoc_last f I L m s v hi]
        exact hvnv

end Stacks.Chow.BertiniChain

end
