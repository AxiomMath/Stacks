module

public import StacksFrontier.Homology.Perfect.BoundedComplexCokernelRank

/-!
# Generic freeness of the cohomology of a bounded complex of finite free modules

Let `C` be a bounded complex of finite free modules over a commutative ring `A`, written in chosen
bases as a `BoundedComplex A`, so that `d^i` is an `r_{i+1} × r_i` matrix. If for every `i` the
`ρ_i × ρ_i` minors of `d^i` generate the unit ideal and its `(ρ_i + 1) × (ρ_i + 1)` minors vanish,
then all the cokernels, images and cohomology modules of `C` are finite locally free, of explicitly
computed ranks. Over a domain these conditions hold after inverting a single nonzero element, so
the cohomology of `C` is generically finite locally free. This is the step of the proof of
[Stacks, Tag 0ESR] which spreads out a complex over the generic point.

## Main results

* `BoundedComplex.isFiniteLocallyFreeOfRank_cokernelD_of_minorIdeal`: if the `ρ × ρ` minors of
  `d^i` generate the unit ideal and its `(ρ + 1) × (ρ + 1)` minors vanish, then `coker d^i` is
  finite locally free of rank `r_{i+1} - ρ`.
* `BoundedComplex.isFiniteLocallyFreeOfRank_range_d_of_minorIdeal`: under the same hypotheses
  `im d^i` is finite locally free of rank `ρ`.
* `BoundedComplex.isFiniteLocallyFreeOfRank_homology_of_minorIdeal`: if this holds in every degree
  with ranks `ρ_i`, then `H^j` is finite locally free of rank `r_j - ρ_j - ρ_{j-1}`.
* `BoundedComplex.exists_isFiniteLocallyFreeOfRank_homology_of_isLocalization_away`: over a
  domain there is a nonzero `δ` such that the cohomology of the base change of `C` to any
  localization `A_δ` is finite locally free, of ranks vanishing in large degrees.

## Implementation notes

The ranks of the cokernels come from the Fitting criterion for finite local freeness
(`finiteLocallyFreeOfRank_fittingIdeal_tfae`, [Stacks, Tag 07ZD]), as the Fitting ideals of
`coker d^i` are ideals of minors of `d^i` (`BoundedComplex.fittingIdeal_cokernelD`). The cohomology
is then the kernel of the split surjection `coker d^{j-1} → im d^j`, and ranks are compared with
`Module.rankAtStalk`. Over a domain, `ρ_i` is the largest size of a nonvanishing minor of `d^i`,
and `δ` is a product of nonzero `ρ_i × ρ_i` minors over the finitely many degrees where `C` lives.

## References

* [Stacks Project, Tag 0ESR](https://stacks.math.columbia.edu/tag/0ESR)
* [Stacks Project, Tag 07ZD](https://stacks.math.columbia.edu/tag/07ZD)
-/

@[expose] public noncomputable section

universe u v

open CategoryTheory Stacks.CokernelRank

namespace BoundedComplex

variable {A : Type u} [CommRing A] (C : BoundedComplex A)

/-- Over the zero ring every module is finite locally free of every rank (the empty family of
elements already generates the unit ideal), so it suffices to treat nontrivial rings. -/
private theorem isFiniteLocallyFreeOfRank_of_nontrivial {M : Type v} [AddCommGroup M]
    [Module A M] {r : ℕ} (h : Nontrivial A → Module.IsFiniteLocallyFreeOfRank A M r) :
    Module.IsFiniteLocallyFreeOfRank A M r :=
  (subsingleton_or_nontrivial A).elim
    (fun _ => ⟨PEmpty, PEmpty.elim, Subsingleton.elim _ _, fun i => i.elim⟩) h

/-- Over a nontrivial ring, if the `ρ × ρ` minors of `d^i` generate the unit ideal then `ρ` is at
most the number `r_{i+1}` of rows of `d^i`. -/
private theorem le_rank_succ_of_minorIdeal_eq_top [Nontrivial A] (i : ℤ) {ρ : ℕ}
    (hρ : minorIdeal (C.d i) ρ = ⊤) : ρ ≤ C.rank (i + 1) := by
  refine le_of_not_gt fun h => top_ne_bot (hρ.symm.trans ?_)
  exact minorIdeal_eq_bot_of_card_lt _ _ (Or.inl (by simpa using h))

/-- If the `ρ × ρ` minors of the matrix of `d^i` generate the unit ideal and its
`(ρ + 1) × (ρ + 1)` minors vanish, then the cokernel of `d^i` is finite locally free of rank
`r_{i+1} - ρ`, by the Fitting criterion [Stacks, Tag 07ZD]. -/
theorem isFiniteLocallyFreeOfRank_cokernelD_of_minorIdeal (i : ℤ) {ρ : ℕ}
    (hρ : minorIdeal (C.d i) ρ = ⊤) (hρ' : minorIdeal (C.d i) (ρ + 1) = ⊥) :
    Module.IsFiniteLocallyFreeOfRank A (C.cokernelD i) (C.rank (i + 1) - ρ) := by
  refine isFiniteLocallyFreeOfRank_of_nontrivial fun _ => ?_
  have hle := C.le_rank_succ_of_minorIdeal_eq_top i hρ
  refine ((finiteLocallyFreeOfRank_fittingIdeal_tfae (R := A) (M := C.cokernelD i)
    (C.rank (i + 1) - ρ)).out 2 1).1 ?_
  refine ⟨?_, ?_⟩
  · rw [show ((C.rank (i + 1) - ρ : ℕ) : ℤ) - 1 = (C.rank (i + 1) : ℤ) - ρ - 1 by omega,
      C.fittingIdeal_cokernelD_sub_one i hle, hρ']
  · rw [C.fittingIdeal_cokernelD i hle, hρ]

/-- If the `ρ × ρ` minors of the matrix of `d^i` generate the unit ideal and its
`(ρ + 1) × (ρ + 1)` minors vanish, then the cokernel of `d^i` is projective. -/
theorem projective_cokernelD_of_minorIdeal (i : ℤ) {ρ : ℕ}
    (hρ : minorIdeal (C.d i) ρ = ⊤) (hρ' : minorIdeal (C.d i) (ρ + 1) = ⊥) :
    Module.Projective A (C.cokernelD i) :=
  have : Module.Flat A (C.cokernelD i) :=
    Module.flat_of_isFiniteLocallyFreeOfRank
      (C.isFiniteLocallyFreeOfRank_cokernelD_of_minorIdeal i hρ hρ')
  Module.Flat.projective_of_finitePresentation

/-- If the `ρ × ρ` minors of the matrix of `d^i` generate the unit ideal and its
`(ρ + 1) × (ρ + 1)` minors vanish, then the image of `d^i` is finite locally free of rank `ρ`:
it is the kernel of the split surjection of `A^{r_{i+1}}` onto `coker d^i`. -/
theorem isFiniteLocallyFreeOfRank_range_d_of_minorIdeal (i : ℤ) {ρ : ℕ}
    (hρ : minorIdeal (C.d i) ρ = ⊤) (hρ' : minorIdeal (C.d i) (ρ + 1) = ⊥) :
    Module.IsFiniteLocallyFreeOfRank A (LinearMap.range (C.d i).mulVecLin) ρ := by
  refine isFiniteLocallyFreeOfRank_of_nontrivial fun _ => ?_
  have hQ := C.isFiniteLocallyFreeOfRank_cokernelD_of_minorIdeal i hρ hρ'
  have := C.projective_cokernelD_of_minorIdeal i hρ hρ'
  obtain ⟨hB, hBr⟩ := C.projective_range_d_and_rankAtStalk i
  have hle := C.le_rank_succ_of_minorIdeal_eq_top i hρ
  refine Module.isFiniteLocallyFreeOfRank_of_rankAtStalk_eq _ fun p => ?_
  have h1 := hBr p
  have h2 := Module.rankAtStalk_eq_of_isFiniteLocallyFreeOfRank _ hQ p
  omega

/-- **The cohomology of a complex with constant determinantal ranks.** Let `C` be a bounded
complex of finite free modules, of ranks `r_j`, such that for every `i` the `ρ_i × ρ_i` minors of
the matrix of `d^i` generate the unit ideal and its `(ρ_i + 1) × (ρ_i + 1)` minors vanish. Then
every cohomology module `H^j` is finite locally free of rank `r_j - ρ_j - ρ_{j-1}`. -/
theorem isFiniteLocallyFreeOfRank_homology_of_minorIdeal (ρ : ℤ → ℕ)
    (hρ : ∀ i, minorIdeal (C.d i) (ρ i) = ⊤) (hρ' : ∀ i, minorIdeal (C.d i) (ρ i + 1) = ⊥)
    (j : ℤ) :
    Module.IsFiniteLocallyFreeOfRank A (C.toCochainComplex.homology j)
      (C.rank j - ρ j - ρ (j - 1)) := by
  refine isFiniteLocallyFreeOfRank_of_nontrivial fun _ => ?_
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by ring⟩
  rw [add_sub_cancel_right]
  have hQ := C.isFiniteLocallyFreeOfRank_cokernelD_of_minorIdeal i (hρ i) (hρ' i)
  have hB := C.isFiniteLocallyFreeOfRank_range_d_of_minorIdeal (i + 1) (hρ (i + 1))
    (hρ' (i + 1))
  have := C.projective_cokernelD_of_minorIdeal i (hρ i) (hρ' i)
  have := C.projective_cokernelD_of_minorIdeal (i + 1) (hρ (i + 1)) (hρ' (i + 1))
  have : Module.Projective A (LinearMap.range (C.d (i + 1)).mulVecLin) :=
    (C.projective_range_d_and_rankAtStalk (i + 1)).1
  obtain ⟨hfin, hproj, hrank⟩ := finite_projective_ker_and_rankAtStalk_of_surjective
    (C.cokernelDToRange i) (C.cokernelDToRange_surjective i)
  let eH := C.homologyEquivKerCokernelDToRange i
  have : Module.Finite A (C.toCochainComplex.homology (i + 1)) := Module.Finite.equiv eH.symm
  have : Module.Flat A (C.toCochainComplex.homology (i + 1)) := Module.Flat.of_linearEquiv eH
  refine Module.isFiniteLocallyFreeOfRank_of_rankAtStalk_eq _ fun p => ?_
  rw [Module.rankAtStalk_eq_of_equiv eH]
  have h1 := congrFun hrank p
  rw [Pi.add_apply] at h1
  have h2 := Module.rankAtStalk_eq_of_isFiniteLocallyFreeOfRank _ hQ p
  have h3 := Module.rankAtStalk_eq_of_isFiniteLocallyFreeOfRank _ hB p
  omega

/-- The ideal of `r × r` minors of a differential of a base change is the extension of the ideal
of `r × r` minors of the original differential. -/
theorem minorIdeal_baseChange_d {B : Type*} [CommRing B] (φ : A →+* B) (i : ℤ) (r : ℕ) :
    minorIdeal ((C.baseChange φ).d i) r = Ideal.map φ (minorIdeal (C.d i) r) :=
  (map_minorIdeal (C.d i) r φ).symm

/-- Over a domain, every differential `d^i` has a determinantal rank `ρ ≤ r_i`: some `ρ × ρ`
minor of `d^i` is a nonzero element `δ`, while all its `(ρ + 1) × (ρ + 1)` minors vanish. -/
theorem exists_mem_minorIdeal_d_ne_zero [IsDomain A] (i : ℤ) :
    ∃ ρ : ℕ, ∃ δ : A, δ ≠ 0 ∧ δ ∈ minorIdeal (C.d i) ρ ∧ minorIdeal (C.d i) (ρ + 1) = ⊥ ∧
      ρ ≤ C.rank i := by
  classical
  have hex : ∃ s, minorIdeal (C.d i) (s + 1) = ⊥ :=
    ⟨C.rank i, minorIdeal_eq_bot_of_card_lt _ _ (Or.inr (by simp))⟩
  have hne : minorIdeal (C.d i) (Nat.find hex) ≠ ⊥ := by
    rcases h : Nat.find hex with _ | k
    · rw [minorIdeal_zero]
      exact top_ne_bot
    · exact Nat.find_min hex (by omega : k < Nat.find hex)
  obtain ⟨δ, hδ, hδ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨Nat.find hex, δ, hδ0, hδ, Nat.find_spec hex,
    Nat.find_min' hex (minorIdeal_eq_bot_of_card_lt _ _ (Or.inr (by simp)))⟩

/-- **Generic freeness of the cohomology of a bounded complex of finite free modules.** Over a
domain `A`, there are a nonzero element `δ` and ranks `s_j`, vanishing in large degrees, such that
after base change to any localization `A_δ` every cohomology module `H^j` is finite locally free
of rank `s_j`. -/
theorem exists_isFiniteLocallyFreeOfRank_homology_of_isLocalization_away [IsDomain A] :
    ∃ δ : A, δ ≠ 0 ∧ ∃ s : ℤ → ℕ, (∃ m, ∀ j, m < j → s j = 0) ∧
      ∀ (S : Type v) [CommRing S] [Algebra A S] [IsLocalization.Away δ S] (j : ℤ),
        Module.IsFiniteLocallyFreeOfRank S
          ((C.baseChange (algebraMap A S)).toCochainComplex.homology j) (s j) := by
  classical
  choose ρ δ hδ0 hδ hρ' hle using C.exists_mem_minorIdeal_d_ne_zero
  let T := C.bounded.toFinset
  obtain ⟨m, hm⟩ := C.bounded.bddAbove
  have hm' : ∀ j, m < j → C.rank j = 0 := fun j hj => by
    by_contra h
    exact absurd (hm h) (by omega)
  refine ⟨∏ i ∈ T, δ i, Finset.prod_ne_zero_iff.2 fun i _ => hδ0 i,
    fun j => C.rank j - ρ j - ρ (j - 1), ⟨m, fun j hj => by simp [hm' j hj]⟩, ?_⟩
  intro S _ _ _ j
  have hu := IsLocalization.Away.algebraMap_isUnit (S := S) (∏ i ∈ T, δ i)
  refine (C.baseChange (algebraMap A S)).isFiniteLocallyFreeOfRank_homology_of_minorIdeal ρ
    (fun i => ?_) (fun i => ?_) j
  · by_cases hi : i ∈ T
    · rw [minorIdeal_baseChange_d]
      exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ (hδ i))
        (isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem δ hi)) hu)
    · have h0 : ρ i = 0 := by
        have := hle i
        simp only [T, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hi
        omega
      rw [h0, minorIdeal_zero]
  · rw [minorIdeal_baseChange_d, hρ' i, Ideal.map_bot]

end BoundedComplex
