module

public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Dimension.QuotientSymbolSwap

/-!
# The determinant has dimension one

The map `quotientSymbolMap` from the determinant of `M` to the determinant of `M / S`, and
the proof of `Module.FiniteLength.finrank_determinant_eq_one`.
-/

@[expose] public section

noncomputable section

namespace Module.FiniteLength
universe u v w

private noncomputable def quotientSymbolRaw
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (Q : Type w) [AddCommGroup Q] [Module R Q]
    (q : M →ₗ[R] Q) (f : M) (hf0 : f ≠ 0) (hqf : q f = 0)
    (hlen : moduleLength R Q + 1 = moduleLength R M) :
    DeterminantFree R M →ₗ[IsLocalRing.ResidueField R] determinant R Q :=
  Finsupp.linearCombination (IsLocalRing.ResidueField R)
    (fun e : AdmissibleSequence R M =>
      quotientSymbol R M Q q f hf0 hqf hlen e)

private lemma quotientSymbolRaw_single
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (Q : Type w) [AddCommGroup Q] [Module R Q]
    (q : M →ₗ[R] Q) (f : M) (hf0 : f ≠ 0) (hqf : q f = 0)
    (hlen : moduleLength R Q + 1 = moduleLength R M)
    (e : AdmissibleSequence R M) :
    quotientSymbolRaw R M Q q f hf0 hqf hlen (Finsupp.single e 1) =
      quotientSymbol R M Q q f hf0 hqf hlen e := by
  simp [quotientSymbolRaw]

private lemma quotientSymbolRaw_relation
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (Q : Type w) [AddCommGroup Q] [Module R Q]
    (q : M →ₗ[R] Q) (f : M) (hf0 : f ≠ 0) (hqf : q f = 0)
    (hlen : moduleLength R Q + 1 = moduleLength R M)
    (z : DeterminantFree R M) (hz : DeterminantRelation z) :
    quotientSymbolRaw R M Q q f hf0 hqf hlen z = 0 := by
  classical
  cases hz with
  | dependent e a ha =>
      rw [quotientSymbolRaw_single]
      exact quotientSymbol_zero_of_dependent R M Q q f hf0 hqf hlen e a ha
  | unitChange e a unit replacement x ha hx hreplacement =>
      simp only [map_sub, map_smul, quotientSymbolRaw_single, sub_eq_zero]
      exact quotientSymbol_unitChange R M Q q f hf0 hqf hlen e a unit
        replacement x ha hx hreplacement
  | swap e a b hba ha hswap =>
      simp only [map_add, quotientSymbolRaw_single, add_eq_zero_iff_eq_neg]
      exact quotientSymbol_swap R M Q q f hf0 hqf hlen e a b hba ha hswap

private noncomputable def quotientSymbolMap
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (Q : Type w) [AddCommGroup Q] [Module R Q]
    (q : M →ₗ[R] Q) (f : M) (hf0 : f ≠ 0) (hqf : q f = 0)
    (hlen : moduleLength R Q + 1 = moduleLength R M) :
    determinant R M →ₗ[IsLocalRing.ResidueField R] determinant R Q :=
  (determinantRelations R M).liftQ
    (quotientSymbolRaw R M Q q f hf0 hqf hlen) (Submodule.span_le.mpr fun z hz =>
      LinearMap.mem_ker.mpr (quotientSymbolRaw_relation R M Q q f hf0 hqf hlen z hz))

private lemma quotientSymbolMap_symbol
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (Q : Type w) [AddCommGroup Q] [Module R Q]
    (q : M →ₗ[R] Q) (f : M) (hf0 : f ≠ 0) (hqf : q f = 0)
    (hlen : moduleLength R Q + 1 = moduleLength R M)
    (e : AdmissibleSequence R M) :
    quotientSymbolMap R M Q q f hf0 hqf hlen (symbol e) =
      quotientSymbol R M Q q f hf0 hqf hlen e := by
  change quotientSymbolRaw R M Q q f hf0 hqf hlen (Finsupp.single e 1) = _
  exact quotientSymbolRaw_single R M Q q f hf0 hqf hlen e

private lemma determinant_nontrivial_of_moduleLength_eq_zero
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (hn : moduleLength R M = 0) :
    Nontrivial (determinant R M) := by
  classical
  let K := IsLocalRing.ResidueField R
  let raw : DeterminantFree R M →ₗ[K] K :=
    Finsupp.linearCombination K (fun _ : AdmissibleSequence R M => (1 : K))
  have hfin (i : Fin (moduleLength R M)) : False := Fin.elim0 (hn ▸ i)
  have hraw (z : DeterminantFree R M) (hz : DeterminantRelation z) : raw z = 0 := by
    cases hz <;> exact (hfin ‹Fin _›).elim
  let φ : determinant R M →ₗ[K] K :=
    (determinantRelations R M).liftQ raw
      (Submodule.span_le.mpr fun z hz => LinearMap.mem_ker.mpr (hraw z hz))
  let e : AdmissibleSequence R M :=
    ⟨fun i => (hfin i).elim, fun i => (hfin i).elim⟩
  have hφ : φ (symbol e) = 1 := by
    change raw (Finsupp.single e 1) = 1
    simp [raw]
  have hs : symbol e ≠ 0 := by
    intro hs
    have := congrArg φ hs
    simp [hφ] at this
  exact ⟨⟨symbol e, 0, hs⟩⟩

/-- The determinant of a finite-length module over a local ring has dimension one over the
residue field. -/
@[stacks 02P9 "dimension"]
public theorem finrank_determinant_eq_one {R : Type u} {M : Type v} [CommRing R]
    [IsLocalRing R] [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    Module.finrank (IsLocalRing.ResidueField R) (determinant R M) = 1 := by
  classical
  have aux : ∀ n : ℕ, ∀ (N : Type v) [AddCommGroup N] [Module R N],
      IsFiniteLength R N → moduleLength R N = n → Nontrivial (determinant R N) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro N _ _ hN hn
        by_cases hn0 : n = 0
        · have hn' : moduleLength R N = 0 := by simpa [hn0] using hn
          exact determinant_nontrivial_of_moduleLength_eq_zero hn'
        · have hlenNe : Module.length R N ≠ 0 := by
            intro hzero
            have hnzero : moduleLength R N = 0 := by simp [moduleLength, hzero]
            omega
          have hNne : Nontrivial N :=
            Module.length_pos_iff.mp (pos_iff_ne_zero.mpr hlenNe)
          obtain ⟨f, hf0, hkill⟩ := exists_nonzero_socle_element hN hNne
          let S : Submodule R N := R ∙ f
          let q : N →ₗ[R] N ⧸ S := S.mkQ
          obtain ⟨hQfin, hlenQ⟩ := socle_quotient_length hN f hf0 hkill
          have hQlt : moduleLength R (N ⧸ S) < n := by
            rw [hn] at hlenQ
            change moduleLength R (N ⧸ S) + 1 = n at hlenQ
            omega
          have hQdet : Nontrivial (determinant R (N ⧸ S)) :=
            ih (moduleLength R (N ⧸ S)) hQlt (N ⧸ S) hQfin rfl
          have hqf : q f = 0 := by
            change S.mkQ f = 0
            exact (Submodule.Quotient.mk_eq_zero S).2
              (Submodule.mem_span_singleton_self f)
          obtain ⟨e, he⟩ := exists_admissible_generator hN
          have hquot : quotientSymbol R N (N ⧸ S) q f hf0 hqf hlenQ e ≠ 0 :=
            quotientSymbol_ne_zero_of_spanning hQfin hQdet q S.mkQ_surjective
              f hf0 hqf hlenQ e he
          let ψ := quotientSymbolMap R N (N ⧸ S) q f hf0 hqf hlenQ
          have hsym : symbol e ≠ 0 := by
            intro hzero
            have hmap := congrArg ψ hzero
            rw [quotientSymbolMap_symbol] at hmap
            exact hquot (by simpa using hmap)
          exact ⟨⟨symbol e, 0, hsym⟩⟩
  have hdetne : Nontrivial (determinant R M) :=
    aux (moduleLength R M) M hM rfl
  obtain ⟨e, he⟩ := exists_admissible_generator hM
  have : Module.Finite (IsLocalRing.ResidueField R) (determinant R M) :=
    finite_determinant_of_spanning hM e he
  have hpos : 0 < Module.finrank (IsLocalRing.ResidueField R) (determinant R M) :=
    Module.finrank_pos_iff.mpr inferInstance
  have hle := finrank_determinant_le_one R M hM
  omega

end Module.FiniteLength

end
