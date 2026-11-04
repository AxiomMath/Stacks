module

public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Dimension.PivotEntry

/-!
# The quotient symbol

The symbol `quotientSymbol` of the sequence obtained by deleting the pivot entry, its
compatibility with the unit-change and dependence relations of the determinant, and
auxiliary lemmas on deleting an entry from an adjacent swap.
-/

@[expose] public section

noncomputable section

namespace Module.FiniteLength
universe u v w

noncomputable def quotientSymbol
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (Q : Type w) [AddCommGroup Q] [Module R Q]
    (q : M →ₗ[R] Q) (f : M) (hf0 : f ≠ 0) (hqf : q f = 0)
    (hlen : moduleLength R Q + 1 = moduleLength R M)
    (e : AdmissibleSequence R M) : determinant R Q := by
  classical
  let n := moduleLength R Q
  let e0 : Fin (n + 1) → M := fun i => e.1 (Fin.cast hlen i)
  have he0 : IsAdmissibleSequence (R := R) e0 :=
    admissible_cast hlen e.1 e.2
  have hrange : Set.range e0 = Set.range e.1 := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.cast hlen i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.cast hlen.symm i, by simp [e0]⟩
  by_cases hspan : f ∈ Submodule.span R (Set.range e0)
  · let p := choosePivotEntry e0 he0 f hf0 hspan
    let d : Fin n → Q := fun j => q (e0 (p.i.succAbove j))
    have hd : IsAdmissibleSequence (R := R) d :=
      admissible_delete_quotient q f hqf e0 he0 p.i p.unit p.x p.decomp p.earlier
    exact ((-1 : IsLocalRing.ResidueField R) ^ p.i.val *
      IsLocalRing.residue R p.unit) • symbol ⟨d, hd⟩
  · exact 0

lemma quotientSymbol_eq_pivot
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (Q : Type w) [AddCommGroup Q] [Module R Q]
    (q : M →ₗ[R] Q) (f : M) (hf0 : f ≠ 0) (hqf : q f = 0)
    (hlen : moduleLength R Q + 1 = moduleLength R M)
    (e : AdmissibleSequence R M)
    (p : PivotUnitEntry (R := R)
      (fun i : Fin (moduleLength R Q + 1) => e.1 (Fin.cast hlen i)) f) :
    quotientSymbol R M Q q f hf0 hqf hlen e =
      ((-1 : IsLocalRing.ResidueField R) ^ p.i.val * IsLocalRing.residue R p.unit) •
        symbol ⟨(fun j => q (e.1 (Fin.cast hlen (p.i.succAbove j)))), by
          have he0 : IsAdmissibleSequence (R := R)
              (fun i : Fin (moduleLength R Q + 1) => e.1 (Fin.cast hlen i)) :=
            admissible_cast hlen e.1 e.2
          exact admissible_delete_quotient q f hqf
            (fun i => e.1 (Fin.cast hlen i)) he0 p.i p.unit p.x p.decomp p.earlier⟩ := by
  classical
  let e0 : Fin (moduleLength R Q + 1) → M := fun i => e.1 (Fin.cast hlen i)
  have he0 : IsAdmissibleSequence (R := R) e0 := admissible_cast hlen e.1 e.2
  have hspan : f ∈ Submodule.span R (Set.range e0) :=
    Submodule.span_mono (s := e0 '' {i | i.val < p.i.val + 1}) (Set.image_subset_range _ _)
      p.pivotMem
  let p₀ := choosePivotEntry e0 he0 f hf0 hspan
  have hi : p₀.i = p.i := pivotUnitEntry_index_eq p₀ p
  have hres : IsLocalRing.residue R (p₀.unit : R) =
      IsLocalRing.residue R (p.unit : R) := pivotUnitEntry_residue_eq p₀ p
  have hseq : (fun j : Fin (moduleLength R Q) => q (e0 (p₀.i.succAbove j))) =
      (fun j => q (e0 (p.i.succAbove j))) := by
    funext j
    simp [hi]
  have hdp₀ := admissible_delete_quotient q f hqf e0 he0 p₀.i p₀.unit p₀.x
    p₀.decomp p₀.earlier
  have hdp := admissible_delete_quotient q f hqf e0 he0 p.i p.unit p.x
    p.decomp p.earlier
  have hsub : (⟨fun j => q (e0 (p₀.i.succAbove j)), hdp₀⟩ : AdmissibleSequence R Q) =
      ⟨fun j => q (e0 (p.i.succAbove j)), hdp⟩ := by
    exact Subtype.ext hseq
  unfold quotientSymbol
  simp [e0, hspan, p₀, hi, hres]

private lemma deleted_quotient_sequence_spans
    {R : Type u} {M : Type v} {Q : Type w} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]
    {n : ℕ} (q : M →ₗ[R] Q) (hq : Function.Surjective q)
    (f : M) (hfq : q f = 0) (e : Fin (n + 1) → M)
    (p : PivotUnitEntry (R := R) e f)
    (hspan : Submodule.span R (Set.range e) = ⊤) :
    Submodule.span R (Set.range (fun j : Fin n => q (e (p.i.succAbove j)))) = ⊤ := by
  classical
  let d : Fin n → Q := fun j => q (e (p.i.succAbove j))
  let T : Submodule R Q := Submodule.span R (Set.range d)
  have hprior : ∀ k : Fin (n + 1), k < p.i → q (e k) ∈ T := by
    intro k hk
    have hne : k ≠ p.i := ne_of_lt hk
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hne
    apply Submodule.subset_span
    exact ⟨j, by simp [d, hj]⟩
  have hpivot : q (e p.i) ∈ T := by
    have hqeq : q (e p.i) = q p.x := by
      rw [p.decomp, map_add, map_smul, hfq]
      simp
    rw [hqeq]
    have hx : ∀ x, x ∈ spanBefore (R := R) e p.i → q x ∈ T := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨k, hk, rfl⟩ := hx
          exact hprior k hk
      | zero => simp
      | add x y hx hy ihx ihy => simpa using T.add_mem ihx ihy
      | smul a x hx ih => simpa using T.smul_mem a ih
    exact hx p.x p.earlier
  have hmap : (Submodule.span R (Set.range e)).map q ≤ T := by
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro y ⟨x, ⟨k, rfl⟩, rfl⟩
    by_cases hki : k = p.i
    · simpa [hki] using hpivot
    · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hki
      exact Submodule.subset_span ⟨j, by simp [d, hj]⟩
  have htop : (⊤ : Submodule R M).map q = ⊤ :=
    (Submodule.map_top q).trans (LinearMap.range_eq_top.mpr hq)
  show T = ⊤
  apply top_unique
  rwa [← htop, ← hspan]

lemma quotientSymbol_ne_zero_of_spanning
    {R : Type u} {M : Type v} {Q : Type w} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]
    (hQ : IsFiniteLength R Q) (hQdet : Nontrivial (determinant R Q))
    (q : M →ₗ[R] Q) (hq : Function.Surjective q)
    (f : M) (hf0 : f ≠ 0) (hfq : q f = 0)
    (hlen : moduleLength R Q + 1 = moduleLength R M)
    (e : AdmissibleSequence R M)
    (he : Submodule.span R (Set.range e.1) = ⊤) :
    quotientSymbol R M Q q f hf0 hfq hlen e ≠ 0 := by
  classical
  let n := moduleLength R Q
  let e0 : Fin (n + 1) → M := fun i => e.1 (Fin.cast hlen i)
  have he0 : IsAdmissibleSequence (R := R) e0 := admissible_cast hlen e.1 e.2
  have hrange : Set.range e0 = Set.range e.1 := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.cast hlen i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.cast hlen.symm i, by simp [e0]⟩
  have hspan0 : Submodule.span R (Set.range e0) = ⊤ := by
    rwa [hrange]
  have hfspan : f ∈ Submodule.span R (Set.range e0) := by
    rw [hspan0]
    exact Submodule.mem_top
  let p := choosePivotEntry e0 he0 f hf0 hfspan
  let d : Fin n → Q := fun j => q (e0 (p.i.succAbove j))
  have hd : IsAdmissibleSequence (R := R) d :=
    admissible_delete_quotient q f hfq e0 he0 p.i p.unit p.x p.decomp p.earlier
  have hdspan : Submodule.span R (Set.range d) = ⊤ :=
    deleted_quotient_sequence_spans q hq f hfq e0 p hspan0
  let de : AdmissibleSequence R Q := ⟨d, hd⟩
  have hdsymbol : symbol de ≠ 0 := by
    intro hz
    have hgen := span_symbol_eq_top hQ de hdspan
    rw [hz] at hgen
    have hbot : (⊥ : Submodule (IsLocalRing.ResidueField R) (determinant R Q)) = ⊤ := by
      simp at hgen
    exact (bot_ne_top : (⊥ : Submodule (IsLocalRing.ResidueField R)
      (determinant R Q)) ≠ ⊤) hbot
  have hcoeff :
      (-1 : IsLocalRing.ResidueField R) ^ p.i.val * IsLocalRing.residue R p.unit ≠ 0 := by
    apply mul_ne_zero
    · apply pow_ne_zero
      norm_num
    · intro hz
      have hnot : (p.unit : R) ∉ IsLocalRing.maximalIdeal R :=
        IsLocalRing.notMem_maximalIdeal.mpr p.unit.isUnit
      exact hnot ((IsLocalRing.residue_eq_zero_iff _).mp hz)
  have hpivotEq := quotientSymbol_eq_pivot R M Q q f hf0 hfq hlen e p
  rw [hpivotEq]
  simpa [de, d, e0] using smul_ne_zero hcoeff hdsymbol

lemma quotientSymbol_zero_of_not_span
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (Q : Type w) [AddCommGroup Q] [Module R Q]
    (q : M →ₗ[R] Q) (f : M) (hf0 : f ≠ 0) (hqf : q f = 0)
    (hlen : moduleLength R Q + 1 = moduleLength R M)
    (e : AdmissibleSequence R M)
    (hspan : f ∉ Submodule.span R
      (Set.range (fun i : Fin (moduleLength R Q + 1) => e.1 (Fin.cast hlen i)))) :
    quotientSymbol R M Q q f hf0 hqf hlen e = 0 := by
  classical
  simp [quotientSymbol, hspan]

/-- Images under `q` of `spanBefore e a` lie in the span before the deleted index of `a`. -/
private lemma map_mem_spanBefore_deleted
    {R : Type u} {M : Type v} {Q : Type w} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]
    {n : ℕ} (q : M →ₗ[R] Q) (f : M) (hqf : q f = 0)
    (e : Fin (n + 1) → M) (p : PivotUnitEntry (R := R) e f)
    (j : Fin n) (a : Fin (n + 1)) (hj : p.i.succAbove j = a) {x : M}
    (hx : x ∈ spanBefore (R := R) e a) :
    q x ∈ spanBefore (R := R) (fun k : Fin n => q (e (p.i.succAbove k))) j := by
  subst hj
  exact map_spanBefore_le_of_pivot q f hqf e p j (Submodule.mem_map_of_mem hx)

lemma quotientSymbol_unitChange
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (Q : Type w) [AddCommGroup Q] [Module R Q]
    (q : M →ₗ[R] Q) (f : M) (hf0 : f ≠ 0) (hqf : q f = 0)
    (hlen : moduleLength R Q + 1 = moduleLength R M)
    (e : AdmissibleSequence R M) (a : Fin (moduleLength R M))
    (unit : Rˣ) (replacement x : M)
    (ha : e.1 a = (unit : R) • replacement + x)
    (hx : x ∈ spanBefore (R := R) e.1 a)
    (hreplacement : IsAdmissibleSequence (R := R) (Function.update e.1 a replacement)) :
    quotientSymbol R M Q q f hf0 hqf hlen e =
      IsLocalRing.residue R unit •
        quotientSymbol R M Q q f hf0 hqf hlen
          ⟨Function.update e.1 a replacement, hreplacement⟩ := by
  classical
  let n := moduleLength R Q
  let eNew : AdmissibleSequence R M := ⟨Function.update e.1 a replacement, hreplacement⟩
  let e0 : Fin (n + 1) → M := fun i => e.1 (Fin.cast hlen i)
  let a0 : Fin (n + 1) := Fin.cast hlen.symm a
  let e0New : Fin (n + 1) → M := fun i => eNew.1 (Fin.cast hlen i)
  let e0Update : Fin (n + 1) → M := Function.update e0 a0 replacement
  have he0 : IsAdmissibleSequence (R := R) e0 := admissible_cast hlen e.1 e.2
  have he0New : IsAdmissibleSequence (R := R) e0New :=
    admissible_cast hlen eNew.1 eNew.2
  have heq : e0New = e0Update := by
    funext i
    by_cases hi : i = a0
    · subst i
      simp [e0New, e0Update, e0, eNew, a0]
    · have hcast : Fin.cast hlen i ≠ a := by
        intro h
        apply hi
        apply Fin.cast_injective hlen
        simpa [a0] using h
      simp [e0New, e0Update, e0, eNew, a0, hi, hcast]
  have ha0 : e0 a0 = (unit : R) • replacement + x := by
    simpa [e0, a0] using ha
  have hx0 : x ∈ spanBefore (R := R) e0 a0 := by
    simpa [e0, a0, spanBefore_cast] using hx
  have he0Update : IsAdmissibleSequence (R := R) e0Update := by
    rwa [← heq]
  let eNewDerived : AdmissibleSequence R M :=
    ⟨fun i => e0Update (Fin.cast hlen.symm i),
      admissible_cast hlen.symm e0Update he0Update⟩
  have hseqNew : eNewDerived = eNew := by
    apply Subtype.ext
    funext i
    by_cases hi : i = a
    · subst i
      simp [eNewDerived, e0Update, e0, a0, eNew]
    · have hnot : Fin.cast hlen.symm i ≠ a0 := by
        intro h
        apply hi
        have hc := congrArg (Fin.cast hlen) h
        simpa [a0] using hc
      have hcast : Fin.cast hlen (Fin.cast hlen.symm i) = i := by simp
      simp [eNewDerived, e0Update, e0, a0, eNew, hi, hnot, hcast]
  have hcut : initialSpan (R := R) e0 (n + 1) =
      initialSpan (R := R) e0Update (n + 1) := by
    show initialSpan (R := R) e0 (n + 1) =
      initialSpan (R := R) (Function.update e0 a0 replacement) (n + 1)
    exact initialSpan_update_eq e0 a0 unit replacement x ha0 hx0 (by omega)
  have hfull : Submodule.span R (Set.range e0) =
      Submodule.span R (Set.range e0Update) := by
    calc
      Submodule.span R (Set.range e0) = initialSpan (R := R) e0 (n + 1) :=
        span_range_eq_initialSpan e0
      _ = initialSpan (R := R) e0Update (n + 1) := hcut
      _ = Submodule.span R (Set.range e0Update) :=
        (span_range_eq_initialSpan e0Update).symm
  by_cases hspan : f ∈ Submodule.span R (Set.range e0)
  · let p := choosePivotEntry e0 he0 f hf0 hspan
    obtain ⟨pUpdate, hpidx, hpunitAt, hpunitAway⟩ :=
      pivotUnitEntry_update p a0 unit replacement x ha0 hx0
    let pNew : PivotUnitEntry (R := R)
        (fun i : Fin (n + 1) => eNewDerived.1 (Fin.cast hlen i)) f := {
      i := pUpdate.i
      unit := pUpdate.unit
      x := pUpdate.x
      decomp := by simpa [eNewDerived] using pUpdate.decomp
      earlier := pUpdate.earlier
      pivotMem := pUpdate.pivotMem
      pivotMin := pUpdate.pivotMin
    }
    have hpnewidx : pNew.i = p.i := by
      simpa [pNew] using hpidx
    have hpnewunitAt : p.i = a0 → pNew.unit = unit⁻¹ * p.unit := by
      intro h
      simpa [pNew] using hpunitAt h
    have hpnewunitAway : p.i ≠ a0 → pNew.unit = p.unit := by
      intro h
      simpa [pNew] using hpunitAway h
    let d : Fin n → Q := fun j => q (e0 (p.i.succAbove j))
    let dNew : Fin n → Q := fun j => q (e0Update (pNew.i.succAbove j))
    have hd : IsAdmissibleSequence (R := R) d :=
      admissible_delete_quotient q f hqf e0 he0 p.i p.unit p.x p.decomp p.earlier
    have hdNew : IsAdmissibleSequence (R := R) dNew :=
      admissible_delete_quotient q f hqf e0Update he0Update pNew.i pNew.unit pNew.x
        pNew.decomp pNew.earlier
    have hqold : quotientSymbol R M Q q f hf0 hqf hlen e =
        ((-1 : IsLocalRing.ResidueField R) ^ p.i.val *
          IsLocalRing.residue R p.unit) • symbol ⟨d, hd⟩ := by
      simpa [d, e0] using quotientSymbol_eq_pivot R M Q q f hf0 hqf hlen e p
    have hqnewDerived : quotientSymbol R M Q q f hf0 hqf hlen eNewDerived =
        ((-1 : IsLocalRing.ResidueField R) ^ pNew.i.val *
          IsLocalRing.residue R pNew.unit) • symbol ⟨dNew, hdNew⟩ := by
      simpa [dNew, eNewDerived] using
        quotientSymbol_eq_pivot R M Q q f hf0 hqf hlen eNewDerived pNew
    have hqseq : quotientSymbol R M Q q f hf0 hqf hlen eNewDerived =
        quotientSymbol R M Q q f hf0 hqf hlen eNew :=
      congrArg (quotientSymbol R M Q q f hf0 hqf hlen) hseqNew
    have hqnew : quotientSymbol R M Q q f hf0 hqf hlen eNew =
        ((-1 : IsLocalRing.ResidueField R) ^ pNew.i.val *
          IsLocalRing.residue R pNew.unit) • symbol ⟨dNew, hdNew⟩ := by
      rwa [← hqseq]
    by_cases hia : p.i = a0
    · have hdEq : (⟨d, hd⟩ : AdmissibleSequence R Q) = ⟨dNew, hdNew⟩ := by
        apply Subtype.ext
        funext j
        simp [d, dNew, e0Update, hpnewidx, hia]
      have hunit := hpnewunitAt hia
      rw [hqold, hqnew, hdEq]
      have hcoeff : (-1 : IsLocalRing.ResidueField R) ^ p.i.val *
          IsLocalRing.residue R p.unit =
          IsLocalRing.residue R unit *
            ((-1 : IsLocalRing.ResidueField R) ^ pNew.i.val *
              IsLocalRing.residue R pNew.unit) := by
        rw [hpnewidx, hunit]
        simp [map_mul, mul_assoc, mul_comm]
      calc
        ((-1 : IsLocalRing.ResidueField R) ^ p.i.val * IsLocalRing.residue R p.unit) •
            symbol ⟨dNew, hdNew⟩ =
          (IsLocalRing.residue R unit *
              ((-1 : IsLocalRing.ResidueField R) ^ pNew.i.val *
                IsLocalRing.residue R pNew.unit)) • symbol ⟨dNew, hdNew⟩ := by rw [hcoeff]
        _ = IsLocalRing.residue R unit •
            (((-1 : IsLocalRing.ResidueField R) ^ pNew.i.val *
              IsLocalRing.residue R pNew.unit) • symbol ⟨dNew, hdNew⟩) := by rw [smul_smul]
    · have hnot : a0 ≠ p.i := fun h => hia h.symm
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hnot
      let dUpdate : Fin n → Q := Function.update d j (q replacement)
      have hxq : q x ∈ spanBefore (R := R) d j :=
        map_mem_spanBefore_deleted q f hqf e0 p j a0 hj hx0
      have hrel : d j = (unit : R) • q replacement + q x := by
        dsimp [d]
        rw [hj, ha0, map_add, map_smul]
      have hfun : dNew = dUpdate := by
        funext j'
        by_cases hji : j' = j
        · subst j'
          simp [dNew, dUpdate, d, e0Update, hpnewidx, hj]
        · have hneq : p.i.succAbove j' ≠ a0 := by
            intro heqidx
            apply hji
            exact Fin.succAbove_right_injective (p := p.i) (heqidx.trans hj.symm)
          simp [dNew, dUpdate, d, e0Update, hpnewidx,
            Function.update_of_ne hji, hneq]
      have hdUpdate : IsAdmissibleSequence (R := R) dUpdate := by
        rwa [← hfun]
      have hdEq : (⟨dNew, hdNew⟩ : AdmissibleSequence R Q) = ⟨dUpdate, hdUpdate⟩ := by
        exact Subtype.ext hfun
      have hsymbol : symbol ⟨d, hd⟩ =
          IsLocalRing.residue R unit • symbol ⟨dUpdate, hdUpdate⟩ := by
        apply symbol_unitChange ⟨d, hd⟩ j unit (q replacement) (q x) hrel hxq hdUpdate
      rw [hqold, hqnew, hdEq]
      have hunit := hpnewunitAway hia
      calc
        ((-1 : IsLocalRing.ResidueField R) ^ p.i.val * IsLocalRing.residue R p.unit) •
            symbol ⟨d, hd⟩ =
          ((-1 : IsLocalRing.ResidueField R) ^ p.i.val * IsLocalRing.residue R p.unit) •
            (IsLocalRing.residue R unit • symbol ⟨dUpdate, hdUpdate⟩) := by rw [hsymbol]
        _ = IsLocalRing.residue R unit •
            (((-1 : IsLocalRing.ResidueField R) ^ pNew.i.val *
              IsLocalRing.residue R pNew.unit) • symbol ⟨dUpdate, hdUpdate⟩) := by
          rw [smul_smul, smul_smul, hpnewidx, hunit]
          congr 1
          ring
  · have hnotNew : f ∉ Submodule.span R (Set.range e0New) := by
      intro hf
      apply hspan
      rwa [hfull, ← heq]
    have hnotOld : f ∉ Submodule.span R
        (Set.range (fun i : Fin (moduleLength R Q + 1) => e.1 (Fin.cast hlen i))) := by
      simpa [e0] using hspan
    have hnotNew' : f ∉ Submodule.span R
        (Set.range (fun i : Fin (moduleLength R Q + 1) => eNew.1 (Fin.cast hlen i))) := by
      simpa [e0New] using hnotNew
    rw [quotientSymbol_zero_of_not_span R M Q q f hf0 hqf hlen e hnotOld,
      quotientSymbol_zero_of_not_span R M Q q f hf0 hqf hlen eNew hnotNew']
    simp

lemma quotientSymbol_zero_of_dependent
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (Q : Type w) [AddCommGroup Q] [Module R Q]
    (q : M →ₗ[R] Q) (f : M) (hf0 : f ≠ 0) (hqf : q f = 0)
    (hlen : moduleLength R Q + 1 = moduleLength R M)
    (e : AdmissibleSequence R M) (a : Fin (moduleLength R M))
    (ha : e.1 a ∈ spanBefore (R := R) e.1 a) :
    quotientSymbol R M Q q f hf0 hqf hlen e = 0 := by
  classical
  let n := moduleLength R Q
  let e0 : Fin (n + 1) → M := fun i => e.1 (Fin.cast hlen i)
  have he0 : IsAdmissibleSequence (R := R) e0 := admissible_cast hlen e.1 e.2
  let a0 : Fin (n + 1) := Fin.cast hlen.symm a
  have ha0 : e0 a0 ∈ spanBefore (R := R) e0 a0 := by
    simpa [e0, a0, spanBefore_cast] using ha
  by_cases hspan : f ∈ Submodule.span R (Set.range e0)
  · let p := choosePivotEntry e0 he0 f hf0 hspan
    have hneq : p.i ≠ a0 := by
      intro h
      apply p.pivotMin
      rw [h]
      have hdiff : e0 a0 - p.x ∈ spanBefore (R := R) e0 a0 :=
        (spanBefore (R := R) e0 a0).sub_mem ha0 (by simpa [h] using p.earlier)
      have hdecomp : e0 a0 = (↑p.unit : R) • f + p.x := by
        simpa [h] using p.decomp
      have hrewrite : f = (↑p.unit⁻¹ : R) • (e0 a0 - p.x) := by
        calc
          f = (↑p.unit⁻¹ : R) • ((↑p.unit : R) • f) := by simp [smul_smul]
          _ = (↑p.unit⁻¹ : R) • (e0 a0 - p.x) := by rw [hdecomp]; congr 1; abel
      rw [hrewrite]
      exact (spanBefore (R := R) e0 a0).smul_mem _ hdiff
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hneq.symm
    let d : Fin n → Q := fun j => q (e0 (p.i.succAbove j))
    have hd : IsAdmissibleSequence (R := R) d :=
      admissible_delete_quotient q f hqf e0 he0 p.i p.unit p.x p.decomp p.earlier
    have hqmem : q (e0 a0) ∈ spanBefore (R := R) d j :=
      map_mem_spanBefore_deleted q f hqf e0 p j a0 hj ha0
    have hqdep : d j ∈ spanBefore (R := R) d j := by
      simpa [d, hj] using hqmem
    have hz : symbol ⟨d, hd⟩ = 0 :=
      symbol_eq_zero_of_mem_spanBefore ⟨d, hd⟩ j hqdep
    rw [quotientSymbol_eq_pivot R M Q q f hf0 hqf hlen e p]
    have hsym : (symbol
        ⟨fun j => q (e.1 (Fin.cast hlen (p.i.succAbove j))),
          admissible_delete_quotient q f hqf e0 he0 p.i p.unit p.x p.decomp p.earlier⟩) =
        symbol ⟨d, hd⟩ := by
      apply congrArg symbol
      apply Subtype.ext
      funext j
      rfl
    rw [hsym, hz]
    simp
  · exact quotientSymbol_zero_of_not_span R M Q q f hf0 hqf hlen e hspan

lemma spanBefore_succAdjacent
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {n : ℕ} (e : Fin n → M) (a b : Fin n) (hba : b.val + 1 = a.val) :
    spanBefore (R := R) e a =
      Submodule.span R (insert (e b) (e '' Set.Iio b)) := by
  rw [spanBefore_eq_initialSpan, show a.val = b.val + 1 by omega, initialSpan_succ]
  congr 1

lemma map_spanBefore_before_pivot_le_deletedPrefix
    {R : Type u} {M : Type v} {Q : Type w} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]
    {n : ℕ} (q : M →ₗ[R] Q) (e : Fin (n + 1) → M) {f : M}
    (p : PivotUnitEntry (R := R) e f) (j : Fin n)
    (target : Fin (n + 1)) (htarget : p.i.succAbove j = target)
    (htargetBefore : target < p.i) :
    (spanBefore (R := R) e target).map q ≤
      spanBefore (R := R) (fun k : Fin n => q (e (p.i.succAbove k))) j := by
  classical
  let d : Fin n → Q := fun k => q (e (p.i.succAbove k))
  rw [spanBefore, Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro y ⟨z, ⟨k, hk, rfl⟩, rfl⟩
  have hkp : k ≠ p.i := ne_of_lt (lt_trans hk htargetBefore)
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hkp
  have hlt : p.i.succAbove j' < p.i.succAbove j := by
    rwa [hj', htarget]
  have hjlt : j' < j := (Fin.succAbove_lt_succAbove_iff).mp hlt
  exact Submodule.subset_span ⟨j', hjlt, by simp [hj']⟩

/-- Alias of `Stacks.Cech.LinearCupProduct.val_succAbove`. -/
alias succAbove_val_formula := Stacks.Cech.LinearCupProduct.val_succAbove

lemma exists_adjacent_delete_index {n : ℕ} (a b : Fin (n + 1))
    (hba : b.val + 1 = a.val) :
    ∃ k : Fin n, k.castSucc = b ∧ k.succ = a := by
  refine ⟨⟨b.val, by omega⟩, ?_, ?_⟩
  · apply Fin.ext
    rfl
  · apply Fin.ext
    simp only [Fin.val_succ]
    omega

lemma swapAdjacent_delete_left
    {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
    {n : ℕ} (e : Fin (n + 1) → M) (a b : Fin (n + 1))
    (_hba : b.val + 1 = a.val) (k : Fin n)
    (hbk : k.castSucc = b) (hak : k.succ = a) :
    (fun j : Fin n => e (b.succAbove j)) =
      (fun j : Fin n => swapAdjacent (R := R) e a b (a.succAbove j)) := by
  funext j
  by_cases hj : j < k
  · have hleft := Fin.succAbove_castSucc_of_lt k j hj
    have hright := Fin.succAbove_succ_of_le k j (le_of_lt hj)
    rw [← hbk, ← hak, hleft, hright]
    have hneA : j.castSucc ≠ k.succ :=
      Fin.ne_of_lt ((Fin.castSucc_lt_succ_iff).2 (le_of_lt hj))
    have hneB : j.castSucc ≠ k.castSucc :=
      Fin.ne_of_lt ((Fin.castSucc_lt_castSucc_iff).2 hj)
    simp [swapAdjacent, hneA, hneB]
  · by_cases hEq : j = k
    · subst j
      rw [← hbk, ← hak, Fin.succAbove_castSucc_self, Fin.succAbove_succ_self]
      have hneq : k.castSucc ≠ k.succ :=
        Fin.ne_of_lt ((Fin.castSucc_lt_succ_iff).2 le_rfl)
      simp [swapAdjacent, hneq]
    · have hgt : k < j := lt_of_le_of_ne (le_of_not_gt hj) (Ne.symm hEq)
      have hleft := Fin.succAbove_castSucc_of_le k j (le_of_lt hgt)
      have hright := Fin.succAbove_succ_of_lt k j hgt
      rw [← hbk, ← hak, hleft, hright]
      have hneA : j.succ ≠ k.succ := Fin.ne_of_gt (Fin.succ_lt_succ_iff.2 hgt)
      have hneB : j.succ ≠ k.castSucc :=
        (Fin.ne_of_lt ((Fin.castSucc_lt_succ_iff).2 (le_of_lt hgt))).symm
      simp [swapAdjacent, hneA, hneB]

lemma swapAdjacent_delete_right
    {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
    {n : ℕ} (e : Fin (n + 1) → M) (a b : Fin (n + 1))
    (_hba : b.val + 1 = a.val) (k : Fin n)
    (hbk : k.castSucc = b) (hak : k.succ = a) :
    (fun j : Fin n => e (a.succAbove j)) =
      (fun j : Fin n => swapAdjacent (R := R) e a b (b.succAbove j)) := by
  have hab : a ≠ b := by
    rw [← hak, ← hbk]
    exact Fin.castSucc_lt_succ.ne'
  have hinv : swapAdjacent (R := R) (swapAdjacent (R := R) e a b) a b = e := by
    funext i
    by_cases hia : i = a
    · subst hia
      simp [swapAdjacent, hab.symm]
    · by_cases hib : i = b
      · subst hib
        simp [swapAdjacent, hab.symm]
      · simp [swapAdjacent, hia, hib]
  have h := swapAdjacent_delete_left (R := R) (swapAdjacent (R := R) e a b) a b _hba k hbk hak
  rw [hinv] at h
  exact h.symm

end Module.FiniteLength

end
