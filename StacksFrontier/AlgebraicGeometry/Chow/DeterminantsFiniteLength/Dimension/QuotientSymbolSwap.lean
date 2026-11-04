module

public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Dimension.QuotientSymbol

/-!
# The quotient symbol and the swap relation

The symbol `quotientSymbol` is compatible with the swap relation of the determinant.
-/

@[expose] public section

noncomputable section

namespace Module.FiniteLength
universe u v w

/-- If `a • f + x = b • f + y` with `x, y` in a submodule not containing `f`, then `a` and `b`
have the same residue. -/
private theorem residue_eq_of_smul_add_eq_smul_add
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    (L : Submodule R M) {f x y : M} {a b : R}
    (h : a • f + x = b • f + y) (hx : x ∈ L) (hy : y ∈ L) (hf : f ∉ L) :
    IsLocalRing.residue R a = IsLocalRing.residue R b := by
  by_contra hres
  obtain ⟨w, hw⟩ : IsUnit (a - b) := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, map_sub]
    exact fun hz => hres (sub_eq_zero.mp hz)
  have hcoeff : (a - b) • f = y - x := by
    rw [sub_smul, sub_eq_sub_iff_add_eq_add, add_comm y]
    exact h
  apply hf
  have hmem := L.smul_mem (↑w⁻¹ : R) (L.sub_mem hy hx)
  rwa [← hcoeff, smul_smul, ← hw, Units.inv_mul, one_smul] at hmem

lemma quotientSymbol_swap
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (Q : Type w) [AddCommGroup Q] [Module R Q]
    (q : M →ₗ[R] Q) (f : M) (hf0 : f ≠ 0) (hqf : q f = 0)
    (hlen : moduleLength R Q + 1 = moduleLength R M)
    (e : AdmissibleSequence R M) (a b : Fin (moduleLength R M))
    (hba : b.val + 1 = a.val)
    (ha : ∀ r, r ∈ IsLocalRing.maximalIdeal R →
      r • e.1 a ∈ spanBefore (R := R) e.1 b)
    (hswap : IsAdmissibleSequence (R := R) (swapAdjacent (R := R) e.1 a b)) :
    quotientSymbol R M Q q f hf0 hqf hlen e = - quotientSymbol R M Q q f hf0 hqf hlen
      ⟨swapAdjacent (R := R) e.1 a b, hswap⟩ := by
  classical
  let n := moduleLength R Q
  let es : AdmissibleSequence R M := ⟨swapAdjacent (R := R) e.1 a b, hswap⟩
  let e0 : Fin (n + 1) → M := fun i => e.1 (Fin.cast hlen i)
  let es0 : Fin (n + 1) → M := fun i => es.1 (Fin.cast hlen i)
  let a0 : Fin (n + 1) := Fin.cast hlen.symm a
  let b0 : Fin (n + 1) := Fin.cast hlen.symm b
  have he0 : IsAdmissibleSequence (R := R) e0 := admissible_cast hlen e.1 e.2
  have hes0 : IsAdmissibleSequence (R := R) es0 := admissible_cast hlen es.1 es.2
  have hba0 : b0.val + 1 = a0.val := by simpa [a0, b0] using hba
  have hab0 : a0 ≠ b0 := by
    intro h
    have := congrArg Fin.val h
    omega
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    omega
  have hcastSwap : es0 = swapAdjacent (R := R) e0 a0 b0 := by
    funext i
    by_cases hi : i = a0
    · subst i
      have haCast : Fin.cast hlen a0 = a := by simp [a0]
      have hleft : es.1 (Fin.cast hlen a0) = e.1 b := by
        rw [haCast]
        simp [es, swapAdjacent]
      have hright : swapAdjacent (R := R) e0 a0 b0 a0 = e0 b0 := by
        simp [swapAdjacent]
      have hbVal : e0 b0 = e.1 b := by simp [e0, b0]
      calc
        es0 a0 = e.1 b := hleft
        _ = swapAdjacent (R := R) e0 a0 b0 a0 :=
          (hright.trans hbVal).symm
    · by_cases hi' : i = b0
      · subst i
        have hbCast : Fin.cast hlen b0 = b := by simp [b0]
        have hleft : es.1 (Fin.cast hlen b0) = e.1 a := by
          rw [hbCast]
          simp [es, swapAdjacent, hab.symm]
        have hright : swapAdjacent (R := R) e0 a0 b0 b0 = e0 a0 := by
          simp [swapAdjacent, hab0.symm]
        have haVal : e0 a0 = e.1 a := by simp [e0, a0]
        calc
          es0 b0 = e.1 a := hleft
          _ = swapAdjacent (R := R) e0 a0 b0 b0 :=
            (hright.trans haVal).symm
      · have hia : Fin.cast hlen i ≠ a := by
          intro h
          apply hi
          apply Fin.cast_injective hlen
          simpa [a0] using h
        have hib : Fin.cast hlen i ≠ b := by
          intro h
          apply hi'
          apply Fin.cast_injective hlen
          simpa [b0] using h
        calc
          es0 i = e.1 (Fin.cast hlen i) := by
            simp [es0, es, swapAdjacent, hia, hib]
          _ = e0 i := rfl
          _ = swapAdjacent (R := R) e0 a0 b0 i := by
            simp [swapAdjacent, hi, hi']
  have hrangeCast (z : AdmissibleSequence R M) :
      Set.range (fun i : Fin (n + 1) => z.1 (Fin.cast hlen i)) = Set.range z.1 := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.cast hlen i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.cast hlen.symm i, by simp⟩
  have hrangeSwap : Set.range (swapAdjacent (R := R) e0 a0 b0) = Set.range e0 := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      by_cases hia : i = a0
      · subst i
        exact ⟨b0, by simp [swapAdjacent]
          ⟩
      · by_cases hib : i = b0
        · subst i
          exact ⟨a0, by simp [swapAdjacent, hab0.symm]
            ⟩
        · exact ⟨i, by simp [swapAdjacent, hia, hib]
            ⟩
    · rintro ⟨i, rfl⟩
      by_cases hia : i = a0
      · subst i
        exact ⟨b0, by simp [swapAdjacent, hab0.symm]
          ⟩
      · by_cases hib : i = b0
        · subst i
          exact ⟨a0, by simp [swapAdjacent]
            ⟩
        · exact ⟨i, by simp [swapAdjacent, hia, hib]
            ⟩
  have hrangeES : Set.range es0 = Set.range e0 := by
    rw [hcastSwap, hrangeSwap]
  have hspanEq : Submodule.span R (Set.range es0) =
      Submodule.span R (Set.range e0) := congrArg (Submodule.span R) hrangeES
  have hentryA : es0 b0 = e0 a0 := by
    rw [hcastSwap]
    simp [swapAdjacent, hab0.symm]
  have hentryB : es0 a0 = e0 b0 := by
    rw [hcastSwap]
    simp [swapAdjacent]
  have hbLtA : b0.val < a0.val := by omega
  have hbeforeSwap : spanBefore (R := R) es0 b0 = spanBefore (R := R) e0 b0 := by
    rw [spanBefore_eq_initialSpan, spanBefore_eq_initialSpan, hcastSwap]
    exact (initialSpan_swapAdjacent_eq_before (R := R) (M := M)
      e0 a0 b0 hba0 (k := b0.val) (by omega)).symm
  have hmonoE : spanBefore (R := R) e0 b0 ≤ spanBefore (R := R) e0 a0 :=
    initialSpan_mono (R := R) e0 hbLtA.le
  have hmonoES : spanBefore (R := R) es0 b0 ≤ spanBefore (R := R) es0 a0 :=
    initialSpan_mono (R := R) es0 hbLtA.le
  by_cases hfspan : f ∈ Submodule.span R (Set.range e0)
  · have hfspanS : f ∈ Submodule.span R (Set.range es0) := by
      rwa [hspanEq]
    let p := choosePivotEntry e0 he0 f hf0 hfspan
    have hqOld := quotientSymbol_eq_pivot R M Q q f hf0 hqf hlen e p
    by_cases hout : p.i.val < b0.val ∨ a0.val < p.i.val
    · let pSwap := pivotUnitEntry_swapAdjacent_of_outside p a0 b0 hba0 hout
      let pS : PivotUnitEntry (R := R) es0 f := {
        i := p.i
        unit := p.unit
        x := p.x
        decomp := by rw [hcastSwap]; exact pSwap.decomp
        earlier := by rw [hcastSwap]; exact pSwap.earlier
        pivotMem := by rw [hcastSwap]; exact pSwap.pivotMem
        pivotMin := by rw [hcastSwap]; exact pSwap.pivotMin
      }
      have hqNew := quotientSymbol_eq_pivot R M Q q f hf0 hqf hlen es pS
      let d : Fin n → Q := fun j => q (e0 (p.i.succAbove j))
      let dS : Fin n → Q := fun j => q (es0 (p.i.succAbove j))
      have hd : IsAdmissibleSequence (R := R) d :=
        admissible_delete_quotient q f hqf e0 he0 p.i p.unit p.x p.decomp p.earlier
      have hdS : IsAdmissibleSequence (R := R) dS :=
        admissible_delete_quotient q f hqf es0 hes0 p.i pS.unit pS.x
          pS.decomp pS.earlier
      obtain ⟨a', ha'⟩ := Fin.exists_succAbove_eq (show a0 ≠ p.i by
        intro h
        have := congrArg Fin.val h
        omega)
      obtain ⟨b', hb'⟩ := Fin.exists_succAbove_eq (show b0 ≠ p.i by
        intro h
        have := congrArg Fin.val h
        omega)
      have hba' : b'.val + 1 = a'.val := by
        have hvalA : (p.i.succAbove a').val = a0.val := by
          simpa using congrArg Fin.val ha'
        have hvalB : (p.i.succAbove b').val = b0.val := by
          simpa using congrArg Fin.val hb'
        rw [succAbove_val_formula] at hvalA hvalB
        rcases hout with hleft | hright
        · have hnA : ¬ a'.val < p.i.val := by
            by_contra h
            simp [h] at hvalA
            omega
          have hnB : ¬ b'.val < p.i.val := by
            by_contra h
            simp [h] at hvalB
            omega
          simp only [ite_eq_right hnA, ite_eq_right hnB] at hvalA hvalB
          omega
        · have hltA : a'.val < p.i.val := by
            by_contra h
            simp [h] at hvalA
            omega
          have hltB : b'.val < p.i.val := by
            by_contra h
            simp [h] at hvalB
            omega
          simp only [ite_eq_left hltA, ite_eq_left hltB] at hvalA hvalB
          omega
      have hseq : dS = swapAdjacent (R := R) d a' b' := by
        funext j
        by_cases hja : j = a'
        · subst j
          show q (es0 (p.i.succAbove a')) =
            swapAdjacent (R := R) d a' b' a'
          rw [ha', hcastSwap]
          have hleft : q (swapAdjacent (R := R) e0 a0 b0 a0) =
              q (e0 b0) := by simp [swapAdjacent]
          have hab' : a' ≠ b' := by
            intro h
            have := congrArg Fin.val h
            omega
          have hright : swapAdjacent (R := R) d a' b' a' = d b' := by
            simp [swapAdjacent]
          have hdb : d b' = q (e0 b0) := by simp [d, hb']
          calc
            q (swapAdjacent (R := R) e0 a0 b0 a0) = q (e0 b0) := hleft
            _ = d b' := hdb.symm
            _ = swapAdjacent (R := R) d a' b' a' := hright.symm
        · by_cases hjb : j = b'
          · subst j
            show q (es0 (p.i.succAbove b')) =
              swapAdjacent (R := R) d a' b' b'
            rw [hb', hcastSwap]
            have hleft : q (swapAdjacent (R := R) e0 a0 b0 b0) =
                q (e0 a0) := by simp [swapAdjacent, hab0.symm]
            have hbaNe : b' ≠ a' := by
              intro h
              have := congrArg Fin.val h
              omega
            have hright : swapAdjacent (R := R) d a' b' b' = d a' := by
              simp [swapAdjacent, hbaNe]
            have hda : d a' = q (e0 a0) := by simp [d, ha']
            calc
              q (swapAdjacent (R := R) e0 a0 b0 b0) = q (e0 a0) := hleft
              _ = d a' := hda.symm
              _ = swapAdjacent (R := R) d a' b' b' := hright.symm
          · have hka : p.i.succAbove j ≠ a0 := by
              intro h
              apply hja
              exact Fin.succAbove_right_injective (h.trans ha'.symm)
            have hkb : p.i.succAbove j ≠ b0 := by
              intro h
              apply hjb
              exact Fin.succAbove_right_injective (h.trans hb'.symm)
            show q (es0 (p.i.succAbove j)) =
              swapAdjacent (R := R) d a' b' j
            rw [hcastSwap]
            simp [d, swapAdjacent, hka, hkb, hja, hjb]
      have hdSwap : IsAdmissibleSequence (R := R)
          (swapAdjacent (R := R) d a' b') := by
        rwa [← hseq]
      have hrel0 : ∀ r, r ∈ IsLocalRing.maximalIdeal R →
          r • e0 a0 ∈ spanBefore (R := R) e0 b0 := by
        intro r hr
        have h := (spanBefore_cast_mem hlen e.1 b (r • e.1 a)).mp (ha r hr)
        simpa [e0, a0, b0] using h
      have hcond : ∀ r, r ∈ IsLocalRing.maximalIdeal R →
          r • d a' ∈ spanBefore (R := R) d b' := by
        intro r hr
        have hm : q (r • e0 a0) ∈ (spanBefore (R := R) e0 b0).map q :=
          Submodule.mem_map.mpr ⟨r • e0 a0, hrel0 r hr, rfl⟩
        have hmap := map_spanBefore_le_of_pivot q f hqf e0 p b'
        have hm' : r • q (e0 a0) ∈
            (spanBefore (R := R) e0 (p.i.succAbove b')).map q := by
          simpa [hb'] using (show r • q (e0 a0) ∈
            (spanBefore (R := R) e0 b0).map q by simpa using hm)
        have hmem := hmap hm'
        simpa [d, ha'] using hmem
      have hsymbol := symbol_swap ⟨d, hd⟩ a' b' hba' hcond hdSwap
      have hsub : (⟨swapAdjacent (R := R) d a' b', hdSwap⟩ : AdmissibleSequence R Q) =
          ⟨dS, hdS⟩ := by
        exact Subtype.ext hseq.symm
      have hOldSeq : (⟨fun j => q (e.1 (Fin.cast hlen (p.i.succAbove j))),
          admissible_delete_quotient q f hqf e0 he0 p.i p.unit p.x
            p.decomp p.earlier⟩ : AdmissibleSequence R Q) = ⟨d, hd⟩ := by
        apply Subtype.ext
        rfl
      have hNewSeq : (⟨fun j => q (es.1 (Fin.cast hlen (pS.i.succAbove j))),
          admissible_delete_quotient q f hqf es0 hes0 pS.i pS.unit pS.x
            pS.decomp pS.earlier⟩ : AdmissibleSequence R Q) = ⟨dS, hdS⟩ := by
        apply Subtype.ext
        rfl
      rw [hqOld, hqNew, hOldSeq, hNewSeq]
      have hcoeff : (-1 : IsLocalRing.ResidueField R) ^ p.i.val *
          IsLocalRing.residue R p.unit =
          (-1 : IsLocalRing.ResidueField R) ^ pS.i.val *
            IsLocalRing.residue R pS.unit := by simp [pS]
      rw [hcoeff]
      have hsymbol' : symbol ⟨d, hd⟩ = -symbol ⟨dS, hdS⟩ := by
        have hsym : symbol ⟨d, hd⟩ =
            -symbol ⟨swapAdjacent (R := R) d a' b', hdSwap⟩ := by
          simpa [swapAdjacent] using hsymbol
        rwa [hsub] at hsym
      calc
        ((-1 : IsLocalRing.ResidueField R) ^ pS.i.val *
            IsLocalRing.residue R pS.unit) • symbol ⟨d, hd⟩ =
          ((-1 : IsLocalRing.ResidueField R) ^ pS.i.val *
            IsLocalRing.residue R pS.unit) • (-symbol ⟨dS, hdS⟩) :=
          congrArg (fun z : determinant R Q =>
            ((-1 : IsLocalRing.ResidueField R) ^ pS.i.val *
              IsLocalRing.residue R pS.unit) • z) hsymbol'
        _ = -((( -1 : IsLocalRing.ResidueField R) ^ pS.i.val *
              IsLocalRing.residue R pS.unit) • symbol ⟨dS, hdS⟩) := by simp
    · have hpLower : b0.val ≤ p.i.val := by
        have hh := not_or.mp hout
        omega
      have hpUpper : p.i.val ≤ a0.val := by
        have hh := not_or.mp hout
        omega
      let pS := choosePivotEntry es0 hes0 f hf0 hfspanS
      let pSswap : PivotUnitEntry (R := R)
          (swapAdjacent (R := R) e0 a0 b0) f := {
        i := pS.i
        unit := pS.unit
        x := pS.x
        decomp := by rw [← hcastSwap]; exact pS.decomp
        earlier := by rw [← hcastSwap]; exact pS.earlier
        pivotMem := by rw [← hcastSwap]; exact pS.pivotMem
        pivotMin := by rw [← hcastSwap]; exact pS.pivotMin
      }
      have hbound := pivotIndex_swapAdjacent_bounds e0 f p a0 b0 hba0
        hpLower hpUpper pSswap
      rcases hbound with ⟨hSlo, hShi⟩
      have hpSlo : b0.val ≤ pS.i.val := by
        dsimp [pSswap] at hSlo
        exact hSlo
      have hpShi : pS.i.val ≤ a0.val := by
        dsimp [pSswap] at hShi
        exact hShi
      have hpSpos : pS.i = b0 ∨ pS.i = a0 := by
        have hv : pS.i.val = b0.val ∨ pS.i.val = a0.val := by
          omega
        rcases hv with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      have hqNew := quotientSymbol_eq_pivot R M Q q f hf0 hqf hlen es pS
      let d : Fin n → Q := fun j => q (e0 (p.i.succAbove j))
      let dS : Fin n → Q := fun j => q (es0 (pS.i.succAbove j))
      have hd : IsAdmissibleSequence (R := R) d :=
        admissible_delete_quotient q f hqf e0 he0 p.i p.unit p.x p.decomp p.earlier
      have hdS : IsAdmissibleSequence (R := R) dS :=
        admissible_delete_quotient q f hqf es0 hes0 pS.i pS.unit pS.x pS.decomp pS.earlier
      obtain ⟨k, hbk, hak⟩ := exists_adjacent_delete_index a0 b0 hba0
      have hOld : quotientSymbol R M Q q f hf0 hqf hlen e =
          ((-1 : IsLocalRing.ResidueField R) ^ p.i.val *
            IsLocalRing.residue R p.unit) • symbol ⟨d, hd⟩ := by
        simpa [d, e0] using hqOld
      have hNew : quotientSymbol R M Q q f hf0 hqf hlen es =
          ((-1 : IsLocalRing.ResidueField R) ^ pS.i.val *
            IsLocalRing.residue R pS.unit) • symbol ⟨dS, hdS⟩ := by
        simpa [dS, es0] using hqNew
      by_cases hpib : p.i = b0
      · rcases hpSpos with hpSb | hpSa
        · have hpSx : pS.x ∈ spanBefore (R := R) e0 a0 := by
            have hprev : pS.x ∈ spanBefore (R := R) es0 b0 := by
              simpa [hpSb] using pS.earlier
            exact hmonoE (hbeforeSwap ▸ hprev)
          have hidx : p.i.succAbove k = a0 := by
            rw [hpib, ← hbk, Fin.succAbove_castSucc_self, hak]
          have hqa : q (e0 a0) ∈ spanBefore (R := R) d k := by
            have hqeq : q (e0 a0) = q pS.x := by
              rw [← hentryA, ← hpSb, pS.decomp, map_add, map_smul, hqf]
              simp
            have hmap := map_spanBefore_le_of_pivot q f hqf e0 p k
            have hmem : q pS.x ∈
                (spanBefore (R := R) e0 (p.i.succAbove k)).map q :=
              Submodule.mem_map.mpr ⟨pS.x, by simpa [hidx] using hpSx, rfl⟩
            have hmem' := hmap hmem
            simpa [hqeq] using hmem'
          have hddep : d k ∈ spanBefore (R := R) d k := by
            simpa [d, hidx] using hqa
          have hzero : symbol ⟨d, hd⟩ = 0 :=
            symbol_eq_zero_of_mem_spanBefore ⟨d, hd⟩ k hddep
          have hpx : p.x ∈ spanBefore (R := R) es0 a0 := by
            have hprev : p.x ∈ spanBefore (R := R) e0 b0 := by
              simpa [hpib] using p.earlier
            exact hmonoES (hbeforeSwap.symm ▸ hprev)
          have hidxS : pS.i.succAbove k = a0 := by
            rw [hpSb, ← hbk, Fin.succAbove_castSucc_self, hak]
          have hqb : q (es0 a0) ∈ spanBefore (R := R) dS k := by
            have hqeq : q (es0 a0) = q p.x := by
              rw [hentryB, ← hpib, p.decomp, map_add, map_smul, hqf]
              simp
            have hmap := map_spanBefore_le_of_pivot q f hqf es0 pS k
            have hmem : q p.x ∈
                (spanBefore (R := R) es0 (pS.i.succAbove k)).map q :=
              Submodule.mem_map.mpr ⟨p.x, by simpa [hidxS] using hpx, rfl⟩
            have hmem' := hmap hmem
            simpa [hqeq] using hmem'
          have hdSdep : dS k ∈ spanBefore (R := R) dS k := by
            simpa [dS, hidxS] using hqb
          have hzeroS : symbol ⟨dS, hdS⟩ = 0 :=
            symbol_eq_zero_of_mem_spanBefore ⟨dS, hdS⟩ k hdSdep
          rw [hOld, hNew, hzero, hzeroS]
          simp
        · have hseqFun := swapAdjacent_delete_left (R := R) (M := M)
            e0 a0 b0 hba0 k hbk hak
          have hseq : d = dS := by
            funext j
            dsimp [d, dS]
            rw [hpib, hpSa, hcastSwap]
            exact congrArg q (congrFun hseqFun j)
          have hpX : p.x ∈ spanBefore (R := R) es0 a0 := by
            have hpBefore : p.x ∈ spanBefore (R := R) e0 b0 := by
              simpa [hpib] using p.earlier
            exact hmonoES (hbeforeSwap.symm ▸ hpBefore)
          have hunitResidue : IsLocalRing.residue R (p.unit : R) =
              IsLocalRing.residue R (pS.unit : R) :=
            residue_eq_of_smul_add_eq_smul_add (spanBefore (R := R) es0 a0)
              (by rw [← p.decomp, ← pS.decomp, hpib, hpSa, hentryB]) hpX
              (by simpa [hpSa] using pS.earlier) (by simpa [hpSa] using pS.pivotMin)
          have hsub : (⟨d, hd⟩ : AdmissibleSequence R Q) = ⟨dS, hdS⟩ := by
            exact Subtype.ext hseq
          have hcoeff : ((-1 : IsLocalRing.ResidueField R) ^ p.i.val *
              IsLocalRing.residue R p.unit) = -
                (((-1 : IsLocalRing.ResidueField R) ^ pS.i.val) *
                  IsLocalRing.residue R pS.unit) := by
            rw [hpib, hpSa, hunitResidue]
            have haVal : a0.val = b0.val + 1 := by omega
            rw [haVal, pow_succ]
            ring
          rw [hOld, hNew]
          rw [hsub]
          rw [hcoeff]
          simp
      · have hpia : p.i = a0 := by
          have hv : p.i.val = a0.val := by omega
          exact Fin.ext hv
        rcases hpSpos with hpSb | hpSa
        · have hseqFun := swapAdjacent_delete_right (R := R) (M := M)
            e0 a0 b0 hba0 k hbk hak
          have hseq : d = dS := by
            funext j
            dsimp [d, dS]
            rw [hpia, hpSb, hcastSwap]
            exact congrArg q (congrFun hseqFun j)
          have hpSprev : pS.x ∈ spanBefore (R := R) e0 b0 := by
            have hprev : pS.x ∈ spanBefore (R := R) es0 b0 := by
              simpa [hpSb] using pS.earlier
            exact hbeforeSwap ▸ hprev
          have hunitResidue : IsLocalRing.residue R (p.unit : R) =
              IsLocalRing.residue R (pS.unit : R) :=
            residue_eq_of_smul_add_eq_smul_add (spanBefore (R := R) e0 a0)
              (by rw [← p.decomp, ← pS.decomp, hpia, hpSb, hentryA])
              (by simpa [hpia] using p.earlier) (hmonoE hpSprev) (by simpa [hpia] using p.pivotMin)
          have hsub : (⟨d, hd⟩ : AdmissibleSequence R Q) = ⟨dS, hdS⟩ := by
            exact Subtype.ext hseq
          have hcoeff : ((-1 : IsLocalRing.ResidueField R) ^ p.i.val *
              IsLocalRing.residue R p.unit) = -
                (((-1 : IsLocalRing.ResidueField R) ^ pS.i.val) *
                  IsLocalRing.residue R pS.unit) := by
            rw [hpia, hpSb, hunitResidue]
            have haVal : a0.val = b0.val + 1 := by omega
            rw [haVal, pow_succ]
            ring
          rw [hOld, hNew, hsub, hcoeff]
          simp
        · have hidx : p.i.succAbove k = b0 := by
            rw [hpia, ← hak, Fin.succAbove_succ_self, hbk]
          have hidxS : pS.i.succAbove k = b0 := by
            rw [hpSa, ← hak, Fin.succAbove_succ_self, hbk]
          have hpEarlier : p.x ∈ spanBefore (R := R) e0 a0 := by
            simpa [hpia] using p.earlier
          have hpSpan : p.x ∈ Submodule.span R
              (insert (e0 b0) (e0 '' Set.Iio b0)) := by
            rwa [← spanBefore_succAdjacent e0 a0 b0 hba0]
          obtain ⟨μ, y, hy, hpx⟩ := Submodule.mem_span_insert.mp hpSpan
          have hyP : y ∈ spanBefore (R := R) e0 b0 := by
            simpa using hy
          have hpSEarlier : pS.x ∈ spanBefore (R := R) es0 a0 := by
            simpa [hpSa] using pS.earlier
          have hpSSpan : pS.x ∈ Submodule.span R
              (insert (es0 b0) (es0 '' Set.Iio b0)) := by
            rwa [← spanBefore_succAdjacent es0 a0 b0 hba0]
          obtain ⟨ν, z, hz, hpSx⟩ := Submodule.mem_span_insert.mp hpSSpan
          have hzES : z ∈ spanBefore (R := R) es0 b0 := by simpa using hz
          have hzP : z ∈ spanBefore (R := R) e0 b0 := hbeforeSwap ▸ hzES
          have hmonoOld : (spanBefore (R := R) e0 b0).map q ≤
              spanBefore (R := R) d k :=
            map_spanBefore_before_pivot_le_deletedPrefix q e0 p k b0 hidx
              (by omega)
          have hmonoNew : (spanBefore (R := R) es0 b0).map q ≤
              spanBefore (R := R) dS k :=
            map_spanBefore_before_pivot_le_deletedPrefix q es0 pS k b0 hidxS
              (by omega)
          have hqyOld : q y ∈ spanBefore (R := R) d k := by
            apply hmonoOld
            exact Submodule.mem_map.mpr ⟨y, hyP, rfl⟩
          have hqzOld : q z ∈ spanBefore (R := R) d k := by
            apply hmonoOld
            exact Submodule.mem_map.mpr ⟨z, hzP, rfl⟩
          have hqzNew : q z ∈ spanBefore (R := R) dS k := by
            apply hmonoNew
            exact Submodule.mem_map.mpr ⟨z, hzES, rfl⟩
          have hdecompA : e0 a0 = (p.unit : R) • f +
              (↑μ : R) • e0 b0 + y := by
            rw [← hpia, p.decomp, hpx]
            rw [add_assoc]
          have hdecompB : e0 b0 = (pS.unit : R) • f +
              (↑ν : R) • e0 a0 + z := by
            calc
              e0 b0 = es0 a0 := hentryB.symm
              _ = (pS.unit : R) • f + pS.x := by rw [← hpSa]; exact pS.decomp
              _ = (pS.unit : R) • f + (↑ν : R) • e0 a0 + z := by
                rw [hpSx, hentryA]
                abel
          have hqA : q (e0 a0) = (↑μ : R) • q (e0 b0) + q y := by
            rw [hdecompA, map_add, map_add, map_smul, hqf]
            simp
          have hqB : q (e0 b0) = (↑ν : R) • q (e0 a0) + q z := by
            rw [hdecompB, map_add, map_add, map_smul, hqf]
            simp
          have hfun : dS = Function.update d k (q (e0 a0)) := by
            have hidxA : a0.succAbove k = b0 := by simpa [hpia] using hidx
            funext j
            by_cases hj : j = k
            · subst j
              simp [Function.update_self, d, dS, hidxS, hentryA]
            · have hja : a0.succAbove j ≠ a0 := Fin.succAbove_ne a0 j
              have hjb : a0.succAbove j ≠ b0 := by
                intro heq
                apply hj
                exact Fin.succAbove_right_injective (heq.trans hidxA.symm)
              simp [d, dS, Function.update_of_ne hj, hpia, hpSa, hcastSwap,
                swapAdjacent, hjb]
          have hprior : spanBefore (R := R) d k = spanBefore (R := R) dS k := by
            rw [spanBefore_eq_initialSpan, hfun, spanBefore_eq_initialSpan]
            exact initialSpan_update_eq_of_le d k (q (e0 a0)) (Nat.le_refl _)
          have hqyNew : q y ∈ spanBefore (R := R) dS k := by
            apply hmonoNew
            exact Submodule.mem_map.mpr ⟨y, hbeforeSwap.symm ▸ hyP, rfl⟩
          have hzeroBoth : IsLocalRing.residue R (↑μ : R) = 0 →
              symbol ⟨d, hd⟩ = 0 ∧ symbol ⟨dS, hdS⟩ = 0 := by
            intro hμzero
            have hμmax : (↑μ : R) ∈ IsLocalRing.maximalIdeal R :=
              (IsLocalRing.residue_eq_zero_iff _).mp hμzero
            have hμeb : (↑μ : R) • e0 b0 ∈ spanBefore (R := R) e0 b0 :=
              he0 b0 (↑μ : R) hμmax
            have hμqeb : (↑μ : R) • q (e0 b0) ∈ spanBefore (R := R) d k := by
              have hmem := hmonoOld
                (Submodule.mem_map.mpr ⟨(↑μ : R) • e0 b0, hμeb, rfl⟩)
              simpa only [map_smul] using hmem
            have hqAprev : q (e0 a0) ∈ spanBefore (R := R) d k := by
              rw [hqA]
              exact (spanBefore (R := R) d k).add_mem hμqeb hqyOld
            have hdDep : d k ∈ spanBefore (R := R) d k := by
              have hkval : d k = q (e0 b0) := by simp [d, hidx]
              rw [hkval, hqB]
              simpa [d, hidx] using
                (spanBefore (R := R) d k).add_mem
                  ((spanBefore (R := R) d k).smul_mem (↑ν : R) hqAprev) hqzOld
            have hqAprevS : q (e0 a0) ∈ spanBefore (R := R) dS k :=
              hprior ▸ hqAprev
            have hdSDep : dS k ∈ spanBefore (R := R) dS k := by
              simpa [dS, hidxS, hentryA] using hqAprevS
            exact ⟨symbol_eq_zero_of_mem_spanBefore ⟨d, hd⟩ k hdDep,
              symbol_eq_zero_of_mem_spanBefore ⟨dS, hdS⟩ k hdSDep⟩
          by_cases hμ : (↑μ : R) ∈ IsLocalRing.maximalIdeal R
          · have hμzero : IsLocalRing.residue R (↑μ : R) = 0 :=
              (IsLocalRing.residue_eq_zero_iff _).2 hμ
            obtain ⟨hzOld, hzNew⟩ := hzeroBoth hμzero
            rw [hOld, hNew, hzOld, hzNew]
            simp
          · have hμunit : IsUnit (↑μ : R) := by
              by_contra hnot
              exact hμ hnot
            obtain ⟨uμ, huμ⟩ := hμunit
            have hrel : dS k = (↑uμ : R) • d k + q y := by
              calc
                dS k = q (e0 a0) := by simp [dS, hidxS, hentryA]
                _ = (↑μ : R) • q (e0 b0) + q y := hqA
                _ = (↑uμ : R) • d k + q y := by rw [huμ]; simp [d, hidx]
            have hupdate : Function.update dS k (q (e0 b0)) = d := by
              rw [hfun]
              simp [d, hidx]
            have hadm : IsAdmissibleSequence (R := R)
                (Function.update dS k (q (e0 b0))) := by
              rwa [hupdate]
            have hsymbolChange : symbol ⟨dS, hdS⟩ =
                IsLocalRing.residue R uμ • symbol
                  ⟨Function.update dS k (q (e0 b0)), hadm⟩ :=
              symbol_unitChange ⟨dS, hdS⟩ k uμ (q (e0 b0)) (q y)
                (by simpa [d, hidx] using hrel) hqyNew hadm
            have hsub : (⟨Function.update dS k (q (e0 b0)), hadm⟩ :
                AdmissibleSequence R Q) = ⟨d, hd⟩ := by
              exact Subtype.ext hupdate
            rw [hsub] at hsymbolChange
            have hcoeffResidue : IsLocalRing.residue R (p.unit : R) = -
                (IsLocalRing.residue R (↑μ : R) *
                  IsLocalRing.residue R (pS.unit : R)) := by
              by_contra hne
              have hsum : IsLocalRing.residue R
                  ((p.unit : R) + (↑μ : R) * (pS.unit : R)) ≠ 0 := by
                rw [map_add, map_mul]
                intro hz
                exact hne ((eq_neg_iff_add_eq_zero).2 hz)
              have hnot : (p.unit : R) + (↑μ : R) * (pS.unit : R) ∉
                  IsLocalRing.maximalIdeal R := by
                intro hm
                exact hsum ((IsLocalRing.residue_eq_zero_iff _).2 hm)
              have hunitAlpha : IsUnit
                  ((p.unit : R) + (↑μ : R) * (pS.unit : R)) := by
                by_contra hbad
                exact hnot hbad
              obtain ⟨uα, huα⟩ := hunitAlpha
              have huf : (p.unit : R) • f =
                  e0 a0 - (↑μ : R) • e0 b0 - y := by
                rw [hdecompA]
                abel
              have hvsf : (pS.unit : R) • f =
                  e0 b0 - (↑ν : R) • e0 a0 - z := by
                rw [hdecompB]
                abel
              have hdecompAlpha : ((p.unit : R) + (↑μ : R) * (pS.unit : R)) • f =
                  e0 a0 - ((↑μ : R) * (↑ν : R)) • e0 a0 -
                    (↑μ : R) • z - y := by
                calc
                  _ = (p.unit : R) • f + (↑μ : R) • ((pS.unit : R) • f) := by
                    rw [add_smul, mul_smul]
                  _ = (e0 a0 - (↑μ : R) • e0 b0 - y) +
                      (↑μ : R) • (e0 b0 - (↑ν : R) • e0 a0 - z) := by
                    rw [huf, hvsf]
                  _ = e0 a0 - ((↑μ : R) * (↑ν : R)) • e0 a0 -
                        (↑μ : R) • z - y := by
                    simp only [smul_sub, smul_smul]
                    abel
              have hentryA_mem : e0 a0 ∈ spanBefore (R := R) es0 a0 := by
                simpa [hentryA] using
                  (Submodule.subset_span ⟨b0, hbLtA, rfl⟩ : es0 b0 ∈ spanBefore (R := R) es0 a0)
              have hzA : z ∈ spanBefore (R := R) es0 a0 := hmonoES (hbeforeSwap.symm ▸ hzP)
              have hyA : y ∈ spanBefore (R := R) es0 a0 := hmonoES (hbeforeSwap.symm ▸ hyP)
              have hαmem : ((p.unit : R) + (↑μ : R) * (pS.unit : R)) • f ∈
                  spanBefore (R := R) es0 a0 := by
                rw [hdecompAlpha]
                exact Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _ hentryA_mem
                  (Submodule.smul_mem _ _ hentryA_mem)) (Submodule.smul_mem _ _ hzA)) hyA
              have hmul : (↑uα⁻¹ : R) *
                  ((p.unit : R) + (↑μ : R) * (pS.unit : R)) = 1 := by
                rw [← huα]
                exact Units.inv_mul uα
              have hfprev : f ∈ spanBefore (R := R) es0 a0 := by
                have hm := (spanBefore (R := R) es0 a0).smul_mem
                  (↑uα⁻¹ : R) hαmem
                rwa [smul_smul, hmul, one_smul] at hm
              exact pS.pivotMin (by simpa [hpSa] using hfprev)
            have hcoeff : ((-1 : IsLocalRing.ResidueField R) ^ p.i.val *
                IsLocalRing.residue R p.unit) = -
                  (((-1 : IsLocalRing.ResidueField R) ^ pS.i.val) *
                    IsLocalRing.residue R pS.unit * IsLocalRing.residue R uμ) := by
              rw [hpia, hpSa, huμ, hcoeffResidue]
              ring
            rw [hOld, hNew]
            rw [hsymbolChange]
            rw [hcoeff]
            simp [smul_smul, mul_comm]
  · have hfnotS : f ∉ Submodule.span R (Set.range es0) := by
      rwa [hspanEq]
    have hfnot : f ∉ Submodule.span R
        (Set.range (fun i : Fin (moduleLength R Q + 1) =>
          e.1 (Fin.cast hlen i))) := by simpa [e0] using hfspan
    have hfnotS' : f ∉ Submodule.span R
        (Set.range (fun i : Fin (moduleLength R Q + 1) =>
          es.1 (Fin.cast hlen i))) := by simpa [es0] using hfnotS
    rw [quotientSymbol_zero_of_not_span R M Q q f hf0 hqf hlen e hfnot,
      quotientSymbol_zero_of_not_span R M Q q f hf0 hqf hlen es hfnotS']
    simp

end Module.FiniteLength

end
