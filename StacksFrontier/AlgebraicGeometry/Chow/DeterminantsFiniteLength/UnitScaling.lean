module

public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Functor

/-!
# The determinant functor on scaling by a unit

Multiplication by a unit of the base ring is an automorphism of a finite-length module, and
the determinant functor sends it to multiplication by the residue of that unit raised to the
length of the module.

## Main results

* `Module.FiniteLength.determinantFunctor_map_unit_smul` computes the determinant of the
  automorphism given by scaling by a unit.

## Implementation notes

Scaling an admissible sequence entrywise by a unit leaves the span of the entries preceding
each index unchanged, hence leaves admissibility unchanged, and each of the `l` entries
contributes one factor of the residue of the unit to the symbol by the unit-change
relation. The automorphism is presented as a morphism of the groupoid of finite-length
modules, and its image under the determinant functor is read off through the functor's
`mapLinearEquiv` component.

## References

* [Stacks Project, Tag 02PD](https://stacks.math.columbia.edu/tag/02PD)
-/

@[expose] public section

noncomputable section

open CategoryTheory
namespace Module.FiniteLength
universe u v

/-- The sequence obtained by scaling every entry by a unit of the base ring. -/
private def scaledSequence {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] {n : ℕ}
    (e : Fin n → M) (a : Rˣ) (S : Finset (Fin n)) : Fin n → M :=
  fun i => if i ∈ S then (a : R) • e i else e i

/-- Scaling every entry by a unit does not change the span of the entries preceding an
index. -/
private theorem spanBefore_scaledSequence_eq {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (e : Fin n → M) (a : Rˣ) (S : Finset (Fin n)) (j : Fin n) :
    spanBefore (R := R) (scaledSequence e a S) j = spanBefore (R := R) e j := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro y ⟨i, hi, rfl⟩
    by_cases his : i ∈ S
    · simp only [scaledSequence, ite_eq_left his]
      exact Submodule.smul_mem _ _ (Submodule.subset_span
        (show e i ∈ e '' Set.Iio j from ⟨i, hi, rfl⟩))
    · simpa [scaledSequence, his] using
        (Submodule.subset_span (show e i ∈ e '' Set.Iio j from ⟨i, hi, rfl⟩))
  · apply Submodule.span_le.2
    rintro y ⟨i, hi, rfl⟩
    have hmem : scaledSequence e a S i ∈ spanBefore (R := R) (scaledSequence e a S) j :=
      Submodule.subset_span
        (show scaledSequence e a S i ∈ scaledSequence e a S '' Set.Iio j from ⟨i, hi, rfl⟩)
    by_cases his : i ∈ S
    · rw [show e i = ((↑(a⁻¹) : R)) • scaledSequence e a S i by
        simp [scaledSequence, his, smul_smul]]
      exact Submodule.smul_mem _ _ hmem
    · simpa [scaledSequence, his] using hmem

/-- Scaling every entry of an admissible sequence by a unit keeps it admissible. -/
private theorem scaledSequence_admissible {R : Type u} {M : Type v}
    [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (e : Fin n → M) (he : IsAdmissibleSequence (R := R) e)
    (a : Rˣ) (S : Finset (Fin n)) :
    IsAdmissibleSequence (R := R) (scaledSequence e a S) := by
  intro j r hr
  rw [spanBefore_scaledSequence_eq e a S j]
  by_cases hjs : j ∈ S
  · simp only [scaledSequence, ite_eq_left hjs]
    rw [smul_comm r]
    exact Submodule.smul_mem _ _ (he j r hr)
  · simpa [scaledSequence, hjs] using he j r hr

/-- The symbol of a sequence scaled by a unit is the original symbol times the residue of the
unit raised to the length of the module: the unit-change relation contributes one factor
per entry. -/
private theorem symbol_scaledSequence {R : Type u} {M : Type v}
    [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    (e : AdmissibleSequence R M) (a : Rˣ)
    (S : Finset (Fin (moduleLength R M))) :
    symbol ⟨scaledSequence e.1 a S, scaledSequence_admissible e.1 e.2 a S⟩ =
      (IsLocalRing.residue R a ^ S.card) • symbol e := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      have heq : (⟨scaledSequence e.1 a ∅,
          scaledSequence_admissible e.1 e.2 a ∅⟩ : AdmissibleSequence R M) = e := by
        apply Subtype.ext
        funext i
        simp [scaledSequence]
      rw [heq]
      simp
  | @insert i S hi ih =>
      let eS : AdmissibleSequence R M :=
        ⟨scaledSequence e.1 a S, scaledSequence_admissible e.1 e.2 a S⟩
      let eIns : AdmissibleSequence R M :=
        ⟨scaledSequence e.1 a (insert i S),
          scaledSequence_admissible e.1 e.2 a (insert i S)⟩
      have hentry : eIns.1 i = (a : R) • eS.1 i := by
        simp [eIns, eS, scaledSequence, hi]
      have hbase : Function.update eIns.1 i (eS.1 i) = eS.1 := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [Function.update]
        · simp [Function.update, hji, eIns, eS, scaledSequence, Finset.mem_insert]
      have hadm : IsAdmissibleSequence (R := R)
          (Function.update eIns.1 i (eS.1 i)) := by
        rw [hbase]
        exact eS.2
      have hbaseSubtype :
          (⟨Function.update eIns.1 i (eS.1 i), hadm⟩ : AdmissibleSequence R M) = eS :=
        Subtype.ext hbase
      have hstep := symbol_unitChange eIns i a (eS.1 i) 0 (by simpa using hentry)
        (by simp) hadm
      have hsym : symbol ⟨scaledSequence e.1 a (insert i S),
          scaledSequence_admissible e.1 e.2 a (insert i S)⟩ = symbol eIns := rfl
      rw [hbaseSubtype] at hstep
      rw [hsym, hstep, ih]
      simp [hi, pow_succ, smul_smul, mul_comm]

/-- Multiplication by a unit on a finite-length module acts on its determinant
by the corresponding power of the residue of that unit. -/
@[stacks 02PD]
public theorem determinantFunctor_map_unit_smul
    {R : Type u} [CommRing R] [IsLocalRing R]
    (X : FiniteLengthModuleIso.{u, v} R) (a : Rˣ) (f : X ⟶ X)
    (hf : ∀ m : X.of.obj, f.iso.hom.hom.hom m = (a : R) • m)
    (x : determinant R X.of.obj) :
    (determinantFunctor R).mapLinearEquiv f x =
      (IsLocalRing.residue R a ^ moduleLength R X.of.obj) • x := by
  classical
  let c := IsLocalRing.residue R a ^ moduleLength R X.of.obj
  have hsymbol (e : AdmissibleSequence R X.of.obj) :
      (determinantFunctor R).mapLinearEquiv f (symbol e) = c • symbol e := by
    have hseq :
        (fun i ↦ f.iso.hom.hom.hom
          (e.1 (Fin.cast ((determinantFunctor R).map_length f).symm i))) =
          scaledSequence e.1 a Finset.univ := by
      funext i
      simp only [scaledSequence, Finset.mem_univ, ite_eq_left]
      rw [hf, Fin.cast_eq_self]
    have hsub :
        (⟨fun i ↦ f.iso.hom.hom.hom
          (e.1 (Fin.cast ((determinantFunctor R).map_length f).symm i)),
          (determinantFunctor R).map_admissible f e⟩ : AdmissibleSequence R X.of.obj) =
          ⟨scaledSequence e.1 a Finset.univ,
            scaledSequence_admissible e.1 e.2 a Finset.univ⟩ :=
      Subtype.ext hseq
    rw [(determinantFunctor R).map_symbol f e, hsub]
    simpa [c, moduleLength] using symbol_scaledSequence e a Finset.univ
  refine Submodule.Quotient.induction_on (determinantRelations R X.of.obj) x fun z => ?_
  induction z using Finsupp.induction with
  | zero => simp
  | @single_add e b z he hb ih =>
      have hsingle :
          (Submodule.Quotient.mk (Finsupp.single e b) : determinant R X.of.obj) =
            b • symbol e := by
        rw [symbol, ← Submodule.Quotient.mk_smul]
        congr 1
        ext i
        simp [Finsupp.smul_single]
      simp only [Submodule.Quotient.mk_add, map_add, ih]
      rw [hsingle, map_smul, hsymbol]
      simp [smul_smul, mul_comm, c]

end Module.FiniteLength

end
