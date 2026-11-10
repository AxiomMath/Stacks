module

public import Mathlib.RingTheory.SimpleModule.Rank
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.InitialSpan

/-!
# Spanning admissible sequences exist

Every finite-length module over a local ring has an admissible sequence that spans it. This
is what makes the determinant nonzero, and it is the starting point of every comparison of
determinants: identities between symbols are proved by exhibiting a spanning admissible
sequence and transporting it.

## Main results

* `Module.FiniteLength.exists_admissible_generator` produces a spanning admissible sequence.
* `Module.FiniteLength.maximalIdeal_smul_eq_zero_of_simple` is the fact about simple modules
  that makes the inductive step work.

## References

* [Stacks Project, Tag 02P6](https://stacks.math.columbia.edu/tag/02P6)
* [Stacks Project, Tag 02P9](https://stacks.math.columbia.edu/tag/02P9)
-/

@[expose] public section

noncomputable section

namespace Module.FiniteLength

universe u v

/-- The maximal ideal of a local ring annihilates every simple module over it. -/
public theorem maximalIdeal_smul_eq_zero_of_simple
    {R : Type u} [CommRing R] [IsLocalRing R] {V : Type v}
    [AddCommGroup V] [Module R V] [IsSimpleModule R V]
    {r : R} (hr : r ∈ IsLocalRing.maximalIdeal R) (z : V) : r • z = 0 := by
  have ha : (Module.annihilator R V).IsMaximal := IsSimpleModule.annihilator_isMaximal
  have heq : Module.annihilator R V = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal ha
  exact (Module.mem_annihilator.mp (heq ▸ hr)) z

/-- Every finite-length module over a local ring admits an admissible sequence that spans it.
The sequence is built by induction along a filtration with simple quotients: a lift of a
generator of the top simple quotient is appended to a spanning admissible sequence of the
submodule, and appending keeps admissibility because the maximal ideal kills the quotient. -/
public theorem exists_admissible_generator
    {R : Type u} [CommRing R] [IsLocalRing R] {M : Type v}
    [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    ∃ e : AdmissibleSequence R M, Submodule.span R (Set.range e.1) = ⊤ := by
  classical
  refine IsFiniteLength.rec (R := R)
    (motive := fun M _ _ _ =>
      ∃ e : AdmissibleSequence R M, Submodule.span R (Set.range e.1) = ⊤)
    ?_ ?_ hM
  · intro M _ _ hSub
    have hlen0 : moduleLength R M = 0 := by simp [moduleLength]
    refine ⟨⟨(fun _ => (0 : M)), ?_⟩, ?_⟩
    · intro i r hr
      have hi : 0 < moduleLength R M := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
      rw [hlen0] at hi
      omega
    · have hspan :
          Submodule.span R (Set.range (fun _ : Fin (moduleLength R M) => (0 : M))) = ⊥ := by
        simp
      rw [hspan]
      exact Subsingleton.elim _ _
  · intro M _ _ N _ hN ih
    obtain ⟨eN, hgenN⟩ := ih
    let n := moduleLength R ↥N
    have hex : Function.Exact N.subtype N.mkQ := by
      apply LinearMap.exact_iff.mpr
      simp [N.ker_mkQ]
    have hlen : moduleLength R M = n + 1 := by
      unfold moduleLength
      rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.subtype_injective N.mkQ_surjective hex,
        Module.length_eq_one_iff.mpr (inferInstance : IsSimpleModule R (M ⧸ N)),
        ENat.toNat_add (Module.length_ne_top_iff.mpr hN) (by simp)]
      rfl
    let _ : Nontrivial (M ⧸ N) := IsSimpleModule.nontrivial R (M ⧸ N)
    obtain ⟨q, hq⟩ : ∃ q : M ⧸ N, q ≠ 0 := exists_ne 0
    obtain ⟨x, hxq⟩ := N.mkQ_surjective q
    have hxq0 : N.mkQ x ≠ 0 := by simpa [hxq] using hq
    let e0 : Fin (n + 1) → M := Fin.snoc (fun i => (eN.1 i : M)) x
    let S : Submodule R M := Submodule.span R (Set.range e0)
    have hNmem : ∀ z : N, (z : M) ∈ S := by
      intro z
      have hz : z ∈ Submodule.span R (Set.range eN.1) := by
        rw [hgenN]
        exact Submodule.mem_top
      induction hz using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨i, rfl⟩ := hy
          exact Submodule.subset_span ⟨i.castSucc, by simp [e0, Fin.snoc_castSucc]⟩
      | zero => exact S.zero_mem
      | add z w hz hw ihz ihw => exact S.add_mem ihz ihw
      | smul a z hz ih => exact S.smul_mem a ih
    have hxS : x ∈ S := Submodule.subset_span ⟨Fin.last n, by simp [e0, Fin.snoc_last]⟩
    have hspanQ : R ∙ N.mkQ x = ⊤ :=
      (IsSimpleModule.toIsSimpleOrder.eq_bot_or_eq_top (R ∙ N.mkQ x)).resolve_left
        (Submodule.span_singleton_eq_bot.not.mpr hxq0)
    have hgen0 : S = ⊤ := by
      refine Submodule.eq_top_iff'.mpr fun y => ?_
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
        (show N.mkQ y ∈ R ∙ N.mkQ x by rw [hspanQ]; exact Submodule.mem_top)
      have hyN : y - a • x ∈ N := by
        apply (Submodule.Quotient.mk_eq_zero N).mp
        change N.mkQ (y - a • x) = 0
        rw [map_sub, map_smul, ha, sub_self]
      simpa using S.add_mem (hNmem ⟨y - a • x, hyN⟩) (S.smul_mem a hxS)
    have hadm0 : IsAdmissibleSequence (R := R) e0 := by
      intro a
      refine Fin.lastCases ?_ ?_ a
      · intro r hr
        have hrxN : r • x ∈ N := by
          apply (Submodule.Quotient.mk_eq_zero N).mp
          change N.mkQ (r • x) = 0
          rw [map_smul, maximalIdeal_smul_eq_zero_of_simple hr (N.mkQ x)]
        let rxN : N := ⟨r • x, hrxN⟩
        have hz : rxN ∈ Submodule.span R (Set.range eN.1) := by
          rw [hgenN]
          exact Submodule.mem_top
        have hmapmem : (r • x : M) ∈
            Submodule.map N.subtype (Submodule.span R (Set.range eN.1)) :=
          Submodule.mem_map.mpr ⟨rxN, hz, rfl⟩
        rw [Submodule.map_span] at hmapmem
        have hincl' : N.subtype '' Set.range eN.1 ⊆ e0 '' Set.Iio (Fin.last n) := by
          rintro y ⟨z, ⟨i, rfl⟩, rfl⟩
          exact ⟨i.castSucc, Fin.castSucc_lt_last i, by simp [e0, Fin.snoc_castSucc]⟩
        simpa only [spanBefore, e0, Fin.snoc_last] using
          Submodule.span_mono hincl' hmapmem
      · intro i r hr
        have hz := eN.2 i r hr
        have hmapmem : (r • eN.1 i : M) ∈
            Submodule.map N.subtype (spanBefore (R := R) eN.1 i) :=
          Submodule.mem_map.mpr ⟨r • eN.1 i, hz, rfl⟩
        rw [spanBefore, Submodule.map_span] at hmapmem
        have hincl : N.subtype '' (eN.1 '' Set.Iio i) ⊆
            e0 '' Set.Iio i.castSucc := by
          rintro y ⟨z, ⟨j, hj, rfl⟩, rfl⟩
          exact ⟨j.castSucc, by simpa using hj, by simp [e0, Fin.snoc_castSucc]⟩
        simpa only [spanBefore, e0, Fin.snoc_castSucc] using
          Submodule.span_mono hincl hmapmem
    let e' : Fin (moduleLength R M) → M := fun a => e0 (Fin.cast hlen a)
    have hadm' : IsAdmissibleSequence (R := R) e' := by
      intro a r hr
      have ha := hadm0 (Fin.cast hlen a) r hr
      have himage : e0 '' Set.Iio (Fin.cast hlen a) = e' '' Set.Iio a := by
        ext y
        constructor
        · rintro ⟨b, hb, rfl⟩
          exact ⟨Fin.cast hlen.symm b, by simpa [Fin.lt_def] using hb, by simp [e']⟩
        · rintro ⟨b, hb, rfl⟩
          exact ⟨Fin.cast hlen b, by simpa using hb, by simp [e']⟩
      simpa only [spanBefore, e'] using (congrArg (Submodule.span R) himage ▸ ha)
    have hrange : Set.range e' = Set.range e0 :=
      Function.Surjective.range_comp (fun b => ⟨Fin.cast hlen.symm b, by simp⟩) e0
    exact ⟨⟨e', hadm'⟩, (congrArg (Submodule.span R) hrange).trans hgen0⟩

end Module.FiniteLength

end
