module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.UniformRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicRingMap
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.Adic
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.QuotientLimit
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut

/-!
# Weakly adic rings

A linearly topologized ring is *weakly pre-adic* when the closures of the powers of a single
ideal are open and form a neighbourhood basis of zero, and *weakly adic* when it is in addition
complete and separated.  This file defines both, gives the equivalent characterisations of weak
pre-adicness, shows an adic ring is weakly adic and a weakly adic ring is admissible with a
countable basis of open ideals, and proves that completion and the completed tensor product
stay in the class.

## References

* [Stacks Project, Tag 0GXE](https://stacks.math.columbia.edu/tag/0GXE)
* [Stacks Project, Tag 0GXF](https://stacks.math.columbia.edu/tag/0GXF)
* [Stacks Project, Tag 0GXG](https://stacks.math.columbia.edu/tag/0GXG)
* [Stacks Project, Tag 0GXH](https://stacks.math.columbia.edu/tag/0GXH)
* [Stacks Project, Tag 0GXI](https://stacks.math.columbia.edu/tag/0GXI)
* [Stacks Project, Tag 0GXJ](https://stacks.math.columbia.edu/tag/0GXJ)
-/

@[expose] public section

namespace TopologicalRing

section

/-- A linearly topologized ring is *weakly pre-adic* if the closures of the powers of some
ideal are open and form a neighborhood basis at zero. -/
@[stacks 0GXE "part (1)"]
public class IsWeaklyPreAdic (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] : Prop where
  /-- There is an ideal whose closed powers form a fundamental system of open ideals. -/
  exists_ideal : ∃ I : Ideal A, (∀ n : ℕ, IsOpen ((I ^ n).topologicalClosure : Set A)) ∧
    (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ ((I ^ n).topologicalClosure : Set A))

/-- A linearly topologized ring is *weakly adic* if it is weakly pre-adic, complete, and
separated. Completeness uses the canonical uniformity of its additive topological group. -/
@[stacks 0GXE "part (2)"]
public class IsWeaklyAdic (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] : Prop extends IsWeaklyPreAdic A, T2Space A where
  /-- The additive topological group is complete for its canonical uniformity. -/
  completeSpace : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)

attribute [instance] IsWeaklyAdic.completeSpace

end

section

open Filter

universe u v


private lemma weaklyPreAdic_of_preAdmissible_open_closures
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] (I : Ideal A)
    (hI : TopologicalRing.IsIdealOfDefinition I)
    (hopen : ∀ n : ℕ, 1 ≤ n → IsOpen ((I ^ n).topologicalClosure : Set A)) :
    TopologicalRing.IsWeaklyPreAdic A := by
  refine ⟨I, ?_, ?_⟩
  · intro n
    cases n with
    | zero => simp
    | succ n => exact hopen (n + 1) (by omega)
  · refine ⟨fun U => ⟨fun hU => ?_, ?_⟩⟩
    · obtain ⟨J, hJopen, hJU⟩ :=
        (IsLinearTopology.hasBasis_open_ideal (R := A)).mem_iff.mp hU
      obtain ⟨n, hn⟩ := hI.2 J (hJopen.mem_nhds (zero_mem J))
      refine ⟨n, trivial, ?_⟩
      intro x hx
      exact hJU (closure_minimal (by simpa using hn)
        (AddSubgroup.isClosed_of_isOpen J.toAddSubgroup hJopen) hx)
    · rintro ⟨n, -, hn⟩
      cases n with
      | zero => simp [show U = Set.univ by simpa using hn]
      | succ n =>
        exact Filter.mem_of_superset
          ((hopen (n + 1) (by omega)).mem_nhds (subset_closure (zero_mem _))) hn

/-- The ring receives a taut continuous homomorphism from some pre-adic topological ring. -/
public abbrev HasTautPreAdicSource (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : Prop :=
  ∃ (A' : Type v) (ringA' : CommRing A') (topologyA' : TopologicalSpace A')
      (topologicalRingA' : IsTopologicalRing A') (linearTopologyA' : IsLinearTopology A' A'),
    let _ := ringA'
    let _ := topologyA'
    let _ := topologicalRingA'
    let _ := linearTopologyA'
    (∃ I : Ideal A', _root_.IsAdic I) ∧
      ∃ φ : A' →+* A, Continuous φ ∧ RingHom.IsTaut φ

/-- Some positive power of an ideal of definition lies in any given open ideal. -/
private lemma exists_pow_succ_le_of_isOpen {A : Type*} [CommRing A] [TopologicalSpace A]
    {I L : Ideal A} (hI : TopologicalRing.IsIdealOfDefinition I) (hL : IsOpen (L : Set A)) :
    ∃ n : ℕ, I ^ (n + 1) ≤ L := by
  obtain ⟨n, hn⟩ := hI.2 L (hL.mem_nhds (zero_mem L))
  exact ⟨n, (Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn⟩

/-- The four equivalent characterizations of a weakly pre-adic linearly topologized ring. -/
@[stacks 0GXF "weakly_pre_adic_characterizations"]
public lemma weaklyPreAdic_tfae (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] :
    List.TFAE
      [ TopologicalRing.IsWeaklyPreAdic A,
        HasTautPreAdicSource.{u, max u v} A,
        TopologicalRing.IsPreAdmissible A ∧
          ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧
            (∀ n : ℕ, 1 ≤ n → IsOpen ((I ^ n).topologicalClosure : Set A)),
        TopologicalRing.IsPreAdmissible A ∧
          (∀ I : Ideal A, TopologicalRing.IsIdealOfDefinition I →
            ∀ n : ℕ, 1 ≤ n → IsOpen ((I ^ n).topologicalClosure : Set A)) ] := by
  tfae_have 1 → 2 := by
    intro hweak
    obtain ⟨I, hopen, hbasis⟩ := hweak.exists_ideal
    let targetTopology : TopologicalSpace A := inferInstance
    let targetTopologicalRing : IsTopologicalRing A := inferInstance
    let A' := ULift.{max u v, u} A
    let e : A' ≃+* A := ULift.ringEquiv
    let J : Ideal A' := I.comap e.toRingHom
    let adic : TopologicalSpace A' := J.adicTopology
    have htop : @IsTopologicalRing A' adic _ := by
      let : TopologicalSpace A' := adic
      infer_instance
    have hlin : @IsLinearTopology A' A' _ _ _ adic := by
      let : TopologicalSpace A' := adic
      exact J.isLinearTopology
    have hsourceAdic : @_root_.IsAdic A' _ adic J := rfl
    have hsourceOpenPowers : ∀ n : ℕ, IsOpen ((J ^ n : Ideal A') : Set A') := by
      let : TopologicalSpace A' := adic
      let : IsTopologicalRing A' := htop
      exact (isAdic_iff.mp hsourceAdic).1
    have hmap : J.map e.toRingHom = I := Ideal.map_comap_eq_self_of_equiv e I
    have hmapPow (n : ℕ) : (J ^ n).map e.toRingHom = I ^ n := by
      rw [Ideal.map_pow, hmap]
    have hcont : @Continuous A' A adic targetTopology e.toRingHom := by
      have hzero : Tendsto (e : A' → A) (@nhds A' adic 0) (@nhds A targetTopology 0) := by
        rw [Filter.tendsto_def]
        intro U hU
        obtain ⟨n, -, hn⟩ := hbasis.mem_iff.mp hU
        apply J.hasBasis_nhds_zero_adic.mem_iff.mpr
        refine ⟨n, trivial, ?_⟩
        intro x hx
        apply hn
        apply subset_closure
        have hx' : e x ∈ (J ^ n).map e.toRingHom := Ideal.mem_map_of_mem _ hx
        rwa [hmapPow] at hx'
      have hzero' : ContinuousAt (e : A' → A) 0 := by
        simpa only [ContinuousAt, e.map_zero] using hzero
      exact @continuous_of_continuousAt_zero A' adic _ htop.isTopologicalAddGroup
        A (A' →+ A) _ targetTopology _ _ _ e.toAddMonoidHom hzero'
    have hmaple (L : Ideal A') (hL : @IsOpen A' adic (L : Set A')) :
        ∃ n, I ^ n ≤ L.map e.toRingHom := by
      obtain ⟨n, -, hn⟩ := J.hasBasis_nhds_zero_adic.mem_iff.mp
        (@IsOpen.mem_nhds A' adic 0 (L : Set A') hL (zero_mem L))
      refine ⟨n, ?_⟩
      rw [← hmapPow n]
      exact Ideal.map_mono hn
    have htaut : @RingHom.IsTaut A' A _ adic _ targetTopology targetTopologicalRing
        e.toRingHom := by
      constructor
      · intro L hL
        obtain ⟨n, hn⟩ := hmaple L hL
        have hcl : (I ^ n).topologicalClosure ≤
            (L.map e.toRingHom).topologicalClosure :=
          Submodule.topologicalClosure_mono hn
        have hopenL : IsOpen ((L.map e.toRingHom).topologicalClosure : Set A) :=
          Submodule.isOpen_mono hcl (hopen n)
        simpa [Ideal.coe_closure] using hopenL
      · refine Filter.HasBasis.mk ?mem
        intro U
        constructor
        · intro hU
          obtain ⟨n, -, hn⟩ := hbasis.mem_iff.mp hU
          refine ⟨J ^ n, hsourceOpenPowers n, ?_⟩
          change ((Ideal.map e.toRingHom (J ^ n)).closure : Set A) ⊆ U
          rw [hmapPow n]
          simpa only [Ideal.coe_closure, Submodule.topologicalClosure_coe] using hn
        · rintro ⟨L, hL, hLU⟩
          obtain ⟨n, hn⟩ := hmaple L hL
          have hcl : ((I ^ n).topologicalClosure : Set A) ⊆
              ((L.map e.toRingHom).closure : Set A) := by
            have hcl' := Submodule.topologicalClosure_mono hn
            have hclSets : ((I ^ n).topologicalClosure : Set A) ⊆
                ((L.map e.toRingHom).topologicalClosure : Set A) := hcl'
            simpa only [Submodule.topologicalClosure_coe, Ideal.coe_closure] using hclSets
          exact hbasis.mem_iff.mpr ⟨n, trivial, hcl.trans hLU⟩
    refine ⟨A', inferInstance, adic, htop, hlin, ?_⟩
    refine ⟨⟨J, hsourceAdic⟩, ?_⟩
    exact ⟨e.toRingHom, hcont, htaut⟩
  tfae_have 2 → 3 := by
    rintro ⟨A', ringA', topologyA', topRingA', linearTopologyA', hsource, φ, hcont, htaut⟩
    let : CommRing A' := ringA'
    let : TopologicalSpace A' := topologyA'
    let : IsTopologicalRing A' := topRingA'
    let : IsLinearTopology A' A' := linearTopologyA'
    obtain ⟨I, hIadic⟩ := hsource
    have hsourceOpenPowers : ∀ n : ℕ, IsOpen ((I ^ n : Ideal A') : Set A') :=
      (isAdic_iff.mp hIadic).1
    have hIdef : TopologicalRing.IsIdealOfDefinition I := by
      constructor
      · simpa [pow_one] using hsourceOpenPowers 1
      · intro U hU
        obtain ⟨n, -, hn⟩ := hIadic.hasBasis_nhds_zero.mem_iff.mp hU
        exact ⟨n, hn⟩
    obtain ⟨K, hK⟩ :=
      RingHom.isPreAdmissible_of_isTaut φ htaut ⟨I, hIdef⟩
    refine ⟨⟨K, hK⟩, K, hK, ?_⟩
    intro m hm
    obtain ⟨L, hLopen, hLK⟩ := htaut.2.mem_iff.mp (hK.1.mem_nhds (zero_mem K))
    obtain ⟨n, hn'⟩ := exists_pow_succ_le_of_isOpen hIdef hLopen
    let E : Ideal A := (Ideal.map φ (I ^ (n + 1))).closure
    have hEopen : IsOpen (E : Set A) := by
      simpa [E] using htaut.1 (I ^ (n + 1)) (hsourceOpenPowers (n + 1))
    have hEsub : E ≤ K := by
      intro x hx
      change x ∈ closure (Ideal.map φ (I ^ (n + 1)) : Set A) at hx
      apply hLK
      change x ∈ closure (Ideal.map φ L : Set A)
      exact closure_mono (Ideal.map_mono hn') hx
    have hbase : Ideal.map φ (I ^ (n + 1)) ≤ E := by
      intro x hx
      exact subset_closure hx
    have hmapPow : Ideal.map φ (I ^ ((n + 1) * m)) ≤ E ^ m := by
      calc
        Ideal.map φ (I ^ ((n + 1) * m)) =
            Ideal.map φ ((I ^ (n + 1)) ^ m) := by rw [pow_mul]
        _ = (Ideal.map φ (I ^ (n + 1))) ^ m := Ideal.map_pow φ _ _
        _ ≤ E ^ m := Ideal.pow_right_mono hbase m
    have hclosure : (Ideal.map φ (I ^ ((n + 1) * m))).topologicalClosure ≤
        (K ^ m).topologicalClosure :=
      Submodule.topologicalClosure_mono <| hmapPow.trans (Ideal.pow_right_mono hEsub m)
    have hsmallOpen : IsOpen
        ((Ideal.map φ (I ^ ((n + 1) * m))).topologicalClosure : Set A) := by
      simpa only [Ideal.coe_closure, Submodule.topologicalClosure_coe] using
        htaut.1 (I ^ ((n + 1) * m)) (hsourceOpenPowers ((n + 1) * m))
    exact Submodule.isOpen_mono hclosure hsmallOpen
  tfae_have 3 → 1 := by
    rintro ⟨_, I, hI, hopen⟩
    exact weaklyPreAdic_of_preAdmissible_open_closures I hI hopen
  tfae_have 3 → 4 := by
    rintro ⟨hpre, I, hI, hopen⟩
    refine ⟨hpre, ?_⟩
    intro J hJ m hm
    obtain ⟨n, hn'⟩ := exists_pow_succ_le_of_isOpen hI hJ.1
    have hpow : (I ^ ((n + 1) * m) : Ideal A) ≤ J ^ m := by
      simpa [pow_mul] using Ideal.pow_right_mono hn' m
    have hcl : (I ^ ((n + 1) * m)).topologicalClosure ≤
        (J ^ m).topologicalClosure := Submodule.topologicalClosure_mono hpow
    exact Submodule.isOpen_mono hcl
      (hopen ((n + 1) * m) (Nat.succ_le_iff.mpr
        (Nat.mul_pos (Nat.succ_pos n) (by omega))))
  tfae_have 4 → 3 := by
    rintro ⟨hpre, hall⟩
    obtain ⟨I, hI⟩ := hpre
    exact ⟨⟨I, hI⟩, I, hI, hall I hI⟩
  tfae_finish

end

section

open Filter
open scoped Topology

/-- Completion preserves the linear topology of a linearly topologized ring. -/
@[stacks 0GXF "completion_weakly_adic"]
public instance isLinearTopology_completion (A : Type*) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] :
    letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
    letI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
    IsLinearTopology (UniformSpace.Completion A) (UniformSpace.Completion A) := by
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  let : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  exact completion_linearTopology_ring

/-- The completion of a weakly pre-adic linearly topologized ring is weakly adic. -/
@[stacks 0GXF "completion_weakly_adic"]
public instance isWeaklyAdic_completion (A : Type*) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] [TopologicalRing.IsWeaklyPreAdic A] :
    letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
    letI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
    TopologicalRing.IsWeaklyAdic (UniformSpace.Completion A) := by
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  let : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  let C := UniformSpace.Completion A
  let : IsLinearTopology C C := completion_linearTopology_ring
  let hpre : TopologicalRing.IsWeaklyPreAdic C := by
    have hsource :=
      ((TopologicalRing.weaklyPreAdic_tfae.{_, 0} A).out
        1 2).mp (inferInstance : TopologicalRing.IsWeaklyPreAdic A)
    rcases hsource with ⟨A', ringA', topologyA', topologicalRingA', linearTopologyA',
      hAdic, φ, hφ, hφ_taut⟩
    let : CommRing A' := ringA'
    let : TopologicalSpace A' := topologyA'
    let : IsTopologicalRing A' := topologicalRingA'
    let : IsLinearTopology A' A' := linearTopologyA'
    apply ((TopologicalRing.weaklyPreAdic_tfae.{_, 0} C).out
      1 2).mpr
    refine ⟨A', ringA', topologyA', topologicalRingA', linearTopologyA', hAdic,
      (UniformSpace.Completion.coeRingHom : A →+* C).comp φ,
      (UniformSpace.Completion.continuous_coe A).comp hφ, ?_⟩
    exact RingHom.isTaut_comp φ _ (UniformSpace.Completion.continuous_coe A)
      hφ_taut (RingHom.isTaut_completion (A := A))
  let : TopologicalRing.IsWeaklyPreAdic C := hpre
  exact TopologicalRing.IsWeaklyAdic.mk
    (show @CompleteSpace C (IsTopologicalAddGroup.rightUniformSpace C) from by
      rw [IsUniformAddGroup.rightUniformSpace_eq]
      infer_instance)

end

section

open TopologicalRing

/-- An adic linearly topologized ring is weakly adic: the powers of an ideal of definition are
open, hence closed, hence equal to their own closures, so they witness the weakly pre-adic
condition, and completeness and separatedness are part of adicness. -/
public theorem isWeaklyAdic_of_isAdic (A : Type*) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] (hA : TopologicalRing.IsAdic A) :
    TopologicalRing.IsWeaklyAdic A := by
  obtain ⟨I, hIdef, hIadic⟩ := hA.1
  have hopen : ∀ n : ℕ, IsOpen ((I ^ n : Ideal A) : Set A) := (isAdic_iff.mp hIadic).1
  have hcl : ∀ n : ℕ, (((I ^ n).topologicalClosure : Ideal A) : Set A) =
      ((I ^ n : Ideal A) : Set A) := fun n ↦
    ((I ^ n).toAddSubgroup.isClosed_of_isOpen (hopen n)).closure_eq
  have : TopologicalRing.IsWeaklyPreAdic A := by
    refine ⟨I, fun n ↦ ?_, ?_⟩
    · rw [hcl n]
      exact hopen n
    · simpa only [hcl] using hIadic.hasBasis_nhds_zero
  have : T2Space A := hA.2.1
  exact TopologicalRing.IsWeaklyAdic.mk hA.2.2

/-- A weakly adic linearly topologized ring is admissible. -/
@[stacks 0GXF "weakly_adic_admissible"]
public theorem isAdmissible_of_isWeaklyAdic (A : Type*) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalRing.IsWeaklyAdic A] : TopologicalRing.IsAdmissible A := by
  have h := ((weaklyPreAdic_tfae.{_, 0} A).out 1 3).mp
    (inferInstance : TopologicalRing.IsWeaklyPreAdic A)
  exact ⟨h.1, inferInstance, inferInstance⟩

end

section

open scoped Topology


/-- A weakly adic linearly topologized ring has a countable fundamental system of open
ideals. -/
@[stacks 0GXF "weakly_adic_countable_basis"]
public theorem exists_countable_basis_open_ideals (A : Type*) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalRing.IsWeaklyAdic A] :
    ∃ I : ℕ → Ideal A, (∀ n : ℕ, IsOpen (I n : Set A)) ∧
      (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ (I n : Set A)) := by
  obtain ⟨J, h, hb⟩ := TopologicalRing.IsWeaklyPreAdic.exists_ideal (A := A)
  exact ⟨fun n ↦ (J ^ n).topologicalClosure, h, hb⟩

end

section

open scoped Topology


/-- The `J`-adic topology makes `A` a topological ring. -/
public lemma adic_topological_ring {A : Type*} [CommRing A] (J : Ideal A) :
    @IsTopologicalRing A J.adicTopology _ := by
  let _ := J.adicTopology
  infer_instance

/-- Every power `J ^ n` is open in the `J`-adic topology. -/
public lemma source_power_open {A : Type*} [CommRing A] (J : Ideal A) (n : ℕ) :
    @IsOpen A J.adicTopology ((J ^ n : Ideal A) : Set A) := by
  let _ := J.adicTopology
  exact (J.openAddSubgroup n).isOpen'

/-- Every open ideal of the `J`-adic topology contains some power `J ^ n`. -/
public lemma source_open_contains_power {A : Type*} [CommRing A]
    (J L : Ideal A) (hL : @IsOpen A J.adicTopology (L : Set A)) :
    ∃ n : ℕ, J ^ n ≤ L := by
  let _ := J.adicTopology
  obtain ⟨n, _, hn⟩ := J.hasBasis_nhds_zero_adic.mem_iff.mp
    (hL.mem_nhds L.zero_mem)
  exact ⟨n, hn⟩


/-- The closure of a positive power of an open ideal stays inside the ideal. -/
private lemma closure_pow_le_of_isOpen {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {I : Ideal A} (hI : IsOpen (I : Set A)) {n : ℕ} (hn : n ≠ 0) :
    (I ^ n).topologicalClosure ≤ I :=
  Submodule.topologicalClosure_minimal _ (Ideal.pow_le_self hn)
    (I.toAddSubgroup.isClosed_of_isOpen hI)

private lemma closure_powers_open {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] [TopologicalRing.IsWeaklyAdic A]
    (I : Ideal A) (hI : IsOpen (I : Set A)) (n : ℕ) :
    IsOpen ((I ^ n).topologicalClosure : Set A) := by
  obtain ⟨K, hKopen, hKbasis⟩ := TopologicalRing.IsWeaklyPreAdic.exists_ideal (A := A)
  obtain ⟨m, _, hm⟩ := hKbasis.mem_iff.mp (hI.mem_nhds I.zero_mem)
  have hm' : K ^ m ≤ I :=
    (K ^ m).le_topologicalClosure.trans hm
  have hmn : (K ^ (m * n)).topologicalClosure ≤ (I ^ n).topologicalClosure := by
    apply Submodule.topologicalClosure_mono
    simpa [pow_mul] using (pow_le_pow_left' hm' n)
  exact Ideal.isOpen_of_isOpen_subideal hmn (hKopen (m * n))

private lemma exists_finite_approximation {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (I : Ideal A) (hI : IsOpen (I : Set A))
    [Module.Finite A
      (I ⧸ Submodule.comap I.subtype (I ^ 2).topologicalClosure)] :
    ∃ J : Ideal A, J.FG ∧ J ≤ I ∧ I = J ⊔ (I ^ 2).topologicalClosure := by
  classical
  let K : Submodule A I := Submodule.comap I.subtype (I ^ 2).topologicalClosure
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := I ⧸ K)
  choose f hf using fun i : Fin n => K.mkQ_surjective (s i)
  let S : Submodule A I := Submodule.span A (Set.range f)
  have hmap : S.map K.mkQ = ⊤ := by
    simpa only [S, Submodule.map_span, ← Set.range_comp,
      show K.mkQ ∘ f = s from funext hf] using hs
  have hsup : K ⊔ S = ⊤ := (Submodule.map_mkQ_eq_top K S).mp hmap
  let J : Ideal A := S.map I.subtype
  refine ⟨J, ?_, ?_, ?_⟩
  · exact (Submodule.fg_span (Set.finite_range f)).map I.subtype
  · exact Submodule.map_subtype_le (p := I) S
  · have hC := closure_pow_le_of_isOpen hI (by decide : 2 ≠ 0)
    have hmapK : K.map I.subtype = (I ^ 2).topologicalClosure := by
      ext x
      simp [K, hC]
    simpa [Submodule.map_sup, Submodule.map_top, J, hmapK, sup_comm] using
      (congrArg (Submodule.map I.subtype) hsup).symm

private lemma closure_pow_mul_le {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (I : Ideal A) (n : ℕ) :
    (I ^ n).topologicalClosure * I ≤ (I ^ (n + 1)).topologicalClosure := by
  rw [Ideal.mul_le]
  intro x hx y hy
  apply map_mem_closure (mulRight_continuous y) hx
  intro z hz
  simpa [pow_succ] using (Ideal.mul_mem_mul hz hy : z * y ∈ I ^ n * I)

private lemma propagate_approximation {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalRing.IsWeaklyAdic A]
    (I J : Ideal A) (hI : IsOpen (I : Set A)) (hJ : J ≤ I)
    (n : ℕ) (hn : 2 ≤ n)
    (h : I = J ⊔ (I ^ n).topologicalClosure) :
    I = J ⊔ (I ^ (n + 1)).topologicalClosure := by
  have hn0 : n - 1 ≠ 0 := by omega
  have hpow : I ^ n ≤ J ⊔ (I ^ (n + 1)).topologicalClosure := by
    calc
      I ^ n = I ^ (n - 1) * I := by rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
      _ = I ^ (n - 1) * (J ⊔ (I ^ n).topologicalClosure) := by rw [← h]
      _ = I ^ (n - 1) * J ⊔ I ^ (n - 1) * (I ^ n).topologicalClosure :=
        Ideal.mul_sup _ _ _
      _ ≤ J ⊔ (I ^ (n + 1)).topologicalClosure := by
        apply sup_le
        · exact (Ideal.mul_le_right).trans le_sup_left
        · apply Ideal.mul_le.mpr
          intro x hx y hy
          have hxI : x ∈ I := (Ideal.pow_le_self hn0) hx
          have hxy : y * x ∈ (I ^ (n + 1)).topologicalClosure :=
            closure_pow_mul_le I n (Ideal.mul_mem_mul hy hxI)
          exact (mul_comm y x) ▸ ((le_sup_right :
            (I ^ (n + 1)).topologicalClosure ≤
              J ⊔ (I ^ (n + 1)).topologicalClosure) hxy)
  have hopen : IsOpen ((J ⊔ (I ^ (n + 1)).topologicalClosure : Ideal A) : Set A) :=
    Ideal.isOpen_of_isOpen_subideal le_sup_right (closure_powers_open I hI (n + 1))
  have hstep : (I ^ n).topologicalClosure ≤ J ⊔ (I ^ (n + 1)).topologicalClosure :=
    Submodule.topologicalClosure_minimal (I ^ n) hpow
      ((J ⊔ (I ^ (n + 1)).topologicalClosure).toAddSubgroup.isClosed_of_isOpen
        hopen)
  exact le_antisymm (h.le.trans (sup_le le_sup_left hstep))
    (sup_le hJ (closure_pow_le_of_isOpen hI (by omega)))

private lemma closure_powers_cofinal {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalRing.IsWeaklyAdic A] (I : Ideal A)
    (hI : TopologicalRing.IsIdealOfDefinition I) (U : Set A) (hU : U ∈ 𝓝 (0 : A)) :
    ∃ n : ℕ, ((I ^ n).topologicalClosure : Set A) ⊆ U := by
  obtain ⟨K, hKopen, hKbasis⟩ := TopologicalRing.IsWeaklyPreAdic.exists_ideal (A := A)
  obtain ⟨m, _, hm⟩ := hKbasis.mem_iff.mp hU
  have hKm : ((K ^ m).topologicalClosure : Set A) ∈ 𝓝 (0 : A) :=
    (hKopen m).mem_nhds (K ^ m).topologicalClosure.zero_mem
  obtain ⟨n, hn⟩ := hI.2 _ hKm
  have hsub : (I ^ n).topologicalClosure ≤ (K ^ m).topologicalClosure :=
    Submodule.topologicalClosure_minimal (I ^ n) hn
      (Submodule.isClosed_topologicalClosure _)
  exact ⟨n, Set.Subset.trans hsub hm⟩

private lemma closure_of_approximation {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalRing.IsWeaklyAdic A]
    (I J : Ideal A) (hI : TopologicalRing.IsIdealOfDefinition I)
    (h : ∀ n : ℕ, 2 ≤ n → I = J ⊔ (I ^ n).topologicalClosure) :
    J.topologicalClosure = I := by
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal J
      (le_sup_left.trans (h 2 le_rfl).ge)
      (I.toAddSubgroup.isClosed_of_isOpen hI.1)
  · intro x hx
    apply mem_closure_iff_nhds'.mpr
    intro U hU
    have hpre : (fun y : A => x + y) ⁻¹' U ∈ 𝓝 (0 : A) :=
      (continuousAt_const.add continuousAt_id).preimage_mem_nhds (by simpa using hU)
    obtain ⟨n, hn⟩ := closure_powers_cofinal I hI _ hpre
    let m := max 2 n
    have hmn : (I ^ m).topologicalClosure ≤ (I ^ n).topologicalClosure :=
      Submodule.topologicalClosure_mono (Ideal.pow_le_pow_right (Nat.le_max_right 2 n))
    have hmU : ((I ^ m).topologicalClosure : Set A) ⊆
        (fun y : A => x + y) ⁻¹' U := Set.Subset.trans hmn hn
    have hx' : x ∈ J ⊔ (I ^ m).topologicalClosure := (h m (Nat.le_max_left 2 n)).le hx
    obtain ⟨j, hj, c, hc, hsum⟩ := Submodule.mem_sup.mp hx'
    refine ⟨⟨j, hj⟩, ?_⟩
    have hjU : x + -c ∈ U := hmU (neg_mem hc)
    rw [← hsum] at hjU
    simpa [add_assoc] using hjU

private lemma exists_finite_dense_ideal {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalRing.IsWeaklyAdic A] (I : Ideal A)
    (hI : TopologicalRing.IsIdealOfDefinition I)
    [Module.Finite A
      (I ⧸ Submodule.comap I.subtype (I ^ 2).topologicalClosure)] :
    ∃ J : Ideal A, J.FG ∧ J ≤ I ∧ J.topologicalClosure = I := by
  obtain ⟨J, hJfg, hJI, hbase⟩ := exists_finite_approximation I hI.1
  have hall : ∀ n : ℕ, 2 ≤ n → I = J ⊔ (I ^ n).topologicalClosure := by
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    induction m with
    | zero => simpa using hbase
    | succ m ih =>
      simpa only [Nat.add_succ] using
        propagate_approximation I J hI.1 hJI (2 + m) (by omega) (ih (by omega))
  exact ⟨J, hJfg, hJI, closure_of_approximation I J hI hall⟩

/-- The product of the closures of two ideals lies in the closure of their product. -/
public lemma closure_mul_le {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] (J K : Ideal A) :
    J.topologicalClosure * K.topologicalClosure ≤ (J * K).topologicalClosure := by
  rw [Ideal.mul_le]
  intro x hx y hy
  exact map_mem_closure₂' (fun _ => mulLeft_continuous _) (fun _ => mulRight_continuous _) hx hy
    fun _ ha _ hb => Ideal.mul_mem_mul ha hb

/-- `Ideal.closure J` is `J.topologicalClosure`, the closure of `J` as a submodule. -/
public lemma ideal_closure_eq_submodule_closure {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] (J : Ideal A) :
    Ideal.closure J = J.topologicalClosure := by
  ext x
  rfl

private lemma closure_powers_of_dense {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] (I J : Ideal A)
    (hJI : J ≤ I) (h : J.topologicalClosure = I) (n : ℕ) :
    (J ^ n).topologicalClosure = (I ^ n).topologicalClosure := by
  apply le_antisymm
  · exact Submodule.topologicalClosure_mono (pow_le_pow_left' hJI n)
  · have hall : ∀ m : ℕ, I ^ m ≤ (J ^ m).topologicalClosure := by
      intro m
      induction m with
      | zero =>
        simpa only [pow_zero, Ideal.one_eq_top] using
          (Submodule.le_topologicalClosure (⊤ : Ideal A))
      | succ m ih =>
        rw [pow_succ]
        calc
          I ^ m * I ≤ (J ^ m).topologicalClosure * J.topologicalClosure := by
            rw [h]
            exact Ideal.mul_mono ih le_rfl
          _ ≤ (J ^ m * J).topologicalClosure := closure_mul_le _ _
          _ = (J ^ (m + 1)).topologicalClosure := by rw [pow_succ]
    exact (Submodule.topologicalClosure_mono (hall n)).trans
      ((Submodule.isClosed_topologicalClosure (J ^ n)).submodule_topologicalClosure_eq.le)

private lemma continuous_id_adic_source {A : Type*} [CommRing A]
    [τ : TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalRing.IsWeaklyAdic A] (I J : Ideal A)
    (hI : TopologicalRing.IsIdealOfDefinition I) (hJI : J ≤ I) :
    @Continuous A A J.adicTopology τ (RingHom.id A) := by
  refine @continuous_of_tendsto_nhds_zero A J.adicTopology
    (inferInstance) (by let _ := J.adicTopology; infer_instance)
    A (A →+* A) (inferInstance) τ (inferInstance) (inferInstance) (inferInstance)
    (RingHom.id A) ?_
  intro U hU
  obtain ⟨n, hn⟩ := closure_powers_cofinal I hI U hU
  apply J.hasBasis_nhds_zero_adic.mem_iff.mpr
  refine ⟨n, trivial, ?_⟩
  exact Set.Subset.trans
    ((pow_le_pow_left' hJI n).trans (I ^ n).le_topologicalClosure) hn

private lemma taut_id_adic_source {A : Type*} [CommRing A]
    [τ : TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalRing.IsWeaklyAdic A] (I J : Ideal A)
    (hI : TopologicalRing.IsIdealOfDefinition I) (hJI : J ≤ I)
    (hcl : J.topologicalClosure = I) :
    @RingHom.IsTaut A A (inferInstance) J.adicTopology (inferInstance) τ
      (inferInstance) (RingHom.id A) := by
  have hpow (n : ℕ) : (J ^ n).topologicalClosure = (I ^ n).topologicalClosure :=
    closure_powers_of_dense I J hJI hcl n
  have hopen (L : Ideal A) (hL : @IsOpen A J.adicTopology (L : Set A)) :
      IsOpen (Ideal.closure (L.map (RingHom.id A)) : Set A) := by
    obtain ⟨n, hn⟩ := source_open_contains_power J L hL
    apply Ideal.isOpen_of_isOpen_subideal
      (by simpa only [Ideal.map_id, ideal_closure_eq_submodule_closure] using
        (Submodule.topologicalClosure_mono hn))
    rw [hpow]
    exact closure_powers_open I hI.1 n
  refine ⟨hopen, ⟨fun U => ⟨fun hU => ?_, ?_⟩⟩⟩
  · obtain ⟨n, hn⟩ := closure_powers_cofinal I hI U hU
    refine ⟨J ^ n, source_power_open J n, ?_⟩
    simpa only [Ideal.map_id, ideal_closure_eq_submodule_closure, hpow n] using hn
  · rintro ⟨L, hL, hLU⟩
    exact Filter.mem_of_superset ((hopen L hL).mem_nhds (Ideal.closure _).zero_mem) hLU

/-- A complete linearly topologized ring whose topology is the fundamental system given by the
closures of the powers of a finitely generated ideal is adic with a finitely generated ideal of
definition. -/
@[stacks 0GXG]
public lemma exists_fg_isAdic_of_fg_closure_powers_basis
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [T2Space A]
    [hcomplete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)]
    (I : Ideal A) (hIfg : I.FG)
    (hopen : ∀ n : ℕ, IsOpen ((I ^ n).topologicalClosure : Set A))
    (hbasis : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ ((I ^ n).topologicalClosure : Set A))) :
    ∃ J : Ideal A, J.FG ∧ _root_.IsAdic J := by
  let : TopologicalRing.IsWeaklyPreAdic A := ⟨I, hopen, hbasis⟩
  let : TopologicalRing.IsWeaklyAdic A := TopologicalRing.IsWeaklyAdic.mk hcomplete
  have hdef : TopologicalRing.IsIdealOfDefinition I.topologicalClosure := by
    refine ⟨by simpa using hopen 1, fun U hU => ?_⟩
    obtain ⟨n, -, hn⟩ := hbasis.mem_iff.mp hU
    refine ⟨n, Set.Subset.trans (show I.topologicalClosure ^ n ≤ (I ^ n).topologicalClosure by
      simpa only [ideal_closure_eq_submodule_closure] using closure_pow_le_closure_pow I n) hn⟩
  exact @RingHom.exists_fg_ideal_isAdic_of_isTaut
    A A (inferInstance) I.adicTopology (adic_topological_ring I)
    (Ideal.isLinearTopology I) (inferInstance) (inferInstance)
    (inferInstance) (inferInstance) (RingHom.id A)
    (taut_id_adic_source I.topologicalClosure I hdef I.le_topologicalClosure rfl)
    ⟨I, hIfg, rfl⟩ (inferInstance) (inferInstance)

/-- If the quotient ring `A ⧸ K` is Noetherian then `I / (I ∩ K)` is a finite `A`-module for
every ideal `I`: that module is the image of `I` in `A ⧸ K`, a finitely generated ideal of a
Noetherian ring, and `A ⧸ K` is a quotient of `A`, so a generating set over `A ⧸ K` generates
over `A`. This is how the hypothesis of Stacks 0GXH below is met. -/
public lemma _root_.Ideal.finite_quotient_comap_subtype {A : Type*} [CommRing A]
    (I K : Ideal A) (hK : IsNoetherianRing (A ⧸ K)) :
    Module.Finite A (↥I ⧸ Submodule.comap I.subtype K) := by
  have _ : IsNoetherianRing (A ⧸ K) := hK
  let q : A →+* A ⧸ K := Ideal.Quotient.mk K
  let f : ↥I →ₗ[A] A ⧸ K := (Ideal.Quotient.mkₐ A K).toLinearMap.comp I.subtype
  have hker : LinearMap.ker f = Submodule.comap I.subtype K := by
    ext x
    change Ideal.Quotient.mk K x.1 = 0 ↔ x.1 ∈ K
    exact Ideal.Quotient.eq_zero_iff_mem
  have hrange : LinearMap.range f = Submodule.restrictScalars A (I.map q) := by
    ext z
    change z ∈ LinearMap.range f ↔ z ∈ I.map q
    refine ⟨?_, ?_⟩
    · rintro ⟨x, rfl⟩
      exact Ideal.mem_map_of_mem q x.2
    · intro hz
      obtain ⟨x, hx, hzx⟩ := (Ideal.mem_map_iff_of_surjective q
        (Ideal.Quotient.mk_surjective (I := K))).1 hz
      exact ⟨⟨x, hx⟩, by simpa [f, q] using hzx⟩
  have _ : Module.Finite A (Submodule.restrictScalars A (I.map q)) :=
    Module.Finite.of_fg ((IsNoetherian.noetherian (I.map q)).restrictScalars_of_surjective
      (Ideal.Quotient.mk_surjective (I := K)))
  have _ : Module.Finite A (LinearMap.range f) :=
    Module.Finite.equiv (LinearEquiv.ofEq _ _ hrange).symm
  exact Module.Finite.equiv
    ((Submodule.Quotient.equiv (Submodule.comap I.subtype K) (LinearMap.ker f)
      (LinearEquiv.refl A ↥I) (by simpa using hker.symm)).trans f.quotKerEquivRange).symm

/-- A weakly adic ring with an ideal of definition `I` for which
`I / closure(I ^ 2)` is finite has a finitely generated ideal defining its topology. -/
@[stacks 0GXH]
public lemma exists_fg_isAdic_of_quotient_closure_sq_finite
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [TopologicalRing.IsWeaklyAdic A]
    (I : Ideal A) (hI : TopologicalRing.IsIdealOfDefinition I)
    [Module.Finite A
      (I ⧸ Submodule.comap I.subtype (I ^ 2).topologicalClosure)] :
    ∃ J : Ideal A, J.FG ∧ _root_.IsAdic J := by
  obtain ⟨J, hJfg, hJI, hcl⟩ := exists_finite_dense_ideal I hI
  exact @RingHom.exists_fg_ideal_isAdic_of_isTaut
    A A (inferInstance) J.adicTopology (adic_topological_ring J)
    (Ideal.isLinearTopology J) (inferInstance) (inferInstance)
    (inferInstance) (inferInstance) (RingHom.id A)
    (taut_id_adic_source I J hI hJI hcl)
    ⟨J, hJfg, rfl⟩ (inferInstance) (inferInstance)

end

section

/-- The target of a continuous taut homomorphism from a weakly pre-adic linearly topologized
ring is weakly pre-adic. -/
@[stacks 0GXI]
public theorem isWeaklyPreAdic_of_isTaut {A B : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [IsLinearTopology B B] (φ : A →+* B) (hφ : Continuous φ)
    [TopologicalRing.IsWeaklyPreAdic A] (hφ_taut : RingHom.IsTaut φ) :
    TopologicalRing.IsWeaklyPreAdic B := by
  obtain ⟨I, hIopen, hIbasis⟩ := TopologicalRing.IsWeaklyPreAdic.exists_ideal (A := A)
  refine ⟨I.map φ, ?_, ?_⟩
  · intro n
    rw [← Ideal.map_pow φ I n]
    have h := hφ_taut.1 (I ^ n).closure (by
      simpa only [Submodule.topologicalClosure_coe, Ideal.coe_closure] using hIopen n)
    rw [RingHom.closure_map_closure φ hφ (I ^ n)] at h
    simpa only [Ideal.coe_closure, Submodule.topologicalClosure_coe] using h
  · refine hφ_taut.2.to_hasBasis ?_ ?_
    · intro K hKopen
      obtain ⟨n, -, hnK⟩ := hIbasis.mem_iff.mp (hKopen.mem_nhds K.zero_mem)
      refine ⟨n, trivial, ?_⟩
      rw [Submodule.topologicalClosure_coe, ← Ideal.coe_closure] at hnK
      have hle : (I ^ n).closure ≤ K := hnK
      have hmapped : ((I ^ n).closure.map φ).closure ≤ (K.map φ).closure :=
        closure_mono (Ideal.map_mono hle)
      rw [RingHom.closure_map_closure φ hφ (I ^ n)] at hmapped
      rw [← Ideal.map_pow φ I n]
      exact hmapped
    · intro n _
      refine ⟨(I ^ n).closure, ?_, ?_⟩
      · simpa only [Submodule.topologicalClosure_coe, Ideal.coe_closure] using hIopen n
      · rw [RingHom.closure_map_closure φ hφ (I ^ n), Ideal.map_pow]
        simpa only [Submodule.topologicalClosure_coe, Ideal.coe_closure] using
          (subset_rfl : closure (((I.map φ) ^ n : Ideal B) : Set B) ⊆ _)

end

section

open Filter
open scoped TensorProduct Topology

/-- A continuous ring map sends the closure of `L ^ n` into the closure of `K ^ n` once `L` is
mapped into `K`. -/
private theorem map_closure_pow_le {R S : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    (φ : R →+* S) (hφ : Continuous φ) (L : Ideal R) (K : Ideal S) (hLK : L.map φ ≤ K) (n : ℕ) :
    Ideal.map φ (L ^ n).topologicalClosure ≤ (K ^ n).topologicalClosure :=
  calc Ideal.map φ (L ^ n).topologicalClosure
      ≤ Ideal.closure ((Ideal.closure (L ^ n)).map φ) := subset_closure
    _ = Ideal.closure ((L ^ n).map φ) := RingHom.closure_map_closure φ hφ _
    _ = Ideal.closure (L.map φ ^ n) := by rw [Ideal.map_pow]
    _ ≤ Ideal.closure (K ^ n) := closure_mono (Ideal.pow_right_mono hLK n)

set_option synthInstance.maxHeartbeats 80000 in
-- instance search for the topological and algebra structures on the completed tensor product
/-- The completed tensor product of weakly pre-adic linearly topologized rings
over a commutative ring is weakly adic. -/
@[stacks 0GXJ]
public theorem completedTensorProduct_isWeaklyAdic
    {B A C : Type*} [CommRing B] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    [IsLinearTopology C C] [Algebra B A] [Algebra B C]
    (hA : TopologicalRing.IsWeaklyPreAdic A) (hC : TopologicalRing.IsWeaklyPreAdic C) :
    TopologicalRing.IsWeaklyAdic
      (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)) := by
        classical
        let := TopologicalRing.tensorProductTopology (R := B) (M := A) (N := C)
        let := TopologicalRing.tensorProductUniformSpace (R := B) (M := A) (N := C)
        let T := TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)
        have hAw :=
          ((TopologicalRing.weaklyPreAdic_tfae.{_, 0} A).out 1 3).mp hA
        have hCw :=
          ((TopologicalRing.weaklyPreAdic_tfae.{_, 0} C).out 1 3).mp hC
        rcases hAw with ⟨hApre, IA, hIAdef, hIAopen⟩
        rcases hCw with ⟨hCpre, JC, hJCdef, hJCopen⟩
        have hAdm := TopologicalRing.completedTensorProduct_isAdmissible
          (B := B) (A := A) (C := C) hApre hCpre
        let ιA := {I : Ideal A // IsOpen (I : Set A) ∧ I ≤ IA}
        let ιC := {J : Ideal C // IsOpen (J : Set C) ∧ J ≤ JC}
        let I : ιA → Ideal A := fun i => i.1
        let J : ιC → Ideal C := fun j => j.1
        have bI : (nhds (0 : A)).HasBasis (fun _ : ιA => True) (fun i => (I i : Set A)) := by
          refine (IsLinearTopology.hasBasis_open_ideal (R := A)).to_hasBasis
            (fun L hL => ⟨⟨L ⊓ IA, hL.inter hIAdef.1, inf_le_right⟩, trivial, inf_le_left⟩)
            (fun i _ => ⟨i.1, i.2.1, le_rfl⟩)
        have bJ : (nhds (0 : C)).HasBasis (fun _ : ιC => True) (fun j => (J j : Set C)) := by
          refine (IsLinearTopology.hasBasis_open_ideal (R := C)).to_hasBasis
            (fun L hL => ⟨⟨L ⊓ JC, hL.inter hJCdef.1, inf_le_right⟩, trivial, inf_le_left⟩)
            (fun j _ => ⟨j.1, j.2.1, le_rfl⟩)
        let φA : A →+* T := RingHom.comp UniformSpace.Completion.coeRingHom
          ((Algebra.TensorProduct.includeLeft : A →ₐ[B] A ⊗[B] C).toRingHom)
        let φC : C →+* T := RingHom.comp UniformSpace.Completion.coeRingHom
          ((Algebra.TensorProduct.includeRight : C →ₐ[B] A ⊗[B] C).toRingHom)
        have hφA : Continuous φA := by
          change Continuous (fun a : A => ((a ⊗ₜ[B] (1 : C) : A ⊗[B] C) : T))
          exact (UniformSpace.Completion.continuous_coe (A ⊗[B] C)).comp
            (TopologicalRing.continuous_tmul_const (R := B) (M := A) (N := C) (1 : C))
        have hφC : Continuous φC := by
          change Continuous (fun c : C => (((1 : A) ⊗ₜ[B] c : A ⊗[B] C) : T))
          exact (UniformSpace.Completion.continuous_coe (A ⊗[B] C)).comp
            (TopologicalRing.continuous_const_tmul (R := B) (M := A) (N := C) (1 : A))
        let i₀ : ιA := ⟨IA, hIAdef.1, le_rfl⟩
        let j₀ : ιC := ⟨JC, hJCdef.1, le_rfl⟩
        let K : Ideal T := TopologicalRing.projectionKernel I J bI bJ i₀ j₀
        have hQeq (i : ιA) (j : ιC) : TopologicalRing.projectionKernel I J bI bJ i j =
            Ideal.closure (Ideal.map φA (I i) + Ideal.map φC (J j)) :=
          SetLike.coe_injective (TopologicalRing.projectionKernel_eq_closure I J bI bJ i j)
        have hQimage (i : ιA) (j : ιC) :
            Ideal.map φA (I i) ≤ TopologicalRing.projectionKernel I J bI bJ i j ∧
              Ideal.map φC (J j) ≤ TopologicalRing.projectionKernel I J bI bJ i j := by
          rw [hQeq, Ideal.add_eq_sup]
          exact ⟨le_sup_left.trans (show _ ≤ _ from subset_closure),
            le_sup_right.trans (show _ ≤ _ from subset_closure)⟩
        have hK_eq : K = Ideal.closure ((Ideal.map φA IA) + (Ideal.map φC JC)) := hQeq i₀ j₀
        have hLA : Ideal.map φA IA ≤ K := (hQimage i₀ j₀).1
        have hMC : Ideal.map φC JC ≤ K := (hQimage i₀ j₀).2
        have hKpowOpen : ∀ n : ℕ, IsOpen ((K ^ n).topologicalClosure : Set T) := by
          intro n
          cases n with
          | zero => simp
          | succ n =>
              let i : ιA := ⟨(IA ^ (n + 1)).topologicalClosure, hIAopen _ (by omega),
                closure_pow_le_of_isOpen hIAdef.1 (by omega)⟩
              let j : ιC := ⟨(JC ^ (n + 1)).topologicalClosure, hJCopen _ (by omega),
                closure_pow_le_of_isOpen hJCdef.1 (by omega)⟩
              let Q : Ideal T := TopologicalRing.projectionKernel I J bI bJ i j
              have hQopen : IsOpen (Q : Set T) :=
                TopologicalRing.isOpen_projectionKernel I J bI bJ i j
              have hAimage : (I i).map φA ≤ (K ^ (n + 1)).topologicalClosure :=
                map_closure_pow_le φA hφA _ _ hLA _
              have hCimage : (J j).map φC ≤ (K ^ (n + 1)).topologicalClosure :=
                map_closure_pow_le φC hφC _ _ hMC _
              have hQle : Q ≤ (K ^ (n + 1)).topologicalClosure := by
                rw [show Q = _ from hQeq i j, Ideal.add_eq_sup]
                exact closure_minimal (sup_le hAimage hCimage) isClosed_closure
              apply Ideal.isOpen_of_isOpen_subideal hQle hQopen
        have hKcofinal : ∀ U ∈ nhds (0 : T), ∃ n : ℕ,
            ((K ^ n).topologicalClosure : Set T) ⊆ U := by
          intro U hU
          obtain ⟨p, -, hp⟩ := (TopologicalRing.hasBasis_projectionKernel I J bI bJ).mem_iff.mp hU
          let i : ιA := p.1
          let j : ιC := p.2
          have hIi : (I i : Set A) ∈ nhds (0 : A) := i.2.1.mem_nhds (by simp)
          have hJj : (J j : Set C) ∈ nhds (0 : C) := j.2.1.mem_nhds (by simp)
          obtain ⟨n, hn⟩ := hIAdef.2 (I i : Set A) hIi
          obtain ⟨m, hm⟩ := hJCdef.2 (J j : Set C) hJj
          have hn' : IA ^ n ≤ I i := SetLike.coe_subset_coe.mp hn
          have hm' : JC ^ m ≤ J j := SetLike.coe_subset_coe.mp hm
          let L : Ideal T := Ideal.map φA IA
          let M : Ideal T := Ideal.map φC JC
          let Q : Ideal T := TopologicalRing.projectionKernel I J bI bJ i j
          have hLpow : L ^ n ≤ Q := by
            rw [← Ideal.map_pow]
            exact (Ideal.map_mono hn').trans (hQimage i j).1
          have hMpow : M ^ m ≤ Q := by
            rw [← Ideal.map_pow]
            exact (Ideal.map_mono hm').trans (hQimage i j).2
          have hsumPow : (L + M) ^ (n + m) ≤ Q := by
            calc
              (L + M) ^ (n + m) ≤ L ^ n + M ^ m := by
                simpa [Ideal.add_eq_sup] using
                  (Ideal.sup_pow_add_le_pow_sup_pow (I := L) (J := M) (n := n) (m := m))
              _ ≤ Q := sup_le hLpow hMpow
          have hQclosed : IsClosed (Q : Set T) :=
            Q.toAddSubgroup.isClosed_of_isOpen
              (TopologicalRing.isOpen_projectionKernel I J bI bJ i j)
          have hKpower : K ^ (n + m) ≤ Q := by
            rw [hK_eq]
            exact (closure_pow_le_closure_pow (L + M) (n + m)).trans
              (closure_minimal hsumPow hQclosed)
          have hclosure : (K ^ (n + m)).topologicalClosure ≤ Q :=
            closure_minimal hKpower hQclosed
          have hQsub : (Q : Set T) ⊆ U := by
            intro x hx
            exact hp (by simpa [Q, i, j] using hx)
          exact ⟨n + m, fun x hx => hQsub (hclosure hx)⟩
        have hpre : TopologicalRing.IsWeaklyPreAdic T := by
          refine ⟨K, hKpowOpen, ?_⟩
          refine (IsLinearTopology.hasBasis_open_ideal (R := T)).to_hasBasis ?_ ?_
          · intro U hU
            obtain ⟨n, hn⟩ := hKcofinal U (hU.mem_nhds (zero_mem _))
            exact ⟨n, trivial, hn⟩
          · intro n _
            exact ⟨(K ^ n).topologicalClosure, hKpowOpen n, Set.Subset.rfl⟩
        let : TopologicalRing.IsWeaklyPreAdic T := hpre
        let : T2Space T := (hAdm.2).1
        have hcomplete : @CompleteSpace T (IsTopologicalAddGroup.rightUniformSpace T) :=
          (hAdm.2).2
        exact TopologicalRing.IsWeaklyAdic.mk hcomplete

end

end TopologicalRing

end
