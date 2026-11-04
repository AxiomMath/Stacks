module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.Topology.Algebra.Nonarchimedean.Bases
public import Mathlib.Topology.Algebra.UniformFilterBasis
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Defs.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Nilpotent.Descent
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings
public import StacksFrontier.Topology.Algebra.AdicTopology.QuotientDiagram
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteType.WeakIdealConditions

/-!
# Algebras topologically of finite type: equivalence of the characterisations

This file constructs a restricted-power-series presentation from a taut homomorphism with a
dense polynomial map, and proves the equivalence of the four standard characterisations: a
restricted-power-series presentation, finite type modulo every weak ideal of definition, finite
type modulo a cofinal family, and tautness of a presentation.

## Implementation notes

`TopologicalRing.finiteType_tfae` routes its own `(a) → (c)` step through
`TopologicalRing.isTopologicallyOfFiniteType_of_finiteTypeModuloEveryWeakIdeal` rather than
through a fundamental sequence of weak ideals of definition, and spends its countability
hypothesis only on the cofinal condition (b) and the restricted power series presentation (d).

## References

* [Stacks Project, Tag 0ANU](https://stacks.math.columbia.edu/tag/0ANU)
-/

@[expose] public section

namespace TopologicalRing

section

open Filter

universe u v w

variable {B : Type u} {A : Type v}
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]

omit [IsTopologicalRing B] [IsLinearTopology B B] [IsLinearTopology A A] in
private theorem polynomialMap_continuous_of_taut (σ : Type w) (φ : B →+* A)
    (f : MvPolynomial σ B →+* A)
    (hf : f.comp MvPolynomial.C = φ) (htaut : RingHom.IsTaut φ) :
    letI : UniformSpace (MvPolynomial σ B) := restrictedPolynomialUniformSpace B σ
    letI : TopologicalSpace (MvPolynomial σ B) := restrictedPolynomialTopology B σ
    Continuous f := by
  let : UniformSpace (MvPolynomial σ B) := restrictedPolynomialUniformSpace B σ
  let : TopologicalSpace (MvPolynomial σ B) := restrictedPolynomialTopology B σ
  let : Nonempty { I : Ideal B // IsOpen (I : Set B) } := ⟨⟨⊤, isOpen_univ⟩⟩
  let hP := (restrictedPolynomialRingSubgroupsBasis B σ).hasBasis_nhds_zero
  have hzero : Tendsto f (nhds (0 : MvPolynomial σ B)) (nhds (0 : A)) := by
    apply (hP.tendsto_iff htaut.2).2
    intro J hJ
    refine ⟨⟨J, hJ⟩, trivial, ?_⟩
    have hmap : (J.map (MvPolynomial.C : B →+* MvPolynomial σ B)).map f ≤
        Ideal.map φ J := by
      rw [Ideal.map_map, hf]
    intro x hx
    exact subset_closure (Ideal.map_le_iff_le_comap.mp hmap hx)
  apply continuous_of_continuousAt_zero f.toAddMonoidHom
  show Tendsto (f.toAddMonoidHom) (nhds 0) (nhds (f.toAddMonoidHom 0))
  rw [map_zero]
  exact hzero

/-- One step of lifting a compatible sequence along a surjection with liftable kernel. -/
private theorem exists_lift_step
    {S T : ℕ → Type*} [∀ n, Ring (S n)] [∀ n, Ring (T n)]
    (s : ∀ n, S (n + 1) →+* S n) (t : ∀ n, T (n + 1) →+* T n)
    (f : ∀ n, S n →+* T n)
    (hcomm : ∀ n, (t n).comp (f (n + 1)) = (f n).comp (s n))
    (hsurj : ∀ n, Function.Surjective (f n))
    (hker : ∀ n (x : S n), f n x = 0 →
      ∃ y : S (n + 1), f (n + 1) y = 0 ∧ s n y = x)
    (y : ∀ n, T n) (hy : ∀ n, t n (y (n + 1)) = y n) (n : ℕ) (z : S n) (hz : f n z = y n) :
    ∃ u : S (n + 1), f (n + 1) u = y (n + 1) ∧ s n u = z := by
  obtain ⟨u, hu⟩ := hsurj (n + 1) (y (n + 1))
  have hc := congrArg (fun g : S (n + 1) →+* T n => g u) (hcomm n)
  simp only [RingHom.comp_apply] at hc
  have hdelta : f n (z - s n u) = 0 := by
    rw [map_sub, ← hc, hz, hu, hy n, sub_self]
  obtain ⟨w, hw, hsw⟩ := hker n (z - s n u) hdelta
  refine ⟨u + w, ?_, ?_⟩
  · rw [map_add, hu, hw, add_zero]
  · rw [map_add, hsw]
    abel

/-- A compatible sequence vanishing at `m` vanishes at every earlier index. -/
private theorem eq_zero_of_compatible_of_le {T : ℕ → Type*} [∀ n, Ring (T n)]
    (t : ∀ n, T (n + 1) →+* T n) (y : ∀ n, T n) (hy : ∀ n, t n (y (n + 1)) = y n)
    {m n : ℕ} (hn : n ≤ m) (hym : y m = 0) : y n = 0 := by
  induction m, hn using Nat.le_induction with
  | base => exact hym
  | succ m _ ih => exact ih (by rw [← hy m, hym, map_zero])

private theorem compatible_lift_of_surjective_kernel_lift
    {S T : ℕ → Type*} [∀ n, Ring (S n)] [∀ n, Ring (T n)]
    (s : ∀ n, S (n + 1) →+* S n) (t : ∀ n, T (n + 1) →+* T n)
    (f : ∀ n, S n →+* T n)
    (hcomm : ∀ n, (t n).comp (f (n + 1)) = (f n).comp (s n))
    (hsurj : ∀ n, Function.Surjective (f n))
    (hker : ∀ n (x : S n), f n x = 0 →
      ∃ y : S (n + 1), f (n + 1) y = 0 ∧ s n y = x)
    (y : ∀ n, T n) (hy : ∀ n, t n (y (n + 1)) = y n)
    (x₀ : S 0) (hx₀ : f 0 x₀ = y 0) :
    ∃ x : ∀ n, S n, (∀ n, s n (x (n + 1)) = x n) ∧
      (∀ n, f n (x n) = y n) ∧ x 0 = x₀ := by
  classical
  have step_exists := exists_lift_step s t f hcomm hsurj hker y hy
  let chooseLift (n : ℕ) (z : S n) (hz : f n z = y n) : S (n + 1) :=
    Classical.choose (step_exists n z hz)
  have chooseLift_spec (n : ℕ) (z : S n) (hz : f n z = y n) :
      f (n + 1) (chooseLift n z hz) = y (n + 1) ∧
        s n (chooseLift n z hz) = z :=
    Classical.choose_spec (step_exists n z hz)
  let z : ∀ n, {z : S n // f n z = y n} :=
    Nat.rec ⟨x₀, hx₀⟩ (fun n q =>
      ⟨chooseLift n q.1 q.2, (chooseLift_spec n q.1 q.2).1⟩)
  refine ⟨fun n => (z n).1, ?_, ?_⟩
  · intro n
    exact (chooseLift_spec n (z n).1 (z n).2).2
  · refine ⟨?_, rfl⟩
    intro n
    exact (z n).2

private theorem compatible_lift_vanishing_until
    {S T : ℕ → Type*} [∀ n, Ring (S n)] [∀ n, Ring (T n)]
    (s : ∀ n, S (n + 1) →+* S n) (t : ∀ n, T (n + 1) →+* T n)
    (f : ∀ n, S n →+* T n)
    (hcomm : ∀ n, (t n).comp (f (n + 1)) = (f n).comp (s n))
    (hsurj : ∀ n, Function.Surjective (f n))
    (hker : ∀ n (x : S n), f n x = 0 →
      ∃ y : S (n + 1), f (n + 1) y = 0 ∧ s n y = x)
    (y : ∀ n, T n) (hy : ∀ n, t n (y (n + 1)) = y n)
    (m : ℕ) (hym : y m = 0) :
    ∃ x : ∀ n, S n, (∀ n, s n (x (n + 1)) = x n) ∧
      (∀ n, f n (x n) = y n) ∧ x m = 0 := by
  classical
  have hyzero (n : ℕ) (hn : n ≤ m) : y n = 0 := eq_zero_of_compatible_of_le t y hy hn hym
  have step_exists := exists_lift_step s t f hcomm hsurj hker y hy
  let chooseLift (n : ℕ) (z : S n) (hz : f n z = y n) : S (n + 1) :=
    Classical.choose (step_exists n z hz)
  have chooseLift_spec (n : ℕ) (z : S n) (hz : f n z = y n) :
      f (n + 1) (chooseLift n z hz) = y (n + 1) ∧
        s n (chooseLift n z hz) = z :=
    Classical.choose_spec (step_exists n z hz)
  let z : ∀ n, {x : S n // f n x = y n} := Nat.rec
    ⟨0, by simp [hyzero 0 (Nat.zero_le m)]⟩
    (fun n q => if hn : n < m then
      ⟨0, by simp [hyzero (n + 1) (by omega)]⟩
    else ⟨chooseLift n q.1 q.2, (chooseLift_spec n q.1 q.2).1⟩)
  have hzle (n : ℕ) (hn : n ≤ m) : (z n).1 = 0 := by
    induction n with
    | zero => simp [z]
    | succ n ih =>
      have hnlt : n < m := by omega
      simp [z, hnlt]
  refine ⟨fun n => (z n).1, ?_, ?_, ?_⟩
  · intro n
    by_cases hn : n < m
    · have h₀ := hzle n (by omega)
      have h₁ := hzle (n + 1) (by omega)
      show s n (z (n + 1)).1 = (z n).1
      rw [h₀, h₁, map_zero]
    · have hznext : (z (n + 1)).1 = chooseLift n (z n).1 (z n).2 := by
        simp [z, hn]
      show s n (z (n + 1)).1 = (z n).1
      rw [hznext]
      exact (chooseLift_spec n (z n).1 (z n).2).2
  · intro n
    exact (z n).2
  · exact hzle m le_rfl

private theorem quotientLimit_coordinate_hasBasis
    {Q : ℕ → Type*} [∀ n, CommRing (Q n)] [∀ n, TopologicalSpace (Q n)]
    [∀ n, DiscreteTopology (Q n)]
    (q : ∀ n, Q (n + 1) →+* Q n)
    (T : Subring (∀ n, Q n))
    (hcompat : ∀ x : T, ∀ n, q n (x.1 (n + 1)) = x.1 n) :
    (nhds (0 : T)).HasBasis (fun _ : ℕ => True)
      (fun n => {x : T | x.1 n = 0}) := by
  classical
  refine ⟨?_⟩
  intro U
  constructor
  · intro hU
    rw [nhds_subtype_eq_comap] at hU
    rcases Filter.mem_comap.mp hU with ⟨V, hV, hVU⟩
    rw [nhds_pi, Filter.mem_pi] at hV
    rcases hV with ⟨F, hFfinite, t, ht, hFV⟩
    obtain ⟨m, hm⟩ := hFfinite.bddAbove
    refine ⟨m, trivial, ?_⟩
    intro x hx
    apply hVU
    apply hFV
    intro i hi
    have him : i ≤ m := hm hi
    have hxi : x.1 i = 0 :=
      eq_zero_of_compatible_of_le q (fun n => x.1 n) (fun n => hcompat x n) him hx
    simpa [hxi] using mem_of_mem_nhds (ht i)
  · rintro ⟨m, -, hsub⟩
    have hc : Continuous (fun x : T => x.1 m) :=
      (continuous_apply m).comp continuous_subtype_val
    have ho : IsOpen {x : T | x.1 m = (0 : Q m)} :=
      (isOpen_discrete ({(0 : Q m)} : Set (Q m))).preimage hc
    exact Filter.mem_of_superset (ho.mem_nhds (by simp)) hsub

-- The nested completion, quotient-limit, and compatible-lift constructions elaborate together
-- into a large dependent term, so this bridge needs a larger heartbeat budget.
private theorem restrictedPowerSeriesPresentation_of_taut_dense
    (φ : B →+* A) (hφ : Continuous φ)
    (hB : TopologicalRing.IsWeaklyAdmissible B) (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hBcount : (nhds (0 : B)).IsCountablyGenerated)
    (htaut : RingHom.IsTaut φ)
    (hft : TopologicalRing.IsTopologicallyOfFiniteType φ) :
    HasRestrictedPowerSeriesPresentation φ := by
  classical
  obtain ⟨n, f, hfcomp, hfdense⟩ := hft
  obtain ⟨J, hJ⟩ := exists_fundamental_weak_ideal_sequence B hB hBcount
  let P := MvPolynomial (Fin n) B
  let R := RestrictedPowerSeries B (Fin n)
  let : UniformSpace P := restrictedPolynomialUniformSpace B (Fin n)
  let : TopologicalSpace P := restrictedPolynomialTopology B (Fin n)
  let : IsTopologicalRing P := restrictedPolynomialIsTopologicalRing B (Fin n)
  let : IsUniformAddGroup P :=
    (restrictedPolynomialRingFilterBasis B (Fin n)).toAddGroupFilterBasis.isUniformAddGroup
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  let : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  let : UniformSpace R := restrictedPowerSeriesUniformSpace B (Fin n)
  let : CompleteSpace R := restrictedPowerSeriesCompleteSpace B (Fin n)
  let : T2Space R := restrictedPowerSeriesT2Space B (Fin n)
  let : IsTopologicalRing R := restrictedPowerSeriesIsTopologicalRing B (Fin n)
  let : IsUniformAddGroup R := by
    show IsUniformAddGroup
      (@UniformSpace.Completion P (restrictedPolynomialUniformSpace B (Fin n)))
    exact UniformSpace.Completion.isUniformAddGroup
  let incl : P →+* R := polynomialToRestrictedPowerSeries B (Fin n)
  have hfcont : Continuous f := by
    simpa [P] using polynomialMap_continuous_of_taut
      (B := B) (A := A) (σ := Fin n) (φ := φ) (f := f) hfcomp htaut
  let : CompleteSpace A := hA.2.1
  let : T2Space A := hA.2.2
  let g : R →+* A := UniformSpace.Completion.extensionHom (α := P) f hfcont
  have hgcont : Continuous g := by
    show Continuous (UniformSpace.Completion.extension (α := P) f)
    exact UniformSpace.Completion.continuous_extension
  have hg_incl (x : P) : g (incl x) = f x := by
    show UniformSpace.Completion.extensionHom f hfcont (x : UniformSpace.Completion P) = f x
    exact UniformSpace.Completion.extensionHom_coe f hfcont x
  have hgp : g.comp incl = f := RingHom.ext hg_incl
  let N : ℕ → Ideal P := fun m => (J m).map (MvPolynomial.C : B →+* P)
  let L : ℕ → Ideal R := fun m => Ideal.closure (Ideal.map incl (N m))
  have hLset (m : ℕ) : (L m : Set R) =
      closure ((incl : P → R) '' (N m : Set P)) :=
    idealClosure_map_eq_closure_image_of_denseRange incl
      UniformSpace.Completion.denseRange_coe (N m)
  have hLmem (m : ℕ) : (L m : Set R) ∈ nhds (0 : R) := by
    rw [hLset]
    let idx : {I : Ideal B // IsOpen (I : Set B)} := ⟨J m, (hJ.1 m).1⟩
    simpa [N, idx] using
      (restrictedPowerSeries_nhds_hasBasis B (Fin n)).mem_of_mem (i := idx) trivial
  have hLopen (m : ℕ) : IsOpen (L m : Set R) :=
    (L m).toAddSubgroup.isOpen_of_mem_nhds (g := (0 : R)) (by simpa using hLmem m)
  have hLclosed (m : ℕ) : IsClosed (L m : Set R) :=
    (L m).toAddSubgroup.isClosed_of_isOpen (hLopen m)
  have hLanti : Antitone L := by
    apply antitone_nat_of_succ_le
    intro m
    show Ideal.closure (Ideal.map incl (N (m + 1))) ≤
      Ideal.closure (Ideal.map incl (N m))
    apply closure_mono
    exact Ideal.map_mono (Ideal.map_mono (hJ.2.1 (Nat.le_succ m)))
  have hLbasis : (nhds (0 : R)).HasBasis (fun _ : ℕ => True)
      (fun m => (L m : Set R)) := by
    refine ⟨?_⟩
    intro U
    constructor
    · intro hU
      obtain ⟨V, -, hVU⟩ :=
        (restrictedPowerSeries_nhds_hasBasis B (Fin n)).mem_iff.mp hU
      obtain ⟨m, -, hm⟩ := hJ.2.2.mem_iff.mp (V.2.mem_nhds V.1.zero_mem)
      refine ⟨m, trivial, ?_⟩
      intro x hx
      have himg : incl '' (N m : Set P) ⊆
          incl '' (V.1.map (MvPolynomial.C : B →+* P) : Set P) := by
        rintro z ⟨p, hp, rfl⟩
        have hm' : J m ≤ V.1 := fun b hb => hm hb
        exact ⟨p, Ideal.map_mono hm' hp, rfl⟩
      apply hVU
      rw [hLset] at hx
      exact closure_mono himg hx
    · rintro ⟨m, -, hsub⟩
      exact Filter.mem_of_superset ((hLopen m).mem_nhds (L m).zero_mem) hsub
  have hRlim := RingHom.QuotientDiagram.quotientLimit_equiv
    (RingHom.id R) L hLanti
    (fun m => by simpa [RingHom.QuotientDiagram.targetIdeal, hLclosed m]
      using hLopen m)
    (by simpa [RingHom.QuotientDiagram.targetIdeal,
      fun m => hLclosed m] using hLbasis)
    (by
      rw [IsUniformAddGroup.rightUniformSpace_eq]
      exact restrictedPowerSeriesCompleteSpace B (Fin n))
    (by infer_instance)
  let S := RingHom.QuotientDiagram.quotientLimit (RingHom.id R) L hLanti
  let eR : R ≃+* S := Classical.choose hRlim
  have heR : Continuous eR ∧ Continuous eR.symm ∧
      ∀ (r : R) (m : ℕ),
        ((eR r : S) : ∀ k, R ⧸ RingHom.QuotientDiagram.targetIdeal
          (RingHom.id R) L k) m =
        Ideal.Quotient.mk (RingHom.QuotientDiagram.targetIdeal
          (RingHom.id R) L m) r := Classical.choose_spec hRlim
  let I : ℕ → Ideal A := fun m =>
    RingHom.QuotientDiagram.targetIdeal φ J m
  have hdiag : RingHom.QuotientDiagram.HasQuotientDiagram φ J hJ.2.1 :=
    (RingHom.QuotientDiagram.isTaut_iff_hasQuotientDiagram
      φ hφ hA hB J hJ).mp htaut
  let T := RingHom.QuotientDiagram.quotientLimit φ J hJ.2.1
  let eA : A ≃+* T := Classical.choose hdiag.2.2.2
  have heA : Continuous eA ∧ Continuous eA.symm ∧
      ∀ (a : A) (m : ℕ),
        ((eA a : T) : ∀ k, A ⧸ I k) m = Ideal.Quotient.mk (I m) a :=
    Classical.choose_spec hdiag.2.2.2
  let C : ℕ → Ideal R := fun m =>
    RingHom.QuotientDiagram.targetIdeal (RingHom.id R) L m
  have hCeq (m : ℕ) : C m = L m := by
    show Ideal.closure (Ideal.map (RingHom.id R) (L m)) = L m
    rw [Ideal.map_id]
    exact Ideal.closure_eq_of_isClosed (L m) (hLclosed m)
  let qS : (m : ℕ) → R ⧸ C (m + 1) →+* R ⧸ C m := fun m =>
    RingHom.QuotientDiagram.quotientTransition
      (RingHom.id R) L hLanti m
  let qT : (m : ℕ) → A ⧸ I (m + 1) →+* A ⧸ I m := fun m =>
    RingHom.QuotientDiagram.quotientTransition φ J hJ.2.1 m
  let qA : (m : ℕ) → A →+* A ⧸ I m := fun m => Ideal.Quotient.mk (I m)
  have hNmap (m : ℕ) : Ideal.map f (N m) ≤ I m := by
    show Ideal.map f ((J m).map (MvPolynomial.C : B →+* P)) ≤
      Ideal.closure ((J m).map φ)
    rw [Ideal.map_map, hfcomp]
    exact subset_closure
  have hqker (m : ℕ) : C m ≤ RingHom.ker ((qA m).comp g) := by
    rw [hCeq]
    have hpre : Ideal.map incl (N m) ≤ RingHom.ker ((qA m).comp g) := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro x hx
      show qA m (g (incl x)) = 0
      rw [hg_incl]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (hNmap m (Ideal.mem_map_of_mem f hx))
    have hcont : Continuous ((qA m).comp g) := continuous_quot_mk.comp hgcont
    have : DiscreteTopology (A ⧸ I m) :=
      QuotientAddGroup.discreteTopology_iff.mpr (hdiag.1 m)
    have hclosed : IsClosed (RingHom.ker ((qA m).comp g) : Set R) := by
      show IsClosed (((qA m).comp g) ⁻¹' ({0} : Set (A ⧸ I m)))
      exact (isClosed_discrete _).preimage hcont
    exact closure_minimal hpre hclosed
  let F : (m : ℕ) → R ⧸ C m →+* A ⧸ I m := fun m =>
    Ideal.Quotient.lift (C m) ((qA m).comp g) (fun x hx =>
      RingHom.mem_ker.mp (hqker m hx))
  have hFmk (m : ℕ) (x : R) : F m (Ideal.Quotient.mk (C m) x) = qA m (g x) := by
    simp [F]
  have hFsurj (m : ℕ) : Function.Surjective (F m) := by
    let : DiscreteTopology (A ⧸ I m) :=
      QuotientAddGroup.discreteTopology_iff.mpr (hdiag.1 m)
    have hdense : DenseRange ((qA m).comp f) := by
      have hqsurj : Function.Surjective (qA m) := Ideal.Quotient.mk_surjective
      exact hqsurj.denseRange.comp hfdense continuous_quot_mk
    have hs : Function.Surjective ((qA m).comp f) := denseRange_discrete.mp hdense
    intro y
    obtain ⟨p, hp⟩ := hs y
    refine ⟨Ideal.Quotient.mk (C m) (incl p), ?_⟩
    rw [hFmk, hg_incl]
    exact hp
  have hFmkcomp (m : ℕ) :
      (F m).comp (Ideal.Quotient.mk (C m)) = (qA m).comp g := by
    ext x
    exact hFmk m x
  have hCanti : Antitone C := by
    intro i j hij
    rw [hCeq i, hCeq j]
    exact hLanti hij
  have hFcomm (m : ℕ) : (qT m).comp (F (m + 1)) = (F m).comp (qS m) := by
    apply RingHom.ext
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    show qT m (F (m + 1) (Ideal.Quotient.mk (C (m + 1)) r)) =
      F m (qS m (Ideal.Quotient.mk (C (m + 1)) r))
    have hqSmk : qS m (Ideal.Quotient.mk (C (m + 1)) r) =
        Ideal.Quotient.mk (C m) r := by
      show Ideal.Quotient.factor (hCanti (Nat.le_succ m))
        (Ideal.Quotient.mk (C (m + 1)) r) = Ideal.Quotient.mk (C m) r
      rw [Ideal.Quotient.factor_mk]
    rw [hFmk (m + 1) r, hqSmk, hFmk m r]
    have hIt : I (m + 1) ≤ I m := by
      show (Ideal.closure ((J (m + 1)).map φ) : Set A) ⊆
        (Ideal.closure ((J m).map φ) : Set A)
      exact closure_mono (Ideal.map_mono (hJ.2.1 (Nat.le_succ m)))
    show Ideal.Quotient.factor hIt
      (Ideal.Quotient.mk (I (m + 1)) (g r)) = Ideal.Quotient.mk (I m) (g r)
    rw [Ideal.Quotient.factor_mk]
  have hkerS (m : ℕ) : RingHom.ker (qS m) =
      Ideal.map (Ideal.Quotient.mk (C (m + 1))) (C m) := by
    show RingHom.ker (Ideal.Quotient.factor (hCanti (Nat.le_succ m))) = _
    rw [Ideal.Quotient.factor_ker]
  have hFimageKer (m : ℕ) :
      Ideal.map (F (m + 1)) (Ideal.map (Ideal.Quotient.mk (C (m + 1))) (C m)) =
        RingHom.ker (qT m) := by
    have hcont : Continuous ((qA (m + 1)).comp g) := continuous_quot_mk.comp hgcont
    let : DiscreteTopology (A ⧸ I (m + 1)) :=
      QuotientAddGroup.discreteTopology_iff.mpr (hdiag.1 (m + 1))
    calc
      _ = Ideal.map ((qA (m + 1)).comp g) (C m) := by
        rw [Ideal.map_map, hFmkcomp]
      _ = Ideal.map ((qA (m + 1)).comp g) (Ideal.map incl (N m)) := by
        rw [hCeq m]
        show Ideal.map ((qA (m + 1)).comp g)
          (Ideal.closure (Ideal.map incl (N m))) = _
        exact RingHom.QuotientDiagram.map_closure_eq_of_discrete
          ((qA (m + 1)).comp g) hcont (Ideal.map incl (N m))
      _ = Ideal.map ((qA (m + 1)).comp (g.comp incl)) (N m) := by
        rw [Ideal.map_map]
        rw [RingHom.comp_assoc]
      _ = Ideal.map ((qA (m + 1)).comp f) (N m) := by rw [hgp]
      _ = (J m).map ((qA (m + 1)).comp φ) := by
        show Ideal.map ((qA (m + 1)).comp f) ((J m).map (MvPolynomial.C : B →+* P)) = _
        rw [Ideal.map_map]
        congr 1
        rw [RingHom.comp_assoc, hfcomp]
      _ = RingHom.ker (qT m) := (hdiag.2.2.1 m).symm
  have hkerLift (m : ℕ) (x : R ⧸ C m) (hx : F m x = 0) :
      ∃ y : R ⧸ C (m + 1), F (m + 1) y = 0 ∧ qS m y = x := by
    obtain ⟨u, hu⟩ := Ideal.Quotient.factor_surjective (hCanti (Nat.le_succ m)) x
    have hFuKer : F (m + 1) u ∈ RingHom.ker (qT m) := by
      rw [RingHom.mem_ker]
      show ((qT m).comp (F (m + 1))) u = 0
      rw [hFcomm m]
      show F m (qS m u) = 0
      exact (congrArg (F m) hu).trans hx
    have hkerImage : Ideal.map (F (m + 1)) (RingHom.ker (qS m)) =
        RingHom.ker (qT m) := by
      rw [hkerS m]
      exact hFimageKer m
    have hmem : F (m + 1) u ∈
        Ideal.map (F (m + 1)) (RingHom.ker (qS m)) := by
      rw [hkerImage]
      exact hFuKer
    have hmapset : (Ideal.map (F (m + 1)) (RingHom.ker (qS m)) :
        Set (A ⧸ I (m + 1))) =
          F (m + 1) '' (RingHom.ker (qS m) : Set (R ⧸ C (m + 1))) :=
      Ideal.map_eq_image_of_surjective (F (m + 1)) (hFsurj (m + 1))
    change F (m + 1) u ∈ (Ideal.map (F (m + 1)) (RingHom.ker (qS m)) :
      Set (A ⧸ I (m + 1))) at hmem
    rw [hmapset] at hmem
    obtain ⟨v, hv, hFuEq⟩ := hmem
    refine ⟨u - v, ?_, ?_⟩
    · rw [map_sub, hFuEq, sub_self]
    · rw [map_sub, RingHom.mem_ker.mp hv, sub_zero]
      exact hu
  let : ∀ m, DiscreteTopology (R ⧸ C m) := fun m =>
    QuotientAddGroup.discreteTopology_iff.mpr (by rw [hCeq]; exact hLopen m)
  let : ∀ m, DiscreteTopology (A ⧸ I m) := fun m =>
    QuotientAddGroup.discreteTopology_iff.mpr (hdiag.1 m)
  let hSBasis := quotientLimit_coordinate_hasBasis qS S (fun x m => x.2 m)
  let projS : ∀ m, S →+* R ⧸ C m := fun m =>
    (Pi.evalRingHom (fun k => R ⧸ C k) m).comp S.subtype
  let HF : ∀ m, S →+* A ⧸ I m := fun m => (F m).comp (projS m)
  have hHFcompat (x : S) (m : ℕ) :
      qT m (HF (m + 1) x) = HF m x := by
    show qT m (F (m + 1) (x.1 (m + 1))) = F m (x.1 m)
    have hc := congrArg (fun u : (R ⧸ C (m + 1)) →+* A ⧸ I m =>
      u (x.1 (m + 1))) (hFcomm m)
    simp only [RingHom.comp_apply] at hc
    exact hc.trans (congrArg (F m) (x.2 m))
  let H : S →+* T := RingHom.codRestrict (RingHom.pi HF) T (by
    intro x m
    exact hHFcompat x m)
  have hHcoord (x : S) (m : ℕ) : (H x).1 m = F m (x.1 m) := rfl
  have hHsurj : Function.Surjective H := by
    intro y
    obtain ⟨x₀, hx₀⟩ := hFsurj 0 (y.1 0)
    obtain ⟨x, hxcompat, hxF, -⟩ := compatible_lift_of_surjective_kernel_lift
      qS qT F hFcomm hFsurj hkerLift y.1 (fun m => y.2 m) x₀ hx₀
    exact ⟨⟨x, hxcompat⟩, Subtype.ext (funext hxF)⟩
  have hkerImage (m : ℕ) : {y : T | y.1 m = 0} ⊆
      H '' {x : S | x.1 m = 0} := by
    intro y hy
    obtain ⟨x, hxcompat, hxF, hxzero⟩ := compatible_lift_vanishing_until
      qS qT F hFcomm hFsurj hkerLift y.1 (fun k => y.2 k) m hy
    exact ⟨⟨x, hxcompat⟩, hxzero, Subtype.ext (funext hxF)⟩
  have hHopen : IsOpenMap H := by
    rw [isOpenMap_iff_nhds_le]
    intro x
    rw [Filter.le_map_iff]
    intro U hU
    have hU' : U ∈ nhds (x + (0 : S)) := by simpa using hU
    have hpre : (fun z : S => x + z) ⁻¹' U ∈ nhds (0 : S) :=
      (continuous_const_add x).continuousAt.preimage_mem_nhds hU'
    obtain ⟨m, -, hm⟩ := hSBasis.mem_iff.mp hpre
    have hcoord : Continuous (fun y : T => y.1 m) :=
      (continuous_apply m).comp continuous_subtype_val
    have hWopen : IsOpen {y : T | y.1 m = (H x).1 m} := by
      show IsOpen ((fun y : T => y.1 m) ⁻¹' ({(H x).1 m} : Set (A ⧸ I m)))
      exact (isOpen_discrete _).preimage hcoord
    have hW : {y : T | y.1 m = (H x).1 m} ∈ nhds (H x) :=
      hWopen.mem_nhds rfl
    apply Filter.mem_of_superset hW
    rintro y hy
    change y.1 m = (H x).1 m at hy
    have hzero : (y - H x).1 m = 0 := by
      show y.1 m - (H x).1 m = 0
      rw [hy, sub_self]
    have hyminus : ∀ k, qT k ((y - H x).1 (k + 1)) = (y - H x).1 k := by
      intro k
      show qT k (y.1 (k + 1) - (H x).1 (k + 1)) = y.1 k - (H x).1 k
      rw [map_sub, y.2 k, (H x).2 k]
    obtain ⟨zseq, hzcompat, hzF, hzzero⟩ := compatible_lift_vanishing_until
      qS qT F hFcomm hFsurj hkerLift (fun k => (y - H x).1 k) hyminus m hzero
    let z : S := ⟨zseq, hzcompat⟩
    have hz : z.1 m = 0 := hzzero
    have hHz : H z = y - H x := by
      apply Subtype.ext
      funext k
      show F k (z.1 k) = y.1 k - (H x).1 k
      rw [hHcoord x k]
      show F k (zseq k) = y.1 k - F k (x.1 k)
      rw [hzF k]
      rfl
    have hxz : x + z ∈ U := hm hz
    refine ⟨x + z, hxz, ?_⟩
    rw [map_add, hHz]
    abel
  have hfactor : g = eA.symm.toRingHom.comp (H.comp eR.toRingHom) := by
    apply RingHom.ext
    intro r
    apply eA.injective
    have hcoords : eA (g r) = H (eR r) := by
      apply Subtype.ext
      funext m
      calc
        (eA (g r)).1 m = qA m (g r) := heA.2.2 (g r) m
        _ = F m ((eR r).1 m) := by rw [heR.2.2 r m, hFmk]
        _ = (H (eR r)).1 m := (hHcoord (eR r) m).symm
    simpa using hcoords
  have hgsurj : Function.Surjective g := by
    intro a
    obtain ⟨x, hx⟩ := hHsurj (eA a)
    refine ⟨eR.symm x, ?_⟩
    rw [hfactor]
    show eA.symm (H (eR (eR.symm x))) = a
    rw [eR.apply_symm_apply, hx, eA.symm_apply_apply]
  let eRtop : R ≃ₜ S := Homeomorph.mk eR.toEquiv heR.1 heR.2.1
  let eAtop : T ≃ₜ A := Homeomorph.mk eA.symm.toEquiv heA.2.1 heA.1
  have hGopen : IsOpenMap g := by
    rw [hfactor]
    show IsOpenMap ((eAtop : T → A) ∘ (H ∘ (eRtop : R → S)))
    exact (Homeomorph.isOpenMap eAtop).comp
      (hHopen.comp (Homeomorph.isOpenMap eRtop))
  let K : Ideal R := RingHom.ker g
  have hKclosed : IsClosed (K : Set R) := by
    show IsClosed (g ⁻¹' ({0} : Set A))
    exact isClosed_singleton.preimage hgcont
  let eK : R ⧸ K ≃+* A := g.quotientKerEquivOfSurjective hgsurj
  have heKmk : eK.toRingHom.comp (Ideal.Quotient.mk K) = g := by
    ext r
    exact RingHom.quotientKerEquivOfSurjective_apply_mk (f := g) hgsurj r
  have heKfun : (fun r : R => eK (Ideal.Quotient.mk K r)) = g := by
    funext r
    exact congrArg (fun f : R →+* A => f r) heKmk
  have hquot := QuotientRing.isOpenQuotientMap_mk K
  have heKcont : Continuous eK := by
    apply hquot.continuous_comp_iff.mp
    show Continuous (fun r : R => eK (Ideal.Quotient.mk K r))
    rw [heKfun]
    exact hgcont
  have heKopen : IsOpenMap eK := by
    apply hquot.isOpenMap_iff.mpr
    show IsOpenMap (fun r : R => eK (Ideal.Quotient.mk K r))
    rw [heKfun]
    exact hGopen
  have heKsymmcont : Continuous eK.symm := by
    apply continuous_def.2
    intro U hU
    have hset : eK '' U = eK.symm ⁻¹' U := by
      ext a
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
      · intro ha
        exact ⟨eK.symm a, ha, eK.apply_symm_apply a⟩
    rw [← hset]
    exact heKopen U hU
  refine ⟨n, K, hKclosed, eK, heKcont, heKsymmcont, ?_⟩
  apply RingHom.ext
  intro b
  show eK (Ideal.Quotient.mk K (coeffToRestrictedPowerSeries B (Fin n) b)) = φ b
  rw [RingHom.quotientKerEquivOfSurjective_apply_mk hgsurj]
  show g (incl (MvPolynomial.C b)) = φ b
  rw [hg_incl]
  exact DFunLike.congr_fun hfcomp b

/-- The four finite-type conditions are equivalent, given the two (a) ↔ (c) implications. -/
private theorem finiteType_tfae_aux (φ : B →+* A) (hφ : Continuous φ)
    (hB : TopologicalRing.IsWeaklyAdmissible B)
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hBcount : (nhds (0 : B)).IsCountablyGenerated)
    (hto : FiniteTypeModuloEveryWeakIdeal φ → TopologicalRing.IsTopologicallyOfFiniteType φ)
    (hof : RingHom.IsTaut φ → TopologicalRing.IsTopologicallyOfFiniteType φ →
      FiniteTypeModuloEveryWeakIdeal φ) :
    List.TFAE [
      FiniteTypeModuloEveryWeakIdeal φ,
      FiniteTypeModuloCofinalWeakIdeals φ,
      RingHom.IsTaut φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ,
      HasRestrictedPowerSeriesPresentation φ] := by
  let a : Prop := FiniteTypeModuloEveryWeakIdeal φ
  let b : Prop := FiniteTypeModuloCofinalWeakIdeals φ
  let c : Prop := RingHom.IsTaut φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ
  let d : Prop := HasRestrictedPowerSeriesPresentation φ
  have hab : a ↔ b := by
    constructor
    · exact finiteTypeModuloEveryWeakIdeal_to_cofinal φ hB hBcount
    · exact finiteTypeModuloCofinal_to_every φ
  have hac : a ↔ c := by
    constructor
    · intro h
      exact ⟨h.1, hto h⟩
    · rintro ⟨htaut, hfinite⟩
      exact hof htaut hfinite
  have had : a ↔ d := by
    constructor
    · intro h
      exact restrictedPowerSeriesPresentation_of_taut_dense φ hφ hB hA hBcount h.1 (hto h)
    · exact finiteTypeModuloEveryWeakIdeal_of_presentation φ hφ
  apply List.tfae_of_forall (b := a)
  intro p hp
  simp only [List.mem_cons] at hp
  rcases hp with rfl | rfl | rfl | rfl | hp
  · exact Iff.rfl
  · exact hab.symm
  · exact hac.symm
  · exact had.symm
  · simp at hp

/-- The four finite-type conditions for a morphism of countably indexed weakly admissible rings
are equivalent. -/
public theorem finiteType_tfae (φ : B →+* A) (hφ : Continuous φ)
    (hB : TopologicalRing.IsWeaklyAdmissible B)
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hBcount : (nhds (0 : B)).IsCountablyGenerated)
    (hAcount : (nhds (0 : A)).IsCountablyGenerated) :
    List.TFAE [
      FiniteTypeModuloEveryWeakIdeal φ,
      FiniteTypeModuloCofinalWeakIdeals φ,
      RingHom.IsTaut φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ,
      HasRestrictedPowerSeriesPresentation φ] := by
  exact finiteType_tfae_aux φ hφ hB hA hBcount
    (finiteTypeModuloEveryWeakIdeal_to_topologicallyOfFiniteType φ hφ hB hA hBcount hAcount)
    (finiteTypeModuloEveryWeakIdeal_of_topologicallyOfFiniteType φ hφ)

/-- The four finite-type conditions for a morphism of countably indexed weakly admissible rings
are equivalent.

Stacks 0ANU states this for an arrow of `WAdm^count`, both rings weakly admissible with a
countable fundamental system of neighbourhoods of zero. Countable generation is assumed here
of the source only, which is strictly weaker and so covers every arrow of `WAdm^count`. The
hypothesis is spent twice and both times on the source: on condition (b), the cofinal form, by
`finiteTypeModuloEveryWeakIdeal_to_cofinal`, and on condition (d), the restricted power series
presentation, by `restrictedPowerSeriesPresentation_of_taut_dense`. Condition (c) costs no
countability at all — it is condition (2) of Stacks 0ANT verbatim, and
`isTopologicallyOfFiniteType_of_finiteTypeModuloEveryWeakIdeal` gets it from condition (a) for
any weakly pre-admissible source. -/
@[stacks 0ANU "equivalent_conditions"]
public theorem finiteType_tfae' (φ : B →+* A) (hφ : Continuous φ)
    (hB : TopologicalRing.IsWeaklyAdmissible B)
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hBcount : (nhds (0 : B)).IsCountablyGenerated) :
    List.TFAE [
      FiniteTypeModuloEveryWeakIdeal φ,
      FiniteTypeModuloCofinalWeakIdeals φ,
      RingHom.IsTaut φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ,
      HasRestrictedPowerSeriesPresentation φ] := by
  exact finiteType_tfae_aux φ hφ hB hA hBcount
    (isTopologicallyOfFiniteType_of_finiteTypeModuloEveryWeakIdeal' φ hB.1)
    (finiteTypeModuloEveryWeakIdeal_of_topologicallyOfFiniteType' φ hφ)

end

end TopologicalRing

end
