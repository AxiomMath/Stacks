module

public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible

/-!
# Tautness through the diagram of discrete quotients

A continuous homomorphism of linearly topologized rings is taut exactly when the discrete
quotients of the target, taken along the extensions of a fundamental sequence of open ideals
of the source, reconstruct the target as their inverse limit.

## References

* [Stacks Project, Tag 0ANJ](https://stacks.math.columbia.edu/tag/0ANJ)
-/

@[expose] public section

namespace RingHom.QuotientDiagram

section

open Filter


/-- A decreasing sequence of weak ideals of definition which is a neighbourhood basis of
zero. -/
public abbrev IsFundamentalSequence {B : Type*} [CommRing B] [TopologicalSpace B]
    (J : ℕ → Ideal B) : Prop :=
  (∀ n, TopologicalRing.IsWeakIdealOfDefinition (J n)) ∧ Antitone J ∧
    (nhds (0 : B)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ (J n : Set B))

/-- The closed ideal of the target induced by the `n`-th ideal in a source sequence. -/
public abbrev targetIdeal {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B]
    (f : B →+* A) (J : ℕ → Ideal B) (n : ℕ) : Ideal A :=
  Ideal.closure ((J n).map f)

/-- The canonical transition map between successive target quotients. -/
public noncomputable def quotientTransition {A B : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A]
    [CommRing B] (f : B →+* A) (J : ℕ → Ideal B) (hJ : Antitone J) (n : ℕ) :
    A ⧸ targetIdeal f J (n + 1) →+* A ⧸ targetIdeal f J n :=
  Ideal.Quotient.factor (by
    change closure ((J (n + 1)).map f : Set A) ⊆ closure ((J n).map f : Set A)
    exact closure_mono (Ideal.map_mono (hJ (Nat.le_succ n))))

/-- The inverse limit of the canonical target quotients as a subring of their product. -/
public noncomputable def quotientLimit {A B : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A]
    [CommRing B] (f : B →+* A) (J : ℕ → Ideal B) (hJ : Antitone J) :
    Subring (∀ n, A ⧸ targetIdeal f J n) where
  carrier := {x | ∀ n, quotientTransition f J hJ n (x (n + 1)) = x n}
  zero_mem' := by simp [quotientTransition]
  one_mem' := by simp [quotientTransition]
  add_mem' {x y} hx hy := by
    intro n
    change quotientTransition f J hJ n (x (n + 1) + y (n + 1)) = x n + y n
    rw [map_add, hx n, hy n]
  mul_mem' {x y} hx hy := by
    intro n
    change quotientTransition f J hJ n (x (n + 1) * y (n + 1)) = x n * y n
    rw [map_mul, hx n, hy n]
  neg_mem' {x} hx := by
    intro n
    change quotientTransition f J hJ n (-x (n + 1)) = -x n
    rw [map_neg, hx n]

/-- The canonical map from the source quotient into a stage of the target diagram. -/
public noncomputable def sourceQuotientToTargetQuotient {A B : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [CommRing B]
    (f : B →+* A) (J : ℕ → Ideal B) (n : ℕ) :
    B ⧸ J n →+* A ⧸ targetIdeal f J n :=
  Ideal.Quotient.lift (J n) ((Ideal.Quotient.mk (targetIdeal f J n)).comp f) (by
    intro x hx
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact subset_closure (Ideal.mem_map_of_mem f hx))

/-- The canonical quotient system attached to `J` is a quotient diagram for `f`: its stages
form a neighbourhood basis, each transition quotients by the indicated extended source ideal,
and the target is their topological inverse limit. -/
public abbrev HasQuotientDiagram {A B : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [CommRing B]
    (f : B →+* A) (J : ℕ → Ideal B) (hJ : Antitone J) : Prop :=
  (∀ n, IsOpen (targetIdeal f J n : Set A)) ∧
    (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ (targetIdeal f J n : Set A)) ∧
    (∀ n, RingHom.ker (quotientTransition f J hJ n) =
      (J n).map ((Ideal.Quotient.mk (targetIdeal f J (n + 1))).comp f)) ∧
    ∃ e : A ≃+* quotientLimit f J hJ,
      Continuous e ∧ Continuous e.symm ∧
        ∀ (a : A) (n : ℕ),
          ((e a : quotientLimit f J hJ) : ∀ n, A ⧸ targetIdeal f J n) n =
          Ideal.Quotient.mk (targetIdeal f J n) a

/-- Every open ideal of the source contains a term of the fundamental sequence, so its extension
closure contains the corresponding target ideal. -/
private theorem exists_targetIdeal_subset {A B : Type*}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (f : B →+* A) (J : ℕ → Ideal B) (hJ : IsFundamentalSequence J)
    {I : Ideal B} (hI : IsOpen (I : Set B)) :
    ∃ n, (targetIdeal f J n : Set A) ⊆ Ideal.closure (I.map f) := by
  obtain ⟨n, _, hn⟩ := hJ.2.2.mem_iff.mp (hI.mem_nhds I.zero_mem)
  exact ⟨n, closure_mono (Ideal.map_mono hn)⟩

private theorem targetIdeal_hasBasis_of_isTaut {A B : Type*}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (f : B →+* A) (J : ℕ → Ideal B) (hJ : IsFundamentalSequence J)
    (ht : RingHom.IsTaut f) :
    (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ (targetIdeal f J n : Set A)) :=
  ht.2.to_hasBasis
    (fun _ hI ↦ (exists_targetIdeal_subset f J hJ hI).imp fun _ hn ↦ ⟨trivial, hn⟩)
    fun n _ ↦ ⟨J n, (hJ.1 n).1, Set.Subset.rfl⟩

private theorem isTaut_of_targetIdeal_hasBasis {A B : Type*}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (f : B →+* A) (J : ℕ → Ideal B) (hJ : IsFundamentalSequence J)
    (hopen : ∀ n, IsOpen (targetIdeal f J n : Set A))
    (hbasis : (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ (targetIdeal f J n : Set A))) :
    RingHom.IsTaut f :=
  ⟨fun _ hI ↦ have ⟨n, hn⟩ := exists_targetIdeal_subset f J hJ hI
      Ideal.isOpen_of_isOpen_subideal hn (hopen n),
    hbasis.to_hasBasis (fun n _ ↦ ⟨J n, (hJ.1 n).1, Set.Subset.rfl⟩)
      fun _ hI ↦ (exists_targetIdeal_subset f J hJ hI).imp fun _ hn ↦ ⟨trivial, hn⟩⟩

/-- A continuous ring map to a discrete ring maps the closure of an ideal and the ideal itself to
the same ideal. -/
public theorem map_closure_eq_of_discrete {A C : Type*}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing C] [TopologicalSpace C] [DiscreteTopology C]
    (g : A →+* C) (hg : Continuous g) (L : Ideal A) :
    L.closure.map g = L.map g := by
  refine le_antisymm ?_ (Ideal.map_mono subset_closure)
  apply Ideal.map_le_iff_le_comap.mpr
  show closure (L : Set A) ⊆ g ⁻¹' (L.map g : Set C)
  exact closure_minimal (fun x hx ↦ Ideal.mem_map_of_mem g hx)
    ((isClosed_discrete _).preimage hg)

/-- If the target ideals are open, the quotient of the target by each of them is discrete. -/
public theorem targetQuotient_discrete {A B : Type*}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [CommRing B]
    (f : B →+* A) (J : ℕ → Ideal B)
    (hopen : ∀ n, IsOpen (targetIdeal f J n : Set A)) (n : ℕ) :
    DiscreteTopology (A ⧸ targetIdeal f J n) := by
  let K := targetIdeal f J n
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have heq : (Ideal.Quotient.mk K) '' (K : Set A) = {(0 : A ⧸ K)} := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
    · rintro rfl
      exact ⟨0, K.zero_mem, map_zero _⟩
  rw [← heq]
  exact (QuotientRing.isOpenMap_coe K) _ (hopen n)

private theorem transition_ker_of_open {A B : Type*}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [CommRing B]
    (f : B →+* A) (J : ℕ → Ideal B) (hJ : Antitone J)
    (hopen : ∀ n, IsOpen (targetIdeal f J n : Set A)) (n : ℕ) :
    RingHom.ker (quotientTransition f J hJ n) =
      (J n).map ((Ideal.Quotient.mk (targetIdeal f J (n + 1))).comp f) := by
  let K := targetIdeal f J (n + 1)
  let I := targetIdeal f J n
  let : DiscreteTopology (A ⧸ K) := targetQuotient_discrete f J hopen (n + 1)
  have hc : Continuous (Ideal.Quotient.mk K : A → A ⧸ K) := continuous_quot_mk
  have hmap : (J n).map ((Ideal.Quotient.mk K).comp f) = I.map (Ideal.Quotient.mk K) := by
    rw [← Ideal.map_map]
    exact (map_closure_eq_of_discrete (Ideal.Quotient.mk K) hc ((J n).map f)).symm
  show RingHom.ker (Ideal.Quotient.factor (show K ≤ I from
    closure_mono (Ideal.map_mono (hJ (Nat.le_succ n))))) = _
  rw [Ideal.Quotient.factor_ker, ← hmap]

/-- The canonical map from the target to the inverse limit of its quotients by the target
ideals. -/
public noncomputable def toQuotientLimit {A B : Type*}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [CommRing B]
    (f : B →+* A) (J : ℕ → Ideal B) (hJ : Antitone J) :
    A →+* quotientLimit f J hJ :=
  RingHom.codRestrict (RingHom.pi fun n ↦ Ideal.Quotient.mk (targetIdeal f J n))
    (quotientLimit f J hJ) (by
      intro a n
      simp [quotientTransition])

/-- The canonical map to the inverse limit is injective when the target is Hausdorff and the
target ideals form a neighbourhood basis of zero. -/
public theorem toQuotientLimit_injective {A B : Type*}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] [CommRing B]
    (f : B →+* A) (J : ℕ → Ideal B) (hJ : Antitone J)
    (hbasis : (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ (targetIdeal f J n : Set A))) :
    Function.Injective (toQuotientLimit f J hJ) := by
  intro a b hab
  have hmem (n : ℕ) : a - b ∈ targetIdeal f J n :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).mp
      (congrArg (fun x : quotientLimit f J hJ ↦ x.1 n) hab)
  have hzero : a - b = 0 := by
    by_contra hne
    have ho : ({a - b}ᶜ : Set A) ∈ nhds (0 : A) :=
      isClosed_singleton.isOpen_compl.mem_nhds (by simpa using (Ne.symm hne))
    obtain ⟨n, _, hn⟩ := hbasis.mem_iff.mp ho
    exact (hn (hmem n)) (by simp)
  exact sub_eq_zero.mp hzero

/-- The canonical map to the inverse limit is surjective when the target ideals are open, form a
neighbourhood basis of zero, and the target is complete. -/
public theorem toQuotientLimit_surjective {A B : Type*}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [CommRing B]
    (f : B →+* A) (J : ℕ → Ideal B) (hJ : Antitone J)
    (hopen : ∀ n, IsOpen (targetIdeal f J n : Set A))
    (hbasis : (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ (targetIdeal f J n : Set A)))
    (hcomplete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) :
    Function.Surjective (toQuotientLimit f J hJ) := by
  intro x
  let K : ℕ → Ideal A := targetIdeal f J
  have hK : Antitone K := fun m n hmn ↦ closure_mono (Ideal.map_mono (hJ hmn))
  choose a ha using (fun n ↦ Ideal.Quotient.mk_surjective (x.1 n))
  have hstage (m n : ℕ) (hmn : m ≤ n) :
      Ideal.Quotient.mk (K m) (a n) = x.1 m := by
    have hc : x.1 m = Ideal.Quotient.factor (hK hmn) (x.1 n) :=
      Ideal.Quotient.eq_factor_of_eq_factor_succ hK x.1 (fun k ↦ (x.2 k).symm) hmn
    rw [hc, ← ha n]
    rfl
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  let : CompleteSpace A := hcomplete
  let : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  have hC : CauchySeq a := by
    refine (IsUniformAddGroup.cauchy_map_iff_tendsto Filter.atTop a).2 ⟨inferInstance, ?_⟩
    apply hbasis.tendsto_right_iff.mpr
    intro k _
    rw [prod_atTop_atTop_eq]
    apply eventually_atTop_prod_self.mpr
    refine ⟨k, fun n m hn hm ↦ ?_⟩
    show a n - a m ∈ K k
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem (a n) (a m)).mp
      ((hstage k n hn).trans (hstage k m hm).symm)
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hC
  refine ⟨b, ?_⟩
  apply Subtype.ext
  funext n
  let : DiscreteTopology (A ⧸ K n) := targetQuotient_discrete f J hopen n
  have hcont : Continuous (Ideal.Quotient.mk (K n) : A → A ⧸ K n) := continuous_quot_mk
  have hconst : Tendsto (fun m ↦ Ideal.Quotient.mk (K n) (a m))
      Filter.atTop (nhds (x.1 n)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with m hm
    exact (hstage n m hm).symm
  exact tendsto_nhds_unique (hcont.tendsto b |>.comp hb) hconst

/-- If the target is complete and Hausdorff and the open target ideals form a neighbourhood
basis of zero, the target is isomorphic to the inverse limit of its quotients by a ring
isomorphism which is a homeomorphism and is compatible with the canonical projections. -/
public theorem quotientLimit_equiv {A B : Type*}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [CommRing B]
    (f : B →+* A) (J : ℕ → Ideal B) (hJ : Antitone J)
    (hopen : ∀ n, IsOpen (targetIdeal f J n : Set A))
    (hbasis : (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ (targetIdeal f J n : Set A)))
    (hcomplete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hT2 : T2Space A) :
    ∃ e : A ≃+* quotientLimit f J hJ,
      Continuous e ∧ Continuous e.symm ∧
        ∀ (a : A) (n : ℕ),
          ((e a : quotientLimit f J hJ) : ∀ n, A ⧸ targetIdeal f J n) n =
          Ideal.Quotient.mk (targetIdeal f J n) a := by
  let : T2Space A := hT2
  let e : A ≃+* quotientLimit f J hJ := RingEquiv.ofBijective
    (toQuotientLimit f J hJ)
    ⟨toQuotientLimit_injective f J hJ hbasis,
      toQuotientLimit_surjective f J hJ hopen hbasis hcomplete⟩
  refine ⟨e, ?_, ?_, ?_⟩
  · show Continuous (toQuotientLimit f J hJ)
    apply Continuous.subtype_mk
    exact continuous_pi fun n ↦ continuous_quot_mk
  · apply continuous_of_tendsto_nhds_zero e.symm.toAddMonoidHom
    apply hbasis.tendsto_right_iff.mpr
    intro n _
    let : DiscreteTopology (A ⧸ targetIdeal f J n) :=
      targetQuotient_discrete f J hopen n
    have ho : {x : quotientLimit f J hJ | x.1 n = 0} ∈ nhds (0 : quotientLimit f J hJ) :=
      ((isOpen_discrete {0}).preimage
        ((continuous_apply n).comp continuous_subtype_val)).mem_nhds (by simp)
    apply Filter.mem_of_superset ho
    intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have heq := congrArg (fun y : quotientLimit f J hJ ↦ y.1 n) (e.apply_symm_apply x)
    change Ideal.Quotient.mk (targetIdeal f J n) (e.symm x) = x.1 n at heq
    exact heq.trans hx
  · exact fun _ _ ↦ rfl

/-- A continuous arrow of weakly admissible linearly topologized rings is taut if and only if
its canonical quotients along any chosen decreasing fundamental sequence form the quotient
diagram whose topological inverse limit is the target. -/
@[stacks 0ANJ "taut_iff_quotient_diagram"]
public theorem isTaut_iff_hasQuotientDiagram {A B : Type*}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    (f : B →+* A) (hf : Continuous f)
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hB : TopologicalRing.IsWeaklyAdmissible B)
    (J : ℕ → Ideal B) (hJ : IsFundamentalSequence J) :
    RingHom.IsTaut f ↔ HasQuotientDiagram f J hJ.2.1 := by
  refine ⟨fun ht ↦ ?_, fun hd ↦ isTaut_of_targetIdeal_hasBasis f J hJ hd.1 hd.2.1⟩
  have hopen (n : ℕ) : IsOpen (targetIdeal f J n : Set A) := ht.1 (J n) (hJ.1 n).1
  have hbasis := targetIdeal_hasBasis_of_isTaut f J hJ ht
  exact ⟨hopen, hbasis, transition_ker_of_open f J hJ.2.1 hopen,
    quotientLimit_equiv f J hJ.2.1 hopen hbasis hA.2.1 hA.2.2⟩

end

end RingHom.QuotientDiagram

end
