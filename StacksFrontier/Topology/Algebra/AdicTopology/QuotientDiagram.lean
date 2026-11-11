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

## Main results

* `RingHom.QuotientDiagram.isTaut_iff_exists_isQuotientDiagram`: Stacks 0ANJ (a) ⇔ (b), with
  (b) the existence of some diagram of discrete rings `Aₙ` over `B ⧸ J n` with
  `Aₙ₊₁ ⧸ J n Aₙ₊₁ = Aₙ` and `A = lim Aₙ` topologically.
* `RingHom.QuotientDiagram.isTaut_iff_hasQuotientDiagram`: the same with the canonical
  quotients `A ⧸ closure (J n A)` in place of an arbitrary diagram.

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
  change closure (L : Set A) ⊆ g ⁻¹' (L.map g : Set C)
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
  change RingHom.ker (Ideal.Quotient.factor (show K ≤ I from
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
    change a n - a m ∈ K k
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
  · change Continuous (toQuotientLimit f J hJ)
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
diagram whose topological inverse limit is the target.

This is the specialised form of Stacks 0ANJ (b) for the canonical quotients
`A ⧸ closure (J n A)`; the existential form of (b), over arbitrary diagrams, is
`isTaut_iff_exists_isQuotientDiagram`. -/
public theorem isTaut_iff_hasQuotientDiagram {A B : Type*}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    (f : B →+* A) (hA : TopologicalRing.IsWeaklyAdmissible A)
    (J : ℕ → Ideal B) (hJ : IsFundamentalSequence J) :
    RingHom.IsTaut f ↔ HasQuotientDiagram f J hJ.2.1 := by
  refine ⟨fun ht ↦ ?_, fun hd ↦ isTaut_of_targetIdeal_hasBasis f J hJ hd.1 hd.2.1⟩
  have hopen (n : ℕ) : IsOpen (targetIdeal f J n : Set A) := ht.1 (J n) (hJ.1 n).1
  have hbasis := targetIdeal_hasBasis_of_isTaut f J hJ ht
  exact ⟨hopen, hbasis, transition_ker_of_open f J hJ.2.1 hopen,
    quotientLimit_equiv f J hJ.2.1 hopen hbasis hA.2.1 hA.2.2⟩

/-- The inverse limit of an inverse system of rings indexed by `ℕ`, as the subring of
compatible sequences in the product. -/
public def diagramLimit {Aₙ : ℕ → Type*} [∀ n, CommRing (Aₙ n)]
    (t : ∀ n, Aₙ (n + 1) →+* Aₙ n) : Subring (∀ n, Aₙ n) where
  carrier := {x | ∀ n, t n (x (n + 1)) = x n}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' {x y} hx hy n := by
    change t n (x (n + 1) + y (n + 1)) = x n + y n
    rw [map_add, hx n, hy n]
  mul_mem' {x y} hx hy n := by
    change t n (x (n + 1) * y (n + 1)) = x n * y n
    rw [map_mul, hx n, hy n]
  neg_mem' {x} hx n := by
    change t n (-x (n + 1)) = -x n
    rw [map_neg, hx n]

/-- The diagram of Stacks 0ANJ (b): discrete rings `Aₙ` with maps `π n : A → Aₙ`, transitions
`t n : Aₙ₊₁ → Aₙ` and maps `σ n : B ⧸ J n → Aₙ` making the ladder from `B → A` commute,
such that `t n` identifies `Aₙ₊₁ ⧸ J n Aₙ₊₁` with `Aₙ`, and such that `A = lim Aₙ` as topological
rings, through the maps `π n`. -/
public def IsQuotientDiagram {A B : Type*} [CommRing A] [TopologicalSpace A] [CommRing B]
    (f : B →+* A) (J : ℕ → Ideal B) (hJ : Antitone J)
    {Aₙ : ℕ → Type*} [∀ n, CommRing (Aₙ n)] [∀ n, TopologicalSpace (Aₙ n)]
    (π : ∀ n, A →+* Aₙ n) (t : ∀ n, Aₙ (n + 1) →+* Aₙ n) (σ : ∀ n, B ⧸ J n →+* Aₙ n) :
    Prop :=
  (∀ n, DiscreteTopology (Aₙ n)) ∧
    (∀ n, (σ n).comp (Ideal.Quotient.mk (J n)) = (π n).comp f) ∧
    (∀ n, (t n).comp (π (n + 1)) = π n) ∧
    (∀ n, (t n).comp (σ (n + 1)) = (σ n).comp (Ideal.Quotient.factor (hJ (Nat.le_succ n)))) ∧
    (∀ n, Function.Surjective (t n) ∧
      RingHom.ker (t n) = (J n).map ((σ (n + 1)).comp (Ideal.Quotient.mk (J (n + 1))))) ∧
    ∃ e : A ≃+* diagramLimit t,
      Continuous e ∧ Continuous e.symm ∧ ∀ (a : A) (n : ℕ), (e a : ∀ n, Aₙ n) n = π n a

/-- An upward chain through surjective transitions starting at `y` in stage `n`. -/
private noncomputable def upSeq {Aₙ : ℕ → Type*} [∀ n, CommRing (Aₙ n)]
    (t : ∀ n, Aₙ (n + 1) →+* Aₙ n) (ht : ∀ n, Function.Surjective (t n)) (n : ℕ) (y : Aₙ n) :
    ∀ m, Aₙ m
  | 0 => if h : n = 0 then h ▸ y else 0
  | m + 1 => if h : n = m + 1 then h ▸ y else Function.surjInv (ht m) (upSeq t ht n y m)

private theorem upSeq_self {Aₙ : ℕ → Type*} [∀ n, CommRing (Aₙ n)]
    (t : ∀ n, Aₙ (n + 1) →+* Aₙ n) (ht : ∀ n, Function.Surjective (t n)) (n : ℕ) (y : Aₙ n) :
    upSeq t ht n y n = y := by
  cases n <;> simp [upSeq]

private theorem upSeq_succ {Aₙ : ℕ → Type*} [∀ n, CommRing (Aₙ n)]
    (t : ∀ n, Aₙ (n + 1) →+* Aₙ n) (ht : ∀ n, Function.Surjective (t n)) (n : ℕ) (y : Aₙ n)
    {m : ℕ} (hm : n ≤ m) :
    t m (upSeq t ht n y (m + 1)) = upSeq t ht n y m := by
  simp only [upSeq, show ¬n = m + 1 by omega, ↓reduceDIte, Function.surjInv_eq]

/-- A compatible sequence through surjective transitions with value `y` in stage `n`. -/
private noncomputable def liftSeq {Aₙ : ℕ → Type*} [∀ n, CommRing (Aₙ n)]
    (t : ∀ n, Aₙ (n + 1) →+* Aₙ n) (ht : ∀ n, Function.Surjective (t n)) (n : ℕ) (y : Aₙ n)
    (m : ℕ) : Aₙ m :=
  if n ≤ m then upSeq t ht n y m else t m (liftSeq t ht n y (m + 1))
termination_by n - m

private theorem liftSeq_mem {Aₙ : ℕ → Type*} [∀ n, CommRing (Aₙ n)]
    (t : ∀ n, Aₙ (n + 1) →+* Aₙ n) (ht : ∀ n, Function.Surjective (t n)) (n : ℕ) (y : Aₙ n) :
    liftSeq t ht n y ∈ diagramLimit t := by
  intro m
  by_cases hm : n ≤ m
  · rw [liftSeq.eq_1 t ht n y (m + 1), liftSeq.eq_1 t ht n y m]
    simp only [show n ≤ m + 1 by omega, hm, ↓reduceIte]
    exact upSeq_succ t ht n y hm
  · conv_rhs => rw [liftSeq]
    simp only [hm, ↓reduceIte]

private theorem liftSeq_self {Aₙ : ℕ → Type*} [∀ n, CommRing (Aₙ n)]
    (t : ∀ n, Aₙ (n + 1) →+* Aₙ n) (ht : ∀ n, Function.Surjective (t n)) (n : ℕ) (y : Aₙ n) :
    liftSeq t ht n y n = y := by
  rw [liftSeq]
  simp only [le_rfl, ↓reduceIte, upSeq_self]

/-- The converse half of Stacks 0ANJ: a diagram as in (b) makes `f` taut. The kernels of the
projections are the closed extensions of the `J n`, because each transition kills exactly the
extension of `J n`. -/
private theorem isTaut_of_isQuotientDiagram {A B : Type*}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (f : B →+* A) (J : ℕ → Ideal B) (hJ : IsFundamentalSequence J)
    {Aₙ : ℕ → Type*} [∀ n, CommRing (Aₙ n)] [∀ n, TopologicalSpace (Aₙ n)]
    (π : ∀ n, A →+* Aₙ n) (t : ∀ n, Aₙ (n + 1) →+* Aₙ n) (σ : ∀ n, B ⧸ J n →+* Aₙ n)
    (hd : IsQuotientDiagram f J hJ.2.1 π t σ) : RingHom.IsTaut f := by
  obtain ⟨hdisc, hσ, htπ, -, hker, e, he, hes, heπ⟩ := hd
  have : ∀ n, DiscreteTopology (Aₙ n) := hdisc
  let I : ℕ → Ideal A := fun n ↦ RingHom.ker (π n)
  have hπc (n : ℕ) : Continuous (π n) := by
    have : (π n : A → Aₙ n) = (fun x : diagramLimit t ↦ (x : ∀ n, Aₙ n) n) ∘ e :=
      funext fun a ↦ (heπ a n).symm
    rw [this]
    exact ((continuous_apply n).comp continuous_subtype_val).comp he
  have hIopen (n : ℕ) : IsOpen (I n : Set A) :=
    (isOpen_discrete ({0} : Set (Aₙ n))).preimage (hπc n)
  have hIclosed (n : ℕ) : IsClosed (I n : Set A) :=
    (isClosed_discrete ({0} : Set (Aₙ n))).preimage (hπc n)
  have hIanti : Antitone I := antitone_nat_of_succ_le fun n a ha ↦ by
    change π n a = 0
    rw [← htπ n, RingHom.comp_apply]
    change π (n + 1) a = 0 at ha
    rw [ha, map_zero]
  -- the topology of `A` is the inverse limit topology
  have hnhds : nhds (0 : A) = ⨅ n, Filter.principal (I n : Set A) := by
    let h : A ≃ₜ diagramLimit t :=
      { toEquiv := e.toEquiv, continuous_toFun := he, continuous_invFun := hes }
    rw [h.nhds_eq_comap, nhds_subtype, Filter.comap_comap, nhds_pi, Filter.pi,
      Filter.comap_iInf]
    congr 1
    funext n
    rw [Filter.comap_comap, nhds_discrete, Filter.comap_pure]
    congr 1
    ext a
    change (e a : ∀ n, Aₙ n) n = (e 0 : ∀ n, Aₙ n) n ↔ π n a = 0
    rw [heπ, heπ, map_zero]
  have hbasis : (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ (I n : Set A)) := by
    rw [hnhds]
    exact Filter.hasBasis_iInf_principal
      (directed_of_isDirected_le fun _ _ hij ↦ hIanti hij)
  -- the projections are surjective
  have hπs (n : ℕ) : Function.Surjective (π n) := by
    intro y
    refine ⟨e.symm ⟨liftSeq t (fun m ↦ (hker m).1) n y,
      liftSeq_mem t (fun m ↦ (hker m).1) n y⟩, ?_⟩
    rw [← heπ, RingEquiv.apply_symm_apply]
    exact liftSeq_self t _ n y
  -- each kernel is the extension of `J n` plus the next kernel
  have hstep (n : ℕ) : I n ≤ (J n).map f ⊔ I (n + 1) := by
    intro a ha
    have hmem : π (n + 1) a ∈ ((J n).map f).map (π (n + 1)) := by
      rw [Ideal.map_map, ← hσ (n + 1), ← (hker n).2, RingHom.mem_ker, ← RingHom.comp_apply,
        htπ n]
      exact ha
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ (hπs (n + 1))] at hmem
    exact hmem
  have hsup (n m : ℕ) (hnm : n ≤ m) : I n ≤ (J n).map f ⊔ I m := by
    induction m, hnm using Nat.le_induction with
    | base => exact le_sup_right
    | succ m hnm ih =>
      refine ih.trans (sup_le le_sup_left ((hstep m).trans (sup_le ?_ le_sup_right)))
      exact (Ideal.map_mono (hJ.2.1 hnm)).trans le_sup_left
  have hJI (n : ℕ) : (J n).map f ≤ I n := by
    refine Ideal.map_le_iff_le_comap.mpr fun b hb ↦ ?_
    change π n (f b) = 0
    rw [← RingHom.comp_apply, ← hσ n, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero]
  have hclosure (n : ℕ) : (targetIdeal f J n : Set A) = I n := by
    refine Set.Subset.antisymm (closure_minimal (hJI n) (hIclosed n)) fun a ha ↦ ?_
    change a ∈ closure ((J n).map f : Set A)
    rw [mem_closure_iff_nhds]
    intro U hU
    have hU' : (fun u : A ↦ a - u) ⁻¹' U ∈ nhds (0 : A) :=
      (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨m, -, hm⟩ := hbasis.mem_iff.mp hU'
    obtain ⟨s, hs, u, hu, hsu⟩ :=
      Submodule.mem_sup.mp (hsup n (max n m) (le_max_left n m) ha)
    refine ⟨s, ?_, hs⟩
    have : a - u = s := by rw [← hsu]; ring
    rw [← this]
    exact hm (hIanti (le_max_right n m) hu)
  refine isTaut_of_targetIdeal_hasBasis f J hJ (fun n ↦ by rw [hclosure]; exact hIopen n) ?_
  simpa only [hclosure] using hbasis

/-- A continuous arrow `B → A` of weakly admissible linearly topologized rings is taut if and only
if, for the given decreasing fundamental sequence `J n` of weak ideals of definition of `B`, there
exist discrete rings `Aₙ` forming a commutative diagram over `B → B ⧸ J n` with
`Aₙ₊₁ ⧸ J n Aₙ₊₁ = Aₙ` and `A = lim Aₙ` as topological rings. -/
@[stacks 0ANJ "(a) ⇔ (b), for a given fundamental sequence"]
public theorem isTaut_iff_exists_isQuotientDiagram.{u} {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    (f : B →+* A) (_hf : Continuous f)
    (hA : TopologicalRing.IsWeaklyAdmissible A) (_hB : TopologicalRing.IsWeaklyAdmissible B)
    (J : ℕ → Ideal B) (hJ : IsFundamentalSequence J) :
    RingHom.IsTaut f ↔
      ∃ (Aₙ : ℕ → Type u) (_ : ∀ n, CommRing (Aₙ n)) (_ : ∀ n, TopologicalSpace (Aₙ n))
        (π : ∀ n, A →+* Aₙ n) (t : ∀ n, Aₙ (n + 1) →+* Aₙ n) (σ : ∀ n, B ⧸ J n →+* Aₙ n),
        IsQuotientDiagram f J hJ.2.1 π t σ := by
  refine ⟨fun ht ↦ ?_, fun ⟨_, _, _, π, t, σ, hd⟩ ↦ isTaut_of_isQuotientDiagram f J hJ π t σ hd⟩
  obtain ⟨hopen, -, hker, e, he, hes, heπ⟩ :=
    (isTaut_iff_hasQuotientDiagram f hA J hJ).mp ht
  refine ⟨fun n ↦ A ⧸ targetIdeal f J n, inferInstance, inferInstance,
    fun n ↦ Ideal.Quotient.mk _, quotientTransition f J hJ.2.1,
    sourceQuotientToTargetQuotient f J, targetQuotient_discrete f J hopen, fun n ↦ ?_,
    fun n ↦ ?_, fun n ↦ ?_, fun n ↦ ⟨?_, ?_⟩, e, he, hes, heπ⟩
  · exact RingHom.ext fun _ ↦ rfl
  · exact RingHom.ext fun _ ↦ rfl
  · exact Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl)
  · intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  · rw [hker n]
    rfl

end

end RingHom.QuotientDiagram

end
