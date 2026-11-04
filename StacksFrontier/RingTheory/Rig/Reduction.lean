module

public import Mathlib.RingTheory.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicRingMap
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteType
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible

/-!
# Finite type on reductions

Let `φ : A →+* B` be a continuous homomorphism of linearly topologized commutative rings.
Reduction by the ideals `topologicalNilradical A` and `topologicalNilradical B` of
topologically nilpotent elements turns `φ` into a homomorphism of ordinary rings, and `φ` is
said to be *of finite type on reductions* when that induced homomorphism is of finite type.

This file compares that condition with topological finite type.  Tautness of `φ` together with
topological finite type implies finite type on reductions, as soon as the source has a weak
ideal of definition.  Conversely, if the target is Noetherian and weakly admissible, finite
type on reductions implies topological finite type.  Combining the two directions gives an
equivalence for adic homomorphisms.

## Main definitions

* `Rig.IsFiniteTypeOnReductions` — the induced map on the quotients by the topological
  nilradicals is of finite type.

## Main results

* `Rig.isFiniteTypeOnReductions_of_isTaut_of_isTopologicallyOfFiniteType` — a taut
  homomorphism of topological finite type is of finite type on reductions.
* `Rig.isTopologicallyOfFiniteType_of_isFiniteTypeOnReductions` — over a Noetherian weakly
  admissible target, finite type on reductions implies topological finite type.
* `Rig.isFiniteTypeOnReductions_iff_isTopologicallyOfFiniteType` — the two conditions agree
  for an adic homomorphism into a Noetherian weakly admissible ring.

## Implementation notes

The source states these results for arrows of `WAdm^count` and `WAdm^Noeth`.  Only the
hypotheses actually used are imposed here: a weak ideal of definition in the source for the
first implication, Noetherianity and weak admissibility of the target for the second.
Neither completeness, separatedness, nor countability is required.

## References

* [Stacks Project, Tag 0GC2](https://stacks.math.columbia.edu/tag/0GC2)
* [Stacks Project, Tag 0GC5](https://stacks.math.columbia.edu/tag/0GC5)
* [Stacks Project, Tag 0GC6](https://stacks.math.columbia.edu/tag/0GC6)
* [Stacks Project, Tag 0GG6](https://stacks.math.columbia.edu/tag/0GG6)
-/

@[expose] public section

namespace Rig

/-- A continuous homomorphism of linearly topologized commutative rings is *of finite type on
reductions* if the induced homomorphism between the quotients by their topological
nilradicals is of finite type. -/
@[stacks 0GC2 "finite_type_on_reductions"]
public abbrev IsFiniteTypeOnReductions {A B : Type*} [CommRing A] [TopologicalSpace A]
    [IsLinearTopology A A] [CommRing B] [TopologicalSpace B] [IsLinearTopology B B]
    (φ : A →+* B) (hφ : Continuous φ) : Prop :=
  (Ideal.quotientMap (topologicalNilradical B) φ fun _ hx ↦
    IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr
      ((IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp hx).map hφ)).FiniteType

/-- A continuous taut homomorphism that is topologically of finite type is of finite type on
reductions, provided its source has a weak ideal of definition. -/
@[stacks 0GC5]
public lemma isFiniteTypeOnReductions_of_isTaut_of_isTopologicallyOfFiniteType
    {A B : Type*} [CommRing A] [TopologicalSpace A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    (φ : A →+* B) (hφ : Continuous φ) (hA : TopologicalRing.IsWeaklyPreAdmissible A)
    (htaut : RingHom.IsTaut φ) (hft : TopologicalRing.IsTopologicallyOfFiniteType φ) :
    IsFiniteTypeOnReductions φ hφ := by
  classical
  rcases hA with ⟨I, hIopen, hInil⟩
  have hclosure_le : Ideal.closure (I.map φ) ≤ topologicalNilradical B :=
    TopologicalRing.closure_map_le_topologicalNilradical φ hφ I
      fun x hx ↦ IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr (hInil x hx)
  have hNBopen : IsOpen (topologicalNilradical B : Set B) := by
    apply (topologicalNilradical B).toAddSubgroup.isOpen_of_mem_nhds
    exact Filter.mem_of_superset
      ((htaut.1 I hIopen).mem_nhds (Ideal.zero_mem (Ideal.closure (I.map φ)))) hclosure_le
  rcases hft with ⟨n, f, hcomm, hdense⟩
  let NA := topologicalNilradical A
  let NB := topologicalNilradical B
  have hmap : NA ≤ NB.comap φ := fun x hx ↦
    IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr
      ((IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp hx).map hφ)
  let qA : A →+* A ⧸ NA := Ideal.Quotient.mk NA
  let qB : B →+* B ⧸ NB := Ideal.Quotient.mk NB
  let qφ : A ⧸ NA →+* B ⧸ NB := Ideal.quotientMap NB φ hmap
  have hq : qφ.comp qA = qB.comp φ := Ideal.quotientMap_comp_mk hmap
  show qφ.FiniteType
  let _ : Algebra (A ⧸ NA) (B ⧸ NB) := qφ.toAlgebra
  let evalMap : MvPolynomial (Fin n) (A ⧸ NA) →ₐ[A ⧸ NA] (B ⧸ NB) :=
    MvPolynomial.aeval (fun i => qB (f (MvPolynomial.X i)))
  have hEval : evalMap.toRingHom.comp (MvPolynomial.map qA) = qB.comp f := by
    apply MvPolynomial.ringHom_ext'
    · ext a
      simp only [RingHom.comp_apply, MvPolynomial.map_C]
      show MvPolynomial.aeval (fun i => qB (f (MvPolynomial.X i)))
        (MvPolynomial.C (qA a)) = qB (f (MvPolynomial.C a))
      rw [MvPolynomial.aeval_C]
      show qφ (qA a) = qB (f (MvPolynomial.C a))
      rw [show qφ (qA a) = qB (φ a) from congrArg (fun g : A →+* B ⧸ NB => g a) hq,
        show f (MvPolynomial.C a) = φ a from congrArg (fun g : A →+* B => g a) hcomm]
    · intro i
      simp [RingHom.comp_apply, evalMap, qB]
  have hsurj : Function.Surjective evalMap := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := NB) y
    obtain ⟨p, hp⟩ := hdense.exists_mem_open
      (hNBopen.preimage (continuous_const.sub continuous_id)) ⟨b, by change b - b ∈ NB; simp⟩
    have hEq : qB (f p) = qB b := by
      have hsub : qB b - qB (f p) = 0 := by
        simpa [map_sub] using (Ideal.Quotient.eq_zero_iff_mem.mpr hp : qB (b - f p) = 0)
      exact (sub_eq_zero.mp hsub).symm
    refine ⟨MvPolynomial.map qA p, ?_⟩
    simpa [RingHom.comp_apply, hEq] using
      congrArg (fun g : MvPolynomial (Fin n) A →+* B ⧸ NB => g p) hEval
  exact (Algebra.FiniteType.iff_quotient_mvPolynomial''
    (R := A ⧸ NA) (S := B ⧸ NB)).2 ⟨n, evalMap, hsurj⟩

section

open Filter Pointwise
open scoped Topology

/-- The set of products of `n` elements of `G`, i.e. the degree-`n` part of the multiplicative
word monoid on `G`.  Its span is the `n`-th power of the ideal generated by `G`. -/
private def wordSet {B : Type*} [CommRing B] (G : Finset B) : ℕ → Set B
  | 0 => {1}
  | n + 1 => wordSet G n * (G : Set B)

private theorem wordSet_range
    {R B : Type*} [CommRing R] [CommRing B]
    (e : R →+* B) (G : Finset B) (hG_range : ∀ x ∈ G, ∃ y, e y = x) :
    ∀ n a, a ∈ wordSet G n → ∃ y, e y = a := by
  intro n
  induction n with
  | zero =>
      intro a ha
      obtain rfl : a = 1 := ha
      exact ⟨1, map_one e⟩
  | succ n ih =>
      intro a ha
      simp only [wordSet, Set.mem_mul] at ha
      obtain ⟨u, hu, v, hv, rfl⟩ := ha
      obtain ⟨ru, rfl⟩ := ih u hu
      obtain ⟨rv, rfl⟩ := hG_range v hv
      exact ⟨ru * rv, by simp [map_mul]⟩

private theorem span_wordSet_pow {B : Type*} [CommRing B] (G : Finset B) (n : ℕ) :
    (Ideal.span (G : Set B) : Ideal B) ^ n = Ideal.span (wordSet G n) := by
  induction n with
  | zero => simp [wordSet]
  | succ n ih =>
    rw [pow_succ, ih, Ideal.span_mul_span]
    simp [wordSet]

private theorem approximation_step
    {R B : Type*} [CommRing R] [CommRing B]
    (e : R →+* B) (I : Ideal B) (G : Finset B)
    (hG : Ideal.span (G : Set B) = I)
    (hG_range : ∀ x ∈ G, ∃ y, e y = x)
    (hquot : ∀ b : B, ∃ y, b - e y ∈ I)
    (n : ℕ) {x : B} (hx : x ∈ I ^ n) :
    ∃ y, x - e y ∈ I ^ (n + 1) := by
  classical
  rw [← hG, span_wordSet_pow G n] at hx
  obtain ⟨c, t, ht, _, hsum⟩ :=
    (Submodule.mem_span_iff_exists_finset_subset (s := wordSet G n) (x := x)).mp hx
  let coeffLift : B → R := fun b => Classical.choose (hquot b)
  let coeffResidue : B → B := fun b => b - e (coeffLift b)
  have hcoeff (b : B) : b = e (coeffLift b) + coeffResidue b := by simp [coeffResidue]
  have hresidue (b : B) : coeffResidue b ∈ I :=
    Classical.choose_spec (hquot b)
  have hword_ideal : ∀ a ∈ t, a ∈ I ^ n := by
    intro a ha
    rw [← hG, span_wordSet_pow G n]
    exact Ideal.subset_span (ht ha)
  let preimage : B → R := fun a => if ha : a ∈ wordSet G n then
    Classical.choose (wordSet_range e G hG_range n a ha) else 0
  have hpreimage : ∀ a (ha : a ∈ t), e (preimage a) = a := by
    intro a ha
    simpa only [preimage, dite_eq_left (ht ha)] using
      Classical.choose_spec (wordSet_range e G hG_range n a (ht ha))
  let s : R := ∑ a ∈ t, coeffLift (c a) * preimage a
  have hfirst : (∑ a ∈ t, e (coeffLift (c a)) * a) = e s := by
    dsimp [s]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [map_mul, hpreimage a ha]
  have hsplit : x = e s + ∑ a ∈ t, coeffResidue (c a) * a := by
    calc
      x = ∑ a ∈ t, c a * a := by simpa only [smul_eq_mul] using hsum.symm
      _ = ∑ a ∈ t,
          (e (coeffLift (c a)) * a + coeffResidue (c a) * a) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [← add_mul, ← hcoeff (c a)]
      _ = (∑ a ∈ t, e (coeffLift (c a)) * a) +
          ∑ a ∈ t, coeffResidue (c a) * a := by rw [Finset.sum_add_distrib]
      _ = _ := by rw [hfirst]
  have htail : (∑ a ∈ t, coeffResidue (c a) * a) ∈ I ^ (n + 1) := sum_mem fun a ha ↦ by
    simpa [pow_succ', mul_comm] using Ideal.mul_mem_mul (hresidue (c a)) (hword_ideal a ha)
  exact ⟨s, by simpa [hsplit] using htail⟩

private theorem approximation_all_powers
    {R B : Type*} [CommRing R] [CommRing B]
    (e : R →+* B) (I : Ideal B) (G : Finset B)
    (hG : Ideal.span (G : Set B) = I)
    (hG_range : ∀ x ∈ G, ∃ y, e y = x)
    (hquot : ∀ b : B, ∃ y, b - e y ∈ I) :
    ∀ n b, ∃ y, b - e y ∈ I ^ n := by
  intro n
  induction n with
  | zero => exact fun b ↦ ⟨0, by simp⟩
  | succ n ih =>
      intro b
      obtain ⟨y, hy⟩ := ih b
      obtain ⟨z, hz⟩ := approximation_step e I G hG hG_range hquot n hy
      refine ⟨y + z, ?_⟩
      rw [show b - e (y + z) = (b - e y) - e z by simp [map_add]; ring]
      exact hz

private theorem topologicalNilradical_isIdealOfDefinition
    {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [IsNoetherianRing B]
    (hB : TopologicalRing.IsWeaklyAdmissible B) :
    TopologicalRing.IsIdealOfDefinition (topologicalNilradical B) := by
  rcases hB.1 with ⟨J, hJ⟩
  constructor
  · apply (topologicalNilradical B).toAddSubgroup.isOpen_of_mem_nhds
    apply Filter.mem_of_superset (hJ.1.mem_nhds (zero_mem J))
    intro x hx
    exact IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr (hJ.2 x hx)
  · intro U hU
    obtain ⟨K, hKopen, hKU⟩ := IsLinearTopology.hasBasis_open_ideal.mem_iff.mp hU
    have hfg : (topologicalNilradical B).FG :=
      Ideal.fg_of_isNoetherianRing (topologicalNilradical B)
    have hrad : topologicalNilradical B ≤ K.radical := fun x hx ↦
      IsTopologicallyNilpotent.exists_pow_mem_of_mem_nhds
        (IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp hx)
        (hKopen.mem_nhds (zero_mem K))
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hfg
    exact ⟨n, (SetLike.coe_subset_coe.mpr hn).trans hKU⟩

private theorem denseRange_of_topologicalNilradical_approximation
    {R B : Type*} [CommRing R] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B]
    (e : R →+* B) (hIdef : TopologicalRing.IsIdealOfDefinition (topologicalNilradical B))
    (G : Finset B) (hG : Ideal.span (G : Set B) = topologicalNilradical B)
    (hG_range : ∀ x ∈ G, ∃ y, e y = x)
    (hquot : ∀ b : B, ∃ y, b - e y ∈ topologicalNilradical B) :
    DenseRange e := by
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_iff_forall.mpr
  intro b
  rw [mem_closure_iff_nhds]
  intro V hV
  have hV0 : (fun y : B => b + y) ⁻¹' V ∈ 𝓝 (0 : B) :=
    (continuous_const_add b).continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨K, hKopen, hKV⟩ := IsLinearTopology.hasBasis_open_ideal.mem_iff.mp hV0
  obtain ⟨n, hn⟩ := hIdef.2 K (hKopen.mem_nhds (zero_mem K))
  obtain ⟨y, hy⟩ := approximation_all_powers e (topologicalNilradical B) G hG
    hG_range hquot n b
  have hdiff : e y - b ∈ K := by simpa using K.neg_mem (hn hy)
  refine ⟨e y, ?_, ⟨y, rfl⟩⟩
  simpa using hKV hdiff

/-- A continuous homomorphism into a Noetherian weakly admissible topological ring that is of
finite type on reductions is topologically of finite type. -/
@[stacks 0GC6]
public theorem isTopologicallyOfFiniteType_of_isFiniteTypeOnReductions
    {A B : Type*} [CommRing A] [TopologicalSpace A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [IsLinearTopology B B] [IsNoetherianRing B]
    (φ : A →+* B) (hφ : Continuous φ) (hB : TopologicalRing.IsWeaklyAdmissible B)
    (hred : IsFiniteTypeOnReductions φ hφ) :
    TopologicalRing.IsTopologicallyOfFiniteType φ := by
  classical
  let NA := topologicalNilradical A
  let NB := topologicalNilradical B
  have hmap : NA ≤ NB.comap φ := fun x hx ↦
    IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr
      ((IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp hx).map hφ)
  let qA : A →+* A ⧸ NA := Ideal.Quotient.mk NA
  let qB : B →+* B ⧸ NB := Ideal.Quotient.mk NB
  let qφ : A ⧸ NA →+* B ⧸ NB := Ideal.quotientMap NB φ hmap
  have hq : qφ.comp qA = qB.comp φ := Ideal.quotientMap_comp_mk hmap
  change qφ.FiniteType at hred
  let _ : Algebra (A ⧸ NA) (B ⧸ NB) := qφ.toAlgebra
  obtain ⟨n, f, hf⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial''
      (R := A ⧸ NA) (S := B ⧸ NB)).mp hred
  obtain ⟨G, hG⟩ := (Ideal.fg_of_isNoetherianRing NB : NB.FG)
  let _ : Fintype {x // x ∈ (G : Set B)} := Fintype.ofFinite _
  let σ := Fin n ⊕ {x // x ∈ (G : Set B)}
  let g₀ : Fin n → B := fun i =>
    Classical.choose (Ideal.Quotient.mk_surjective (f (MvPolynomial.X i)))
  have hg₀ (i : Fin n) : qB (g₀ i) = f (MvPolynomial.X i) :=
    Classical.choose_spec (Ideal.Quotient.mk_surjective (f (MvPolynomial.X i)))
  let g : σ → B := Sum.elim g₀ (fun x => x.1)
  let e : MvPolynomial σ A →+* B := MvPolynomial.eval₂Hom φ g
  have hG_range : ∀ x ∈ G, ∃ p, e p = x := fun x hx ↦
    ⟨MvPolynomial.X (Sum.inr ⟨x, hx⟩), by simp [e, g]⟩
  have hEval : (qB.comp e).comp (MvPolynomial.rename Sum.inl).toRingHom =
      f.toRingHom.comp (MvPolynomial.map qA) := by
    apply MvPolynomial.ringHom_ext'
    · ext a
      simp only [RingHom.comp_apply]
      show qB (e (MvPolynomial.rename Sum.inl (MvPolynomial.C a))) =
        f (MvPolynomial.map qA (MvPolynomial.C a))
      rw [MvPolynomial.rename_C, MvPolynomial.map_C]
      have hevalC : e (MvPolynomial.C a) = φ a := by simp [e]
      rw [hevalC, MvPolynomial.C_eq_algebraMap, f.commutes]
      exact (RingHom.congr_fun hq a).symm
    · intro i
      simp [RingHom.comp_apply, e, g, g₀, qB, hg₀]
  have hquot : ∀ b : B, ∃ p, b - e p ∈ NB := by
    intro b
    obtain ⟨p, hp⟩ := hf (qB b)
    obtain ⟨pA, hpA⟩ := MvPolynomial.map_surjective qA Ideal.Quotient.mk_surjective p
    let z : MvPolynomial σ A := MvPolynomial.rename (Sum.inl : Fin n → σ) pA
    have hzEval : qB (e z) = f (MvPolynomial.map qA pA) := by
      simpa [z, RingHom.comp_apply] using
        congrArg (fun H : MvPolynomial (Fin n) A →+* B ⧸ NB => H pA) hEval
    have hz : qB (e z) = qB b := by rw [hzEval, hpA, hp]
    exact ⟨z, Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_sub, hz, sub_self])⟩
  have hIdef : TopologicalRing.IsIdealOfDefinition NB :=
    topologicalNilradical_isIdealOfDefinition hB
  have hdense : DenseRange e := denseRange_of_topologicalNilradical_approximation
    e hIdef G hG hG_range hquot
  let eFin : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let e' : MvPolynomial (Fin (Fintype.card σ)) A →+* B :=
    e.comp (MvPolynomial.rename eFin.symm).toRingHom
  have hrename : Function.Surjective (MvPolynomial.rename (R := A) eFin.symm) :=
    MvPolynomial.rename_surjective _ eFin.symm.surjective
  have hrange : Set.range e = Set.range e' := by
    ext b
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨q, hq⟩ := hrename p
      exact ⟨q, by simp [e', hq]⟩
    · rintro ⟨q, rfl⟩
      exact ⟨MvPolynomial.rename eFin.symm q, rfl⟩
  have hdense' : DenseRange e' := by simpa [DenseRange, hrange] using hdense
  refine ⟨Fintype.card σ, e', ?_, hdense'⟩
  ext a
  simp [e', e]

end

/-- An adic homomorphism into a Noetherian weakly admissible ring is of finite type on
reductions if and only if it is topologically of finite type. -/
@[stacks 0GG6]
public theorem isFiniteTypeOnReductions_iff_isTopologicallyOfFiniteType
    {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [IsLinearTopology B B] [IsNoetherianRing B]
    (φ : A →+* B) (hφ : Continuous φ)
    (hA : TopologicalRing.IsWeaklyPreAdmissible A)
    (hB : TopologicalRing.IsWeaklyAdmissible B)
    (hadic : RingHom.IsAdic φ) :
    IsFiniteTypeOnReductions φ hφ ↔
      TopologicalRing.IsTopologicallyOfFiniteType φ :=
  ⟨isTopologicallyOfFiniteType_of_isFiniteTypeOnReductions φ hφ hB,
    isFiniteTypeOnReductions_of_isTaut_of_isTopologicallyOfFiniteType
      φ hφ hA (RingHom.isTaut_of_isAdic φ hφ hadic)⟩

end Rig

end
