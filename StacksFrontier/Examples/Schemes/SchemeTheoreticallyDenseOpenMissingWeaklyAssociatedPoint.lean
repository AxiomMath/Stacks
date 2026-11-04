module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Order.Filter.EventuallyConst
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Reduced
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.SchemeTheoreticClosure

/-!
# A scheme-theoretically dense open missing a weakly associated point

There is a reduced scheme with a scheme-theoretically dense open subscheme that omits a weakly
associated point of the scheme.

The scheme is the spectrum of the ring of eventually constant sequences `ℕ → 𝔽₂`. The ideal of
sequences that are eventually zero is a minimal prime, hence its point is a generic point of an
irreducible component and so, the ring being reduced, a weakly associated point of the scheme.
The open subscheme is the union of the principal opens attached to the sequences supported at a
single index: it contains the point of every evaluation at an index, hence is topologically
dense and therefore scheme-theoretically dense, yet it misses the point of the ideal of
eventually zero sequences.

## Main results

* `Stacks.Examples.exists_isSchemeTheoreticallyDense_open_notMem_weaklyAssociatedPoint`: such a
  scheme, open subscheme and point.

## Implementation notes

Weak association to the structure sheaf is membership in
`Stacks.Divisors.schemeWeaklyAssociatedPoints`. The index set is `ULift ℕ`, so that the ring,
and hence the scheme, can be produced in any universe.

## References

* [Stacks Project, Tag 084K](https://stacks.math.columbia.edu/tag/084K)
-/

@[expose] public section

open AlgebraicGeometry

namespace Stacks.Examples

universe u

/-- The index set of the sequences, in an arbitrary universe. -/
private abbrev SeqIndex := ULift.{u} ℕ

/-- The subring of sequences `ℕ → 𝔽₂` that are constant from some index on. -/
private def eventuallyConstantSeq : Subring (SeqIndex.{u} → ZMod 2) where
  carrier := {f | Filter.EventuallyConst f Filter.atTop}
  zero_mem' := Filter.EventuallyConst.const 0
  one_mem' := Filter.EventuallyConst.const 1
  add_mem' := fun ha hb => ha.add hb
  neg_mem' := fun ha => ha.neg
  mul_mem' := fun ha hb => ha.mul hb

/-- The ring of eventually constant sequences with values in `𝔽₂`. -/
private abbrev EventuallyConstantSeqRing := ↥eventuallyConstantSeq.{u}

/-- An index beyond `i + 1` is different from `i`. -/
private lemma ne_of_succ_le {i j : SeqIndex.{u}} (h : ULift.up (i.down + 1) ≤ j) : j ≠ i := by
  intro hji
  have hj' : i.down + 1 ≤ j.down := by exact_mod_cast h
  rw [hji] at hj'
  omega

/-- The sequence equal to `1` at the index `i` and to `0` elsewhere. -/
private def spike (i : SeqIndex.{u}) : EventuallyConstantSeqRing.{u} :=
  ⟨fun j => if j = i then 1 else 0, by
    change Filter.EventuallyConst (fun j => if j = i then 1 else 0) Filter.atTop
    rw [Filter.eventuallyConst_atTop]
    refine ⟨ULift.up (i.down + 1), fun j hj => ?_⟩
    simp [ne_of_succ_le hj, ne_of_succ_le (le_refl (ULift.up (i.down + 1)))]⟩

/-- The ideal of sequences that are eventually zero. -/
private def infinityIdeal : Ideal EventuallyConstantSeqRing.{u} where
  carrier := {f | ∀ᶠ i : SeqIndex.{u} in Filter.atTop, f.1 i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    filter_upwards [ha, hb] with i hi hj
    simp [hi, hj]
  smul_mem' := by
    intro a b hb
    filter_upwards [hb] with i hi
    simp [hi]

/-- Evaluation of a sequence at a fixed index, as a ring homomorphism. -/
private def evalRingHom (i : SeqIndex.{u}) : EventuallyConstantSeqRing.{u} →+* ZMod 2 where
  toFun f := f.1 i
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Every element of `𝔽₂` is `0` or `1`. -/
private lemma zmodTwo_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The ideal of eventually zero sequences is prime: an eventually constant sequence is
eventually zero exactly when its eventual value is zero. -/
private lemma infinityIdeal_isPrime : infinityIdeal.{u}.IsPrime := by
  refine Ideal.isPrime_iff.2 ⟨fun htop => ?_, fun {a b} hab => ?_⟩
  · have hone : (1 : EventuallyConstantSeqRing.{u}) ∈ infinityIdeal := htop ▸ Submodule.mem_top
    obtain ⟨i, hi⟩ :=
      (show ∀ᶠ i : SeqIndex.{u} in Filter.atTop, (1 : ZMod 2) = 0 from hone).exists
    norm_num at hi
  · obtain ⟨c, hac⟩ := Filter.eventuallyConst_iff_exists_eventuallyEq.mp
      (show Filter.EventuallyConst a.1 Filter.atTop from a.2)
    obtain ⟨d, hbd⟩ := Filter.eventuallyConst_iff_exists_eventuallyEq.mp
      (show Filter.EventuallyConst b.1 Filter.atTop from b.2)
    have hprod : ∀ᶠ i : SeqIndex.{u} in Filter.atTop, a.1 i * b.1 i = 0 := hab
    have hcd : c * d = 0 := by
      obtain ⟨i, ⟨haci, hbdi⟩, hprod⟩ := (hac.and hbd).and hprod |>.exists
      simpa only [haci, hbdi] using hprod
    rcases mul_eq_zero.mp hcd with hc | hd
    · left
      filter_upwards [hac] with i hi
      simpa [hc] using hi
    · right
      filter_upwards [hbd] with i hi
      simpa [hd] using hi

/-- Each spike is eventually zero. -/
private lemma spike_mem_infinityIdeal (i : SeqIndex.{u}) :
    spike i ∈ infinityIdeal.{u} := by
  change ∀ᶠ j : SeqIndex.{u} in Filter.atTop, (spike i).1 j = 0
  rw [Filter.eventually_atTop]
  exact ⟨ULift.up (i.down + 1), fun j hj => by simp [spike, ne_of_succ_le hj]⟩

/-- The complement of an eventually zero sequence is not eventually zero. -/
private lemma one_sub_notMem_infinityIdeal {f : EventuallyConstantSeqRing.{u}}
    (hf : f ∈ infinityIdeal.{u}) : 1 - f ∉ infinityIdeal.{u} := by
  intro h
  have hone : ∀ᶠ j : SeqIndex.{u} in Filter.atTop, (1 - f).1 j = 1 := by
    filter_upwards [hf] with j hj
    simp [hj]
  obtain ⟨j, hj0, hj1⟩ := h.and hone |>.exists
  exact zero_ne_one (hj0.symm.trans hj1)

/-- The ideal of eventually zero sequences is a minimal prime: the ring has no nontrivial
idempotent-free primes below it, since `f (1 - f) = 0` for every `f`. -/
private lemma infinityIdeal_minimal :
    infinityIdeal.{u} ∈ minimalPrimes EventuallyConstantSeqRing.{u} := by
  rw [minimalPrimes_eq_minimals]
  change Minimal Ideal.IsPrime infinityIdeal
  refine ⟨infinityIdeal_isPrime, ?_⟩
  intro Q hQ hQI f hf
  have hmul : f * (1 - f) = 0 := by
    ext i
    rcases zmodTwo_eq_zero_or_one (f.1 i) with h | h <;> simp [h]
  have hprod : f * (1 - f) ∈ Q := hmul ▸ Q.zero_mem
  exact (hQ.mem_or_mem hprod).resolve_right fun h => one_sub_notMem_infinityIdeal hf (hQI h)

/-- The point of the spectrum given by the ideal of eventually zero sequences. -/
private def infinityPoint : PrimeSpectrum EventuallyConstantSeqRing.{u} :=
  ⟨infinityIdeal, infinityIdeal_isPrime⟩

/-- The point at infinity is a generic point of an irreducible component. -/
private lemma infinityPoint_mem_genericPoints :
    infinityPoint.{u} ∈ genericPoints (PrimeSpectrum EventuallyConstantSeqRing.{u}) := by
  change closure ({infinityPoint} : Set (PrimeSpectrum EventuallyConstantSeqRing.{u})) ∈
    irreducibleComponents (PrimeSpectrum EventuallyConstantSeqRing.{u})
  exact (PrimeSpectrum.vanishingIdeal_mem_minimalPrimes).mp
    (by simpa [infinityPoint] using infinityIdeal_minimal)

/-- The point of the spectrum given by the kernel of evaluation at an index. -/
private def evalPoint (i : SeqIndex.{u}) : PrimeSpectrum EventuallyConstantSeqRing.{u} :=
  ⟨RingHom.ker (evalRingHom i), RingHom.ker_isPrime _⟩

/-- The union of the principal opens attached to the spikes. -/
private def denseOpen : (Spec (.of EventuallyConstantSeqRing.{u})).Opens :=
  ⟨⋃ i : SeqIndex.{u},
      (PrimeSpectrum.basicOpen (spike i) :
        Set (PrimeSpectrum EventuallyConstantSeqRing.{u})),
    isOpen_iUnion fun _ => PrimeSpectrum.isOpen_basicOpen⟩

/-- A point lies in `denseOpen` exactly when some spike is outside its prime ideal. -/
private lemma mem_denseOpen_iff (p : Spec (.of EventuallyConstantSeqRing.{u})) :
    p ∈ (denseOpen.{u} : Set (Spec (.of EventuallyConstantSeqRing.{u}))) ↔
      ∃ i, spike i ∉ p.asIdeal := by
  exact Set.mem_iUnion

/-- **Stacks 084K.** A reduced scheme can have a scheme-theoretically dense open subscheme that
omits a weakly associated point. -/
@[stacks 084K]
theorem exists_isSchemeTheoreticallyDense_open_notMem_weaklyAssociatedPoint :
    ∃ (X : Scheme.{u}) (U : X.Opens) (x : X),
      IsReduced X ∧ Scheme.Opens.IsSchemeTheoreticallyDense U ∧
        x ∈ Stacks.Divisors.schemeWeaklyAssociatedPoints X ∧ x ∉ (U : Set X) := by
  let X : Scheme.{u} := Spec (.of EventuallyConstantSeqRing.{u})
  have : _root_.IsReduced EventuallyConstantSeqRing.{u} :=
    isReduced_of_injective eventuallyConstantSeq.subtype Subtype.val_injective
  have : IsReduced X :=
    (AlgebraicGeometry.affine_isReduced_iff (.of EventuallyConstantSeqRing.{u})).2 inferInstance
  let U : X.Opens := denseOpen
  have hU_dense : Dense (U : Set X) := by
    rw [dense_iff_inter_open]
    intro V hV ⟨p, hp⟩
    obtain ⟨W, hW, hpW, hWV⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp hV
    rcases hW with ⟨f, rfl⟩
    have hpnot : f ∉ p.asIdeal := PrimeSpectrum.mem_basicOpen f p |>.mp hpW
    obtain ⟨i, hi⟩ : ∃ i : SeqIndex.{u}, f.1 i ≠ 0 := by
      by_contra! hn
      obtain rfl : f = 0 := Subtype.ext (funext hn)
      exact hpnot p.asIdeal.zero_mem
    let y := evalPoint i
    have hyW : y ∈ PrimeSpectrum.basicOpen f := (PrimeSpectrum.mem_basicOpen f y).2 hi
    have hyU : y ∈ (U : Set X) := by
      refine (mem_denseOpen_iff y).2 ⟨i, ?_⟩
      change spike i ∉ RingHom.ker (evalRingHom i)
      simp [RingHom.mem_ker, evalRingHom, spike]
    exact ⟨y, hWV hyW, hyU⟩
  have hU_st : Scheme.Opens.IsSchemeTheoreticallyDense U :=
    ((AlgebraicGeometry.dense_open_tfae U).out 1 3).mp hU_dense
  have hxnot : infinityPoint ∉ (U : Set X) := by
    intro hx
    obtain ⟨i, hi⟩ := (mem_denseOpen_iff _).1 hx
    exact hi (spike_mem_infinityIdeal i)
  have hxweak : infinityPoint ∈ Stacks.Divisors.schemeWeaklyAssociatedPoints X := by
    rw [AlgebraicGeometry.weaklyAssociatedPointsOfScheme_eq_genericPoints]
    exact infinityPoint_mem_genericPoints
  exact ⟨X, U, infinityPoint, inferInstance, hU_st, hxweak, hxnot⟩

end Stacks.Examples
