module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Data.Set.Card
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.RingTheory.Algebra.DirectLimit.Descent
import StacksFrontier.RingTheory.Flat.DirectLimit
import StacksFrontier.RingTheory.Spectrum.Prime.Surjective

/-!
# The number of minimal primes of a directed colimit

Let `Rᵢ` be a directed system of commutative rings whose transition maps are faithfully flat.
The number of minimal primes of its colimit is the supremum of the numbers of minimal primes of
the rings in the system. Two facts drive this: a faithfully flat transition map pulls minimal
primes back to minimal primes, so no stage has more minimal primes than the colimit; and every
finite family of minimal primes of the colimit is already separated at some stage, because the
finitely many elements witnessing the separation descend.

## Main results

* `comap_mem_minimalPrimes_of_flat`: a flat ring map contracts minimal primes to minimal primes.
* `encard_minimalPrimes_directLimit` computes the extended-natural cardinality of the set of
  minimal primes of the direct limit.

## Implementation notes

The set `{0, 1, 2, …, ∞}` in the source is represented by `ℕ∞`, and its cardinality operation by
`Set.encard`. The colimit is the explicit ring `Ring.DirectLimit`; this retains both its
canonical construction and all of the transition maps.

The statement is about a directed system of commutative rings rather than about schemes, so it
lives in the root namespace alongside the rest of the `minimalPrimes` API.

## References

* [Stacks Project, Tag 0CB3](https://stacks.math.columbia.edu/tag/0CB3)
-/

public section

universe u v

private theorem directLimit_of_flat
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (R : ι → Type v) [(i : ι) → CommRing (R i)]
    (f : (i j : ι) → i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h => (f i j h : R i → R j))]
    (hflat : ∀ i j (h : i ≤ j), (f i j h).Flat) (i : ι) :
    (Ring.DirectLimit.of R (fun i j h => (f i j h : R i → R j)) i).Flat := by
  classical
  let g := Ring.DirectLimit.of R (fun i j h => (f i j h : R i → R j)) i
  let : Algebra (R i) (Ring.DirectLimit R (fun i j h => (f i j h : R i → R j))) :=
    g.toAlgebra
  show Module.Flat (R i) (Ring.DirectLimit R (fun i j h => (f i j h : R i → R j)))
  let J := {j : ι // i ≤ j}
  have : IsDirected J (· ≤ ·) := ⟨fun j k => by
    obtain ⟨m, hjm, hkm⟩ := directed_of (· ≤ ·) j.1 k.1
    exact ⟨⟨m, j.2.trans hjm⟩, hjm, hkm⟩⟩
  have : Nonempty J := ⟨⟨i, le_rfl⟩⟩
  let : (j : J) → Module (R i) (R j.1) := fun j => Stacks.DirectLimit.FinitePresentationDescent.modJ
    R f i j
  obtain ⟨e, -⟩ := Stacks.DirectLimit.FinitePresentationDescent.exists_linearEquiv_modColim R f i
  have : Module.Flat (R i) (Stacks.DirectLimit.FinitePresentationDescent.ModColim R f i) := by
    apply directLimit_flat
    intro j
    let := (f i j.1 j.2).toAlgebra
    exact hflat i j.1 j.2
  exact Module.Flat.of_linearEquiv e

/-- A flat ring map pulls minimal primes back to minimal primes: flatness gives going down, so
a prime strictly below the contraction of a minimal prime would lift to a prime strictly above
it. -/
@[ega "IV 4.7.2" "more general"]
theorem comap_mem_minimalPrimes_of_flat
    {A B : Type*} [CommRing A] [CommRing B] (g : A →+* B) (hg : g.Flat)
    {q : Ideal B} (hq : q ∈ minimalPrimes B) : q.comap g ∈ minimalPrimes A := by
  let : Algebra A B := g.toAlgebra
  have : Module.Flat A B := hg
  have hgd : Algebra.HasGoingDown A B := Algebra.HasGoingDown.of_flat
  have : q.IsPrime := hq.isPrime
  refine ⟨⟨hq.isPrime.comap g, bot_le⟩, ?_⟩
  rintro p ⟨hp, -⟩ hpq
  by_contra hne
  have hlt : p < Ideal.under A q := lt_of_le_of_ne hpq fun e => hne e.ge
  obtain ⟨Q, hQle, hQprime, hQlies⟩ := hgd.exists_ideal_le_liesOver_of_lt q hlt
  exact hne ((Ideal.comap_mono (hq.2 ⟨hQprime, bot_le⟩ hQle)).trans_eq hQlies.over.symm)

private theorem directLimit_descend_finset
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (R : ι → Type v) [(i : ι) → CommRing (R i)]
    (f : (i j : ι) → i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h => (f i j h : R i → R j))]
    (s : Finset (Ring.DirectLimit R (fun i j h => (f i j h : R i → R j)))) :
    ∃ (i : ι) (g : Ring.DirectLimit R (fun i j h => (f i j h : R i → R j)) → R i),
      ∀ z ∈ s, Ring.DirectLimit.of R (fun i j h => (f i j h : R i → R j)) i (g z) = z := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨Classical.arbitrary ι, fun _ => 0, by simp⟩
  | @insert z s hzs ih =>
    obtain ⟨i, g, hg⟩ := ih
    obtain ⟨j, w, hw⟩ := Ring.DirectLimit.exists_of
      (G := R) (f := fun i j h => f i j h) z
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    refine ⟨k, fun y => if y = z then f j k hjk w else f i k hik (g y), fun y hy => ?_⟩
    by_cases hyz : y = z
    · subst y
      simpa using hw
    · simpa [hyz] using hg y ((Finset.mem_insert.mp hy).resolve_left hyz)

/-- Two distinct minimal primes are separated by an element of the first outside the second. -/
private theorem exists_mem_notMem_of_mem_minimalPrimes {A : Type*} [CommRing A] {q q' : Ideal A}
    (hq : q ∈ minimalPrimes A) (hq' : q' ∈ minimalPrimes A) (hne : q ≠ q') :
    ∃ a ∈ q, a ∉ q' :=
  Set.not_subset_iff_exists_mem_notMem.mp fun hle =>
    hne (le_antisymm hle (hq'.2 ⟨hq.isPrime, bot_le⟩ hle))

private theorem finite_minimalPrimes_le_stage
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (R : ι → Type v) [(i : ι) → CommRing (R i)]
    (f : (i j : ι) → i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h => (f i j h : R i → R j))]
    (hflat : ∀ i j (h : i ≤ j), (f i j h).Flat)
    (s : Finset (Ideal (Ring.DirectLimit R (fun i j h => (f i j h : R i → R j)))))
    (hs : ∀ q ∈ s, q ∈ minimalPrimes
      (Ring.DirectLimit R (fun i j h => (f i j h : R i → R j)))) :
    ∃ i, s.card ≤ Set.encard (minimalPrimes (R i)) := by
  classical
  let T := Ring.DirectLimit R (fun i j h => (f i j h : R i → R j))
  let witness : {q // q ∈ s} → {q // q ∈ s} → T := fun q q' =>
    if h : q.1 = q'.1 then 0 else Classical.choose (exists_mem_notMem_of_mem_minimalPrimes
      (hs q.1 q.2) (hs q'.1 q'.2) h)
  let elems : Finset T := (s.attach ×ˢ s.attach).image fun p => witness p.1 p.2
  obtain ⟨i, lift, hlift⟩ := directLimit_descend_finset R f elems
  let ofi := Ring.DirectLimit.of R (fun i j h => (f i j h : R i → R j)) i
  let c : Ideal T → Ideal (R i) := fun q => q.comap ofi
  have hc_maps : Set.MapsTo c (↑s : Set (Ideal T)) (minimalPrimes (R i)) := fun q hq =>
    comap_mem_minimalPrimes_of_flat ofi (directLimit_of_flat R f hflat i) (hs q hq)
  have hc_inj : Set.InjOn c (↑s : Set (Ideal T)) := by
    intro q hq q' hq' heq
    by_contra hne
    let Q : {q // q ∈ s} := ⟨q, hq⟩
    let Q' : {q // q ∈ s} := ⟨q', hq'⟩
    have hQQ : Q' ≠ Q := fun e => hne (congrArg Subtype.val e).symm
    have hw := Classical.choose_spec (exists_mem_notMem_of_mem_minimalPrimes
      (hs q' hq') (hs q hq) (Ne.symm hne))
    have hmem : witness Q' Q ∈ elems :=
      Finset.mem_image.mpr ⟨(Q', Q), Finset.mem_product.mpr ⟨by simp [Q'], by simp [Q]⟩, rfl⟩
    have hl := hlift (witness Q' Q) hmem
    have ha : lift (witness Q' Q) ∈ c q' := by
      show ofi (lift (witness Q' Q)) ∈ q'
      rw [hl]
      simpa [witness, hQQ] using hw.1
    have ha' : lift (witness Q' Q) ∈ c q := by rwa [← heq] at ha
    change ofi (lift (witness Q' Q)) ∈ q at ha'
    rw [hl] at ha'
    exact hw.2 (by simpa [witness, hQQ] using ha')
  exact ⟨i, by simpa using Set.encard_le_encard_of_injOn hc_maps hc_inj⟩

/-- **Stacks Project, Tag 0CB3.** For a directed system of rings with faithfully
flat transition maps, the number of minimal primes of the direct limit is the
supremum of the numbers of minimal primes at the individual stages. -/
@[stacks 0CB3]
theorem encard_minimalPrimes_directLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (R : ι → Type v) [(i : ι) → CommRing (R i)]
    (f : (i j : ι) → i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h => (f i j h : R i → R j))]
    (hff : ∀ i j (h : i ≤ j), (f i j h).FaithfullyFlat) :
    Set.encard (minimalPrimes (Ring.DirectLimit R
      (fun i j h => (f i j h : R i → R j)))) =
      ⨆ i, Set.encard (minimalPrimes (R i)) := by
  classical
  let T := Ring.DirectLimit R (fun i j h => (f i j h : R i → R j))
  apply le_antisymm
  · refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
    obtain ⟨s, hs, hscard⟩ := Set.exists_subset_encard_eq hn
    have hsf : s.Finite := Set.finite_of_encard_eq_coe hscard
    obtain ⟨i, hi⟩ := finite_minimalPrimes_le_stage R f
      (fun i j h => (hff i j h).flat) hsf.toFinset
      (fun q hq => hs (hsf.mem_toFinset.mp hq))
    simpa only [← hsf.encard_eq_coe_toFinset_card, hscard] using
      hi.trans (le_iSup (fun i => Set.encard (minimalPrimes (R i))) i)
  · refine iSup_le fun i => ?_
    let ofi := Ring.DirectLimit.of R (fun i j h => (f i j h : R i → R j)) i
    have hinj : Function.Injective ofi := Ring.DirectLimit.of_injective f
      (fun i j h => (hff i j h).injective) i
    have himg (p : Ideal (R i)) (hp : p ∈ minimalPrimes (R i)) :
        ∃ q : Ideal T, q ∈ minimalPrimes T ∧ q.comap ofi = p := by
      obtain ⟨q, -, rfl⟩ :=
        Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective hinj p hp
      exact Ideal.exists_minimalPrimes_comap_eq ofi _
        ⟨⟨hp.left.left, Ideal.comap_mono bot_le⟩,
          fun q' ⟨hq'prime, _⟩ hq'le => hp.right ⟨hq'prime, bot_le⟩ hq'le⟩
    let liftPrime : Ideal (R i) → Ideal T := fun p =>
      if hp : p ∈ minimalPrimes (R i) then Classical.choose (himg p hp) else ⊥
    have hlift (p : Ideal (R i)) (hp : p ∈ minimalPrimes (R i)) :
        liftPrime p ∈ minimalPrimes T ∧ (liftPrime p).comap ofi = p := by
      simpa only [liftPrime, dite_eq_left_of_eq_true (eq_true hp)] using
        Classical.choose_spec (himg p hp)
    exact Set.encard_le_encard_of_injOn (f := liftPrime) (fun p hp => (hlift p hp).1)
      fun p hp q hq heq => by rw [← (hlift p hp).2, ← (hlift q hq).2, heq]
