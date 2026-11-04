module

public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.Spectral.ConstructibleTopology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Spectrum.Prime.Profinite
public import StacksFrontier.Topology.Spectral.ConstructibleTopology

/-!
# Zero loci covering a punctured local spectrum

Let `A` be a local ring. This file records two consequences of a family of closed subsets
of `Spec A` covering everything but the generic point.

If `A` is a domain which is not a field and `S` is a multiplicatively closed collection of
finitely generated ideals whose zero loci cover every non-generic point of `Spec A`, then
the ideals of `S` intersect in zero. Applying this to the quotient by a prime shows that,
for a proper finitely generated ideal `J` and an ideal `I` contained in every positive power
of `J`, the zero locus of `I` contains every closed point of `Spec A \ V(J)`.

## Main results

* `PrimeSpectrum.sInf_eq_bot_of_iUnion_zeroLocus_eq_compl_genericPoint` is the vanishing of
  the intersection.
* `PrimeSpectrum.closedPoints_compl_zeroLocus_subset_zeroLocus` is the containment of closed
  points.

## Implementation notes

For a domain, the generic point of its spectrum is the prime ideal `⊥`, so its complement
is written as the set of primes whose underlying ideal is not `⊥`. The intersection of a set
of ideals is its lattice infimum `sInf`. The closed points of the open subspace
`Spec A \ V(J)` are taken in the subspace topology, as in the source, and their images under
the inclusion are asserted to lie in `V(I)`.

The first proof passes to the constructible topology on `Spec A`, in which the zero locus of
a finitely generated ideal is open and the whole space is compact; that turns the covering
hypothesis into a finite subcover and hence into a single ideal of `S`.

## References

* [Stacks Project, Tag 0ATA](https://stacks.math.columbia.edu/tag/0ATA)
* [Stacks Project, Tag 0ATB](https://stacks.math.columbia.edu/tag/0ATB)
-/

@[expose] public section

open Topology

universe u

namespace PrimeSpectrum

/-- **Stacks Project, Tag 0ATA.** A multiplicatively closed collection of finitely generated
ideals whose zero loci cover every non-generic point of the spectrum of a local domain has
zero intersection. -/
@[stacks 0ATA]
theorem sInf_eq_bot_of_iUnion_zeroLocus_eq_compl_genericPoint
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    (hA : ¬ IsField A) (S : Set (Ideal A))
    (hSfg : ∀ I ∈ S, I.FG)
    (hSmul : ∀ I ∈ S, ∀ J ∈ S, I * J ∈ S)
    (hcover : (⋃ I ∈ S, PrimeSpectrum.zeroLocus (I : Set A)) =
      {p : PrimeSpectrum A | p.asIdeal ≠ ⊥}) :
    sInf S = ⊥ := by
  refine le_bot_iff.mp fun x hx ↦ ?_
  have hxS : ∀ I ∈ S, x ∈ I := fun I hI ↦ (sInf_le hI) hx
  by_contra hx0
  have hcov : ∀ q : PrimeSpectrum A, q.asIdeal ≠ ⊥ → q ∈ ⋃ I ∈ S, zeroLocus (I : Set A) :=
    fun q hq ↦ hcover.symm.subset hq
  let m : PrimeSpectrum A := ⟨IsLocalRing.maximalIdeal A,
    (IsLocalRing.maximalIdeal.isMaximal A).isPrime⟩
  have hxmax : x ∈ IsLocalRing.maximalIdeal A := by
    have hmax_ne : IsLocalRing.maximalIdeal A ≠ (⊥ : Ideal A) :=
      fun h ↦ hA (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
    obtain ⟨I, hIS, hpI⟩ := Set.mem_iUnion₂.mp (hcov m hmax_ne)
    exact hpI (hxS I hIS)
  let X := PrimeSpectrum A
  have hclosed : @IsClosed X (constructibleTopology X)
      (PrimeSpectrum.zeroLocus ({x} : Set A)) := by
    simpa only [compl_compl] using
      (@IsOpen.isClosed_compl X (constructibleTopology X) _
        (IsCompact.isOpen_constructibleTopology_of_isOpen
          (PrimeSpectrum.isRetrocompact_zeroLocus_compl (Set.finite_singleton x)).isCompact
          (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl))
  have hopen : ∀ I : S, @IsOpen X (constructibleTopology X)
      (PrimeSpectrum.zeroLocus (I.1 : Set A)) := fun I ↦
    IsCompact.isOpen_constructibleTopology_of_isClosed
      (PrimeSpectrum.isRetrocompact_zeroLocus_compl_of_fg (hSfg I I.2)).isCompact
      (PrimeSpectrum.isClosed_zeroLocus _)
  have hcs : @CompactSpace X (constructibleTopology X) :=
    compactSpace_constructibleTopology X
  let : TopologicalSpace X := constructibleTopology X
  let : CompactSpace X := hcs
  have hcompact : IsCompact (PrimeSpectrum.zeroLocus ({x} : Set A)) := hclosed.isCompact
  have hsub : PrimeSpectrum.zeroLocus ({x} : Set A) ⊆
      ⋃ I : S, PrimeSpectrum.zeroLocus (I.1 : Set A) := by
    intro p hp
    have hpbot : p.asIdeal ≠ ⊥ := fun h ↦ hx0 (by simpa [h] using hp)
    simpa only [Set.iUnion_subtype] using hcov p hpbot
  obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover
    (fun I : S ↦ PrimeSpectrum.zeroLocus (I.1 : Set A)) hopen hsub
  have htne : t.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    rintro rfl
    have hm : m ∈ PrimeSpectrum.zeroLocus ({x} : Set A) := Set.singleton_subset_iff.mpr hxmax
    simpa using ht hm
  let I : Ideal A := t.prod fun J ↦ J.1
  have hmul : ∀ a b, a ∈ S → b ∈ S → a * b ∈ S := fun a b ha hb ↦ hSmul a ha b hb
  have hIS : I ∈ S :=
    Finset.prod_induction_nonempty _ (· ∈ S) hmul htne fun J _ ↦ J.2
  have hzero : PrimeSpectrum.zeroLocus ({x} : Set A) ⊆
      PrimeSpectrum.zeroLocus (I : Set A) := by
    intro p hp
    obtain ⟨J, hJt, hpJ⟩ := Set.mem_iUnion₂.mp (ht hp)
    show I ≤ p.asIdeal
    refine le_trans ?_ hpJ
    intro y hy
    rw [show I = J.1 * (t.erase J).prod (fun K ↦ K.1) by
      classical
      exact (Finset.mul_prod_erase _ _ hJt).symm] at hy
    exact Ideal.mul_le_left hy
  have hrad : I ≤ (Ideal.span ({x} : Set A)).radical :=
    (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp (by
      simpa [PrimeSpectrum.zeroLocus_span] using hzero)
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (hSfg I hIS)
  have hpowS : ∀ k : ℕ, I ^ (k + 1) ∈ S := fun k ↦ by
    simpa using Finset.prod_induction_nonempty (fun _ : Fin (k + 1) ↦ I) (· ∈ S) hmul
      Finset.univ_nonempty fun _ _ ↦ hIS
  have hxpow : x ∈ I ^ (2 * (n + 1)) := hxS _ (by
    simpa [mul_add, Nat.add_assoc] using hpowS (2 * n + 1))
  have hn' : I ^ (n + 1) ≤ Ideal.span ({x} : Set A) :=
    (Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn
  have hle : I ^ (2 * (n + 1)) ≤ Ideal.span ({x ^ 2} : Set A) := by
    rw [show 2 * (n + 1) = (n + 1) + (n + 1) by omega, pow_add]
    calc
      _ ≤ Ideal.span ({x} : Set A) * Ideal.span ({x} : Set A) := Ideal.mul_mono hn' hn'
      _ = Ideal.span ({x * x} : Set A) := Ideal.span_singleton_mul_span_singleton x x
      _ = Ideal.span ({x ^ 2} : Set A) := by rw [pow_two]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp (hle hxpow)
  have : IsUnit x := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨a, ?_⟩
    apply mul_left_cancel₀ hx0
    simpa [pow_two, mul_assoc] using ha.symm
  exact (IsLocalRing.mem_maximalIdeal x).mp hxmax this

/-- **Stacks Project, Tag 0ATB.** If `J` is a proper finitely generated ideal of a local ring
and `I` is contained in every positive power of `J`, then `V(I)` contains every closed point
of `Spec(A) \ V(J)`. -/
@[stacks 0ATB]
theorem closedPoints_compl_zeroLocus_subset_zeroLocus
    {A : Type u} [CommRing A] [IsLocalRing A] (I J : Ideal A)
    (hJ : J ≠ ⊤) (hJfg : J.FG)
    (hIJ : ∀ n : ℕ, 0 < n → I ≤ J ^ n) :
    Subtype.val '' closedPoints
        ((PrimeSpectrum.zeroLocus (J : Set A))ᶜ : Set (PrimeSpectrum A)) ⊆
      PrimeSpectrum.zeroLocus (I : Set A) := by
  classical
  let U : Set (PrimeSpectrum A) := (PrimeSpectrum.zeroLocus (J : Set A))ᶜ
  rintro z ⟨x, hx, rfl⟩
  let y : PrimeSpectrum A := x.val
  let p : Ideal A := y.asIdeal
  have hyU : y ∈ U := x.property
  have hyclosed : IsClosed ({x} : Set U) := mem_closedPoints_iff.mp hx
  have hJnot : ¬ J ≤ p := by
    change y ∉ PrimeSpectrum.zeroLocus (J : Set A) at hyU
    simpa [p, y, PrimeSpectrum.mem_zeroLocus] using hyU
  let B := A ⧸ p
  have : p.IsPrime := y.isPrime
  have : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr y.isPrime.1
  let : IsLocalRing B := IsLocalRing.of_surjective' (Ideal.Quotient.mk p)
    Ideal.Quotient.mk_surjective
  let : IsLocalHom (Ideal.Quotient.mk p) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have : IsDomain B := inferInstance
  let K : Ideal B := J.map (Ideal.Quotient.mk p)
  have hKneBot : K ≠ ⊥ := by
    obtain ⟨a, haJ, haP⟩ := SetLike.not_le_iff_exists.mp hJnot
    intro hK
    have hmk : Ideal.Quotient.mk p a ∈ K := Ideal.mem_map_of_mem _ haJ
    rw [hK, Ideal.mem_bot] at hmk
    exact haP (Ideal.Quotient.eq_zero_iff_mem.mp hmk)
  have hKleMax : K ≤ IsLocalRing.maximalIdeal B :=
    (Ideal.map_mono (IsLocalRing.le_maximalIdeal hJ)).trans
      (IsLocalRing.map_maximalIdeal_le (Ideal.Quotient.mk p))
  have hBnotField : ¬ IsField B := Ring.not_isField_of_ne_of_ne hKneBot
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal (R := B)).ne_top hKleMax)
  let S : Set (Ideal B) := {L | ∃ n : ℕ, 0 < n ∧ K ^ n = L}
  have hSfg : ∀ L ∈ S, L.FG := by
    rintro L ⟨n, _, rfl⟩
    exact (hJfg.map (Ideal.Quotient.mk p)).pow
  have hSmul : ∀ L ∈ S, ∀ M ∈ S, L * M ∈ S := by
    rintro L ⟨n, hn, rfl⟩ M ⟨m, hm, rfl⟩
    exact ⟨n + m, Nat.add_pos_left hn _, by rw [pow_add]⟩
  have hcover : (⋃ L ∈ S, PrimeSpectrum.zeroLocus (L : Set B)) =
      {q : PrimeSpectrum B | q.asIdeal ≠ ⊥} := by
    ext q
    constructor
    · intro hq hqbot
      obtain ⟨L, ⟨n, hn, rfl⟩, hqzero⟩ := Set.mem_iUnion₂.mp hq
      have hle : K ≤ q.asIdeal := (Ideal.IsPrime.pow_le_iff (I := K) (P := q.asIdeal) hn.ne').mp
        ((PrimeSpectrum.mem_zeroLocus q (K ^ n : Ideal B)).mp hqzero)
      exact hKneBot (le_antisymm (by simpa [hqbot] using hle) bot_le)
    · intro hq
      let qA : PrimeSpectrum A := PrimeSpectrum.comap (Ideal.Quotient.mk p) q
      have hpqA : p ≤ qA.asIdeal := by
        rw [PrimeSpectrum.comap_asIdeal]
        exact (Ideal.mk_ker (I := p)).symm.trans_le (Ideal.ker_le_comap _)
      have hqAne : qA.asIdeal ≠ p := by
        intro hEq
        have hmap : qA.asIdeal.map (Ideal.Quotient.mk p) = q.asIdeal := by
          simpa [qA] using (Ideal.map_comap_of_surjective
            (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective q.asIdeal)
        rw [hEq, Ideal.map_quotient_self] at hmap
        exact hq hmap.symm
      have hpqA' : p < qA.asIdeal := lt_of_le_of_ne hpqA (Ne.symm hqAne)
      have hqAnotU : qA ∉ U := by
        intro hqAU
        have hspec : (⟨qA, hqAU⟩ : U) ∈ closure ({x} : Set U) := by
          rw [closure_subtype]
          simpa using (PrimeSpectrum.le_iff_mem_closure y qA).mp
            (show y ≤ qA by change y.asIdeal ≤ qA.asIdeal; exact hpqA'.le)
        have heq : (⟨qA, hqAU⟩ : U) = x := by
          simpa [hyclosed.closure_eq] using hspec
        exact hqAne (by simpa [p] using congrArg (fun w : U => w.val.asIdeal) heq)
      have hJqA : J ≤ qA.asIdeal :=
        (PrimeSpectrum.mem_zeroLocus qA (J : Set A)).mp (by simpa [U] using hqAnotU)
      have hKq : K ≤ q.asIdeal := Ideal.map_le_iff_le_comap.mpr hJqA
      exact Set.mem_iUnion.mpr ⟨K, Set.mem_iUnion.mpr
        ⟨⟨1, by decide, by simp⟩, (PrimeSpectrum.mem_zeroLocus q (K : Set B)).mpr hKq⟩⟩
  have hbig := sInf_eq_bot_of_iUnion_zeroLocus_eq_compl_genericPoint
    hBnotField S hSfg hSmul hcover
  rw [PrimeSpectrum.mem_zeroLocus]
  intro f hfI
  have hfS : Ideal.Quotient.mk p f ∈ sInf S := by
    rw [Ideal.mem_sInf]
    rintro L ⟨n, hn, rfl⟩
    have hmap : (I.map (Ideal.Quotient.mk p)) ≤ K ^ n := by
      rw [← Ideal.map_pow]
      exact Ideal.map_mono (hIJ n hn)
    exact hmap (Ideal.mem_map_of_mem _ hfI)
  rw [hbig] at hfS
  exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hfS)

end PrimeSpectrum
