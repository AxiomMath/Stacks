module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.Topology.Dimension.Codimension
public import StacksFrontier.Topology.Dimension.CodimensionOpen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Codimension in an affine scheme is the height of an ideal

The codimension of an irreducible closed subset of a topological space ([Stacks, Tag 02I3],
`codimension`) is the coheight of that subset in the poset of irreducible closed subsets. On
`Spec R` the irreducible closed subsets are the zero loci `V(p)` of the prime ideals, and the
order isomorphism `PrimeSpectrum.pointsEquivIrreducibleCloseds` reverses inclusion, so the
coheight of `V(p)` is the *height* of `p`. This module records that identification and the two
forms in which a codimension hypothesis stated on a scheme is consumed by commutative algebra:
as a bound on the heights of the minimal primes of an ideal, on an affine open.

## Main definitions

* `PrimeSpectrum.irreducibleClosedsOfPrime`: the irreducible closed subset `V(p) ⊆ Spec R`.

## Main results

* `PrimeSpectrum.codimension_irreducibleClosedsOfPrime`: `codim(V(p), Spec R) = height p`.
* `PrimeSpectrum.codimension_eq_height_vanishingIdeal`: the codimension of an irreducible closed
  subset of `Spec R` is the height of the prime ideal of its generic point.
* `PrimeSpectrum.le_height_of_mem_minimalPrimes`: a codimension bound for the irreducible closed
  subsets of `Spec R` contained in `V(I)` is a height bound on the minimal primes of `I`.
* `PrimeSpectrum.le_height_of_mem_minimalPrimes_of_isOpenEmbedding`: the same with the
  codimension bound given on an ambient space of which `Spec R` is an open subspace, which is
  the shape in which a hypothesis on a scheme is read on an affine chart.
* `PrimeSpectrum.height_vanishingIdealTrace`: the *exact* form of the same translation. The
  prime of `R` cutting out the trace on `Spec R` of an irreducible closed subset `Y` of an
  ambient space has height exactly `codim(Y, X)`.
* `PrimeSpectrum.vanishingIdealTrace_mem_minimalPrimes`: that prime is a *minimal* prime over an
  ideal `I` whose zero locus lands in a closed set `C` in which `Y` is maximal. Together the two
  turn an exact codimension hypothesis about a single irreducible component into the ring-level
  datum `∃ p ∈ I.minimalPrimes, height p = e`.
* `codimension_le_of_le`: codimension is antitone.

## Implementation notes

Codimension is invariant under passing to an open subspace; that is [Stacks, Tag 02I4], proved
in this library as `TopologicalSpace.IrreducibleCloseds.coheight_restrictOpen`, and in Mathlib
as `Topology.IsOpenEmbedding.coheight_map`, which is the form used here because the irreducible
closed subset at hand is given on the open subspace and pushed forward. Neither needs a
sobriety or separation hypothesis.

Together with antitonicity (`codimension_le_of_le`) this makes the hypothesis "every irreducible
closed subset of `X` contained in `Z` has codimension at least `e`" equivalent to the Stacks
phrasing "every irreducible component of `Z` has codimension at least `e`": a component is such
a subset, and conversely any such subset is contained in a component, whose codimension is then
no larger. The first phrasing is the one used downstream because it transports along an open
immersion with no bookkeeping about which components meet the chart.

## References

* [Stacks Project, Tag 02I3](https://stacks.math.columbia.edu/tag/02I3)
* [Stacks Project, Tag 02I4](https://stacks.math.columbia.edu/tag/02I4)
-/

@[expose] public section

open TopologicalSpace

/-- **Codimension is antitone.** If `Y ⊆ Y'` are irreducible closed subsets of `X` then
`codim(Y', X) ≤ codim(Y, X)`: a strict chain of irreducible closed subsets ascending from `Y'`
ascends from `Y` as well. -/
theorem codimension_le_of_le {X : Type*} [TopologicalSpace X] {Y Y' : IrreducibleCloseds X}
    (h : Y ≤ Y') : codimension Y' ≤ codimension Y :=
  Order.coheight_anti h

namespace PrimeSpectrum

variable {R : Type*} [CommRing R]

/-- The irreducible closed subset `V(p) ⊆ Spec R` cut out by a prime ideal: it is the closure of
the point `p`, hence irreducible, and it is a zero locus, hence closed. -/
@[ega "0 16.1.1" "partial", ega "I 1.1.14" "partial"]
def irreducibleClosedsOfPrime (p : PrimeSpectrum R) : IrreducibleCloseds (PrimeSpectrum R) where
  carrier := zeroLocus (p.asIdeal : Set R)
  isIrreducible' := closure_singleton p ▸ isIrreducible_singleton.closure
  isClosed' := isClosed_zeroLocus _

/-- The underlying set of `irreducibleClosedsOfPrime p` is the zero locus of `p`. -/
@[simp]
theorem coe_irreducibleClosedsOfPrime (p : PrimeSpectrum R) :
    (irreducibleClosedsOfPrime p : Set (PrimeSpectrum R)) = zeroLocus (p.asIdeal : Set R) :=
  rfl

/-- **Codimension in an affine scheme is the height of the prime.** The codimension of the
irreducible closed subset `V(p)` of `Spec R` is the height of `p`.

The order isomorphism `PrimeSpectrum.pointsEquivIrreducibleCloseds` carries `p` to `V(p)` and
reverses inclusion, so the coheight of `V(p)` is the height of `p` in the poset of primes, which
is `Ideal.height` by `PrimeSpectrum.height_eq_orderHeight`. -/
@[ega "0 16.1.3" "codim(V(p)", ega "IV 5.1.1" "5.1.1.3 for prime ideals"]
theorem codimension_irreducibleClosedsOfPrime (p : PrimeSpectrum R) :
    codimension (irreducibleClosedsOfPrime p) = p.asIdeal.height := by
  have hEq : OrderDual.ofDual (PrimeSpectrum.pointsEquivIrreducibleCloseds R p) =
      irreducibleClosedsOfPrime p :=
    IrreducibleCloseds.ext (closure_singleton p)
  rw [codimension_eq_coheight, ← hEq, Order.coheight_ofDual, Order.height_orderIso]
  exact (p.height_eq_orderHeight).symm

/-- **The codimension of an irreducible closed subset of an affine scheme.** It is the height of
the prime ideal of functions vanishing on it, that is of the prime of its generic point. -/
@[ega "0 16.1.3" "codim(V(p)", ega "IV 5.1.1" "special case"]
theorem codimension_eq_height_vanishingIdeal (Y : IrreducibleCloseds (PrimeSpectrum R)) :
    codimension Y = (vanishingIdeal (Y : Set (PrimeSpectrum R))).height := by
  have hp : (vanishingIdeal (Y : Set (PrimeSpectrum R))).IsPrime :=
    isIrreducible_iff_vanishingIdeal_isPrime.mp Y.isIrreducible
  have hY : Y = irreducibleClosedsOfPrime ⟨_, hp⟩ := by
    refine IrreducibleCloseds.ext ?_
    change (Y : Set (PrimeSpectrum R)) = zeroLocus (vanishingIdeal (Y : Set (PrimeSpectrum R)))
    rw [zeroLocus_vanishingIdeal_eq_closure, Y.isClosed.closure_eq]
  exact (congrArg codimension hY).trans (codimension_irreducibleClosedsOfPrime _)

/-- **A codimension bound read on the minimal primes.** If every irreducible closed subset of
`Spec R` contained in `V(I)` has codimension at least `e`, then every minimal prime over `I` has
height at least `e`: the zero locus of such a prime is one of those subsets. -/
theorem le_height_of_mem_minimalPrimes {I : Ideal R} {e : ℕ∞}
    (h : ∀ Y : IrreducibleCloseds (PrimeSpectrum R),
      (Y : Set (PrimeSpectrum R)) ⊆ zeroLocus (I : Set R) → e ≤ codimension Y)
    {q : Ideal R} (hq : q ∈ I.minimalPrimes) : e ≤ q.height := by
  have hmem := h (irreducibleClosedsOfPrime ⟨q, hq.isPrime⟩) (zeroLocus_anti_mono_ideal hq.1.2)
  rwa [codimension_irreducibleClosedsOfPrime] at hmem

/-- The image in `X` of `V(q)`, as an irreducible closed subset, lies in a closed set `C` that
contains the image of `V(I)` whenever `I ≤ q`. -/
private theorem map_irreducibleClosedsOfPrime_subset {X : Type*} [TopologicalSpace X]
    {f : PrimeSpectrum R → X} (hf : Continuous f) {C : Set X} (hC : IsClosed C) {I : Ideal R}
    (hI : f '' zeroLocus (I : Set R) ⊆ C) {q : PrimeSpectrum R} (hIq : I ≤ q.asIdeal) :
    (IrreducibleCloseds.map f hf (irreducibleClosedsOfPrime q) : Set X) ⊆ C := by
  rw [IrreducibleCloseds.coe_map]
  exact hC.closure_subset_iff.mpr ((Set.image_mono (zeroLocus_anti_mono_ideal hIq)).trans hI)

/-- **A codimension bound on a space, read on the minimal primes of an affine open.** Let `Z` be
a closed subset of a space `X`, let `Spec R` be an open subspace of `X` through an open
embedding `f`, and let `I` be an ideal of `R` whose zero locus lands in `Z`. If every
irreducible closed subset of `X` contained in `Z` has codimension at least `e`, then every
minimal prime over `I` has height at least `e`.

This is the form in which a codimension hypothesis on a scheme is consumed on an affine chart:
the closure in `X` of `V(q)` is an irreducible closed subset of `X` contained in `Z`, and
codimension is unchanged by the open immersion. -/
theorem le_height_of_mem_minimalPrimes_of_isOpenEmbedding {X : Type*} [TopologicalSpace X]
    {f : PrimeSpectrum R → X} (hf : Topology.IsOpenEmbedding f) {Z : Set X} (hZ : IsClosed Z)
    {e : ℕ∞}
    (hcodim : ∀ Y : IrreducibleCloseds X, (Y : Set X) ⊆ Z → e ≤ codimension Y)
    {I : Ideal R} (hI : f '' zeroLocus (I : Set R) ⊆ Z)
    {q : Ideal R} (hq : q ∈ I.minimalPrimes) : e ≤ q.height := by
  have hmem := hcodim (IrreducibleCloseds.map f hf.continuous
    (irreducibleClosedsOfPrime (⟨q, hq.isPrime⟩ : PrimeSpectrum R)))
    (map_irreducibleClosedsOfPrime_subset hf.continuous hZ hI hq.1.2)
  rwa [codimension_eq_coheight, hf.coheight_map, ← codimension_eq_coheight,
    codimension_irreducibleClosedsOfPrime] at hmem

/-! ### The exact codimension of one irreducible closed subset -/

section Trace

variable {X : Type*} [TopologicalSpace X] {f : PrimeSpectrum R → X}

/-- **The trace of an irreducible closed subset on an open affine piece is a zero locus**: it is
the zero locus of the prime ideal of functions vanishing on it. -/
theorem zeroLocus_vanishingIdeal_preimage (hf : Topology.IsOpenEmbedding f)
    (Y : IrreducibleCloseds X) :
    zeroLocus (vanishingIdeal (f ⁻¹' (Y : Set X)) : Set R) = f ⁻¹' (Y : Set X) := by
  rw [zeroLocus_vanishingIdeal_eq_closure]
  exact (Y.isClosed.preimage hf.continuous).closure_eq

/-- The ideal of functions vanishing on the trace of an irreducible closed subset is prime. -/
theorem isPrime_vanishingIdeal_preimage (hf : Topology.IsOpenEmbedding f)
    (Y : IrreducibleCloseds X) (hne : (f ⁻¹' (Y : Set X)).Nonempty) :
    (vanishingIdeal (f ⁻¹' (Y : Set X))).IsPrime :=
  isIrreducible_iff_vanishingIdeal_isPrime.mp
    (Y.comapOpenEmbedding hf hne).isIrreducible

/-- **The exact codimension of an irreducible closed subset, read as a height on an open affine
piece.** Let `Spec R` be an open subspace of a space `X` through an open embedding `f` and let
`Y ⊆ X` be an irreducible closed subset meeting it. Then the prime ideal of `R` cutting out the
trace `f ⁻¹' Y` has height exactly `codim(Y, X)`.

This is the *equality* strengthening of
`PrimeSpectrum.le_height_of_mem_minimalPrimes_of_isOpenEmbedding`, available because the
irreducible closed subset is pinned rather than quantified over: the trace is an irreducible
closed subset of `Spec R` whose codimension there is the height of its prime
(`PrimeSpectrum.codimension_eq_height_vanishingIdeal`) and is `codim(Y, X)` by [Stacks, Tag 02I4]
(`TopologicalSpace.IrreducibleCloseds.coheight_comapOpenEmbedding`). -/
@[stacks 02I4 "the codimension of one irreducible closed subset, as a height on an affine open",
  ega "0 16.1.3" "codim(V(p)",
  ega "IV 5.1.1" "special case"]
theorem height_vanishingIdeal_preimage (hf : Topology.IsOpenEmbedding f)
    (Y : IrreducibleCloseds X) (hne : (f ⁻¹' (Y : Set X)).Nonempty) :
    (vanishingIdeal (f ⁻¹' (Y : Set X))).height = codimension Y := by
  have h1 := codimension_eq_height_vanishingIdeal (Y.comapOpenEmbedding hf hne)
  rw [IrreducibleCloseds.coe_comapOpenEmbedding] at h1
  rw [← h1, codimension_eq_coheight, codimension_eq_coheight]
  exact (Y.coheight_comapOpenEmbedding hf hne).symm

/-- **A maximal irreducible closed subset of a closed set cuts out a minimal prime.** Let `C` be
a closed subset of `X`, let `Y` be maximal among the irreducible closed subsets of `X` contained
in `C` — that is, an irreducible component of `C` — and let `I` be an ideal of `R` whose zero
locus lands in `C` and which vanishes on the trace of `Y`. Then the prime cutting out the trace
of `Y` is a *minimal* prime over `I`.

A prime `q` with `I ⊆ q ⊆ p` has `V(p) ⊆ V(q) ⊆ V(I)`, so the closure in `X` of the image of
`V(q)` is an irreducible closed subset of `C` containing `Y`; by maximality it *is* `Y`, so
`V(q) ⊆ f ⁻¹' Y = V(p)` and hence `p ⊆ q`. -/
@[ega "0 16.3.1" "partial", ega "I 1.1.14" "partial"]
theorem vanishingIdeal_preimage_mem_minimalPrimes (hf : Topology.IsOpenEmbedding f)
    (Y : IrreducibleCloseds X) (hne : (f ⁻¹' (Y : Set X)).Nonempty) {C : Set X} (hC : IsClosed C)
    (hmax : Maximal (fun W : IrreducibleCloseds X => (W : Set X) ⊆ C) Y) {I : Ideal R}
    (hIC : f '' zeroLocus (I : Set R) ⊆ C)
    (hIY : f ⁻¹' (Y : Set X) ⊆ zeroLocus (I : Set R)) :
    vanishingIdeal (f ⁻¹' (Y : Set X)) ∈ I.minimalPrimes := by
  refine ⟨⟨isPrime_vanishingIdeal_preimage hf Y hne,
    (subset_zeroLocus_iff_le_vanishingIdeal _ _).mp hIY⟩, ?_⟩
  rintro q ⟨hqp, hIq⟩ hqle
  have hWC : (IrreducibleCloseds.map f hf.continuous
      (irreducibleClosedsOfPrime (⟨q, hqp⟩ : PrimeSpectrum R)) : Set X) ⊆ C := by
    exact map_irreducibleClosedsOfPrime_subset hf.continuous hC hIC hIq
  have hlet : Y.comapOpenEmbedding hf hne ≤
      irreducibleClosedsOfPrime (⟨q, hqp⟩ : PrimeSpectrum R) := by
    change f ⁻¹' (Y : Set X) ⊆ zeroLocus (q : Set R)
    rw [← zeroLocus_vanishingIdeal_preimage hf Y]
    exact zeroLocus_anti_mono_ideal hqle
  have hYW : Y ≤ IrreducibleCloseds.map f hf.continuous
      (irreducibleClosedsOfPrime (⟨q, hqp⟩ : PrimeSpectrum R)) := by
    rw [← Y.map_comapOpenEmbedding hf hne]
    exact IrreducibleCloseds.map_mono hf.continuous hlet
  have hWY : (IrreducibleCloseds.map f hf.continuous
      (irreducibleClosedsOfPrime (⟨q, hqp⟩ : PrimeSpectrum R)) : Set X) ⊆ (Y : Set X) :=
    hmax.2 hWC hYW
  have hsub : zeroLocus (q : Set R) ⊆ f ⁻¹' (Y : Set X) := fun x hx =>
    hWY (by rw [IrreducibleCloseds.coe_map]; exact subset_closure ⟨x, hx, rfl⟩)
  exact (vanishingIdeal_anti_mono hsub).trans_eq
    ((vanishingIdeal_zeroLocus_eq_radical q).trans hqp.radical)

end Trace

end PrimeSpectrum

end
