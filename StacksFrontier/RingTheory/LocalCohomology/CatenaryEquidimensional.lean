module

public import StacksFrontier.RingTheory.Catenary.Basic
public import StacksFrontier.RingTheory.Catenary.Formal
public import StacksFrontier.RingTheory.Equidimensional.FlatLocal
public import StacksFrontier.RingTheory.LocalCohomology.HartshorneConnectednessHenselian
public import StacksFrontier.RingTheory.Serre.Defs
import StacksCore.Tactic.EgaSgaAttribute
import StacksFrontier.RingTheory.Catenary.Saturated

/-!
# Equidimensionality of a catenary local ring satisfying `(S₂)`

Let `A` be a Noetherian local ring which is catenary and satisfies Serre's condition `(S₂)`.
Then `Spec(A)` is equidimensional: all of its irreducible components have the same dimension.

The argument is the one of [Stacks, Lemma 0FIW], a contradiction from Hartshorne's connectedness
lemma. Split the minimal primes of `A` into those `p` with `dim(A ⧸ p) = dim(A)` and the rest,
and let `I`, `J` be the products of the two families, so that `V(I)` and `V(J)` are the unions
of the top-dimensional and of the smaller-dimensional irreducible components. If both families
are nonempty then `V(I + J) = V(I) ∩ V(J)` contains the closed point, hence is nonempty; let `z`
be a generic point of one of its irreducible components, that is a minimal prime over `I + J`,
and pick minimal primes `P ≤ z` in the first family and `Q ≤ z` in the second. Neither can equal
`z`, so both lie strictly below it, and catenarity forbids `P ⋖ z` and `Q ⋖ z` simultaneously: a
covering pair drops the coheight by exactly one, which would force
`dim(A ⧸ P) = dim(A ⧸ Q)`. Refining the pair that does not cover exhibits a chain of length two
below `z`, so `dim(A_z) ≥ 2`, and `(S₂)` turns this into `depth(A_z) ≥ 2`. But the punctured
spectrum of `A_z` is covered by the two closed subsets cut out by `I` and by `J`, they are
disjoint on it — a prime below `z` containing `I + J` is `z` itself, by minimality of `z` — and
each is nonempty, containing the point lying over `P` resp. over `Q`. So the punctured spectrum
of `A_z` is disconnected, contradicting [Stacks, Lemma 0BLR].

## Main results

* `Stacks.Equidimensional.equidimensional_of_isCatenary_of_propertySkRing_two` — the spectrum of
  a catenary Noetherian local ring satisfying `(S₂)` is equidimensional.

## Implementation notes

The three notions of the source are modelled as follows. Catenarity of `A` is `Ring.IsCatenary`
(`StacksFrontier/RingTheory/Catenary/Basic.lean`, Definition 00NI). Serre's condition `(S₂)` is
`PropertySkRing A 2` (`StacksFrontier/RingTheory/Serre/Defs.lean`, Definition 031P), that is
`min{2, dim A_𝔭} ≤ depth A_𝔭` at every prime `𝔭`. Equidimensionality of `Spec(A)` is
`TopologicalSpace.Equidimensional (PrimeSpectrum A)`
(`StacksFrontier/Topology/Dimension/Equidimensional.lean`, Definition 0058), namely that any two
irreducible components have the same `topologicalKrullDim` as subspaces.

"Equidimensional" has several inequivalent readings, so it is worth recording which one this is.
The irreducible components of `Spec(A)` are the closed sets `V(p)` for `p` a minimal prime, and
the dimension of `V(p)` is `dim(A ⧸ p)`; the condition therefore unfolds to: **all minimal primes
of `A` have the same coheight, i.e. `dim(A ⧸ p)` is independent of the minimal prime `p`.** That
is exactly `SpecEquidimensional A` of
`StacksFrontier/RingTheory/Equidimensional/FlatLocal.lean`, and the two are identified by
`specEquidimensional_iff_equidimensional` in the same file (whose proof runs through
`PrimeSpectrum.zeroLocus_minimalPrimes` and `topologicalKrullDim_zeroLocus`). The proof below
works with `SpecEquidimensional` and converts once, at the start; the tagged statement is the
topological one.

Catenarity enters only through `coheight_covby_of_catenary`, which is stated for the
saturated-chain spelling `IsCatenaryRingSaturated`; the passage from `Ring.IsCatenary` to it is
`_root_.isCatenaryRingSaturated_of_isCatenary` of
`StacksFrontier/RingTheory/Catenary/Saturated.lean`. The depth produced by `(S₂)` is
`ringDepth`, while Hartshorne's lemma is stated for `Module.depth`; the two are identified by the
public `ringDepth_eq_depth_maximalIdeal`.

## References

* [Stacks Project, Tag 0FIW](https://stacks.math.columbia.edu/tag/0FIW)
* [Stacks Project, Tag 0BLR](https://stacks.math.columbia.edu/tag/0BLR), Hartshorne's
  connectedness lemma
* [EGA IV, Corollary 5.10.9]
-/

@[expose] public section

open IsLocalRing PrimeSpectrum TopologicalSpace

universe u

namespace Stacks.Equidimensional

/-- The zero locus of a finite product of ideals is the union of their zero loci. -/
private lemma zeroLocus_finsetProd {A : Type u} [CommRing A] (s : Finset (Ideal A)) :
    zeroLocus (↑(s.prod id) : Set A) = ⋃ p ∈ s, zeroLocus (p : Set A) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    rw [Finset.prod_insert hp, Finset.set_biUnion_insert, ← ih]
    exact zeroLocus_mul (id p) (s.prod id)

/-- A finite product of ideals is contained in each of its factors. -/
private lemma finsetProd_le {A : Type u} [CommRing A] (s : Finset (Ideal A)) {r : Ideal A}
    (hr : r ∈ s) : s.prod id ≤ r := by
  classical
  calc s.prod id = (s.erase r).prod id * id r := (Finset.prod_erase_mul s id hr).symm
    _ ≤ r := Ideal.mul_le_right

/-- **The disconnection.** Let `z` be a minimal prime over `I + J` and let `P, Q` be primes
strictly below `z` with `I ≤ P` and `J ≤ Q`. If every prime below `z` contains `I` or contains
`J`, then the punctured spectrum of a localization `B` of `A` at `z` is disconnected: the traces
of `V(I)` and `V(J)` on it are closed, cover it, are disjoint, and each is nonempty. -/
private theorem not_isPreconnected_compl_closedPoint {A : Type u} [CommRing A] {I J : Ideal A}
    {z P Q : PrimeSpectrum A} (hz : z.asIdeal ∈ (I + J).minimalPrimes)
    (hPz : P < z) (hQz : Q < z) (hPI : I ≤ P.asIdeal) (hQJ : J ≤ Q.asIdeal)
    (hIJ : ∀ x : PrimeSpectrum A, x ≤ z → I ≤ x.asIdeal ∨ J ≤ x.asIdeal)
    (B : Type u) [CommRing B] [IsLocalRing B] [Algebra A B]
    [IsLocalization.AtPrime B z.asIdeal] :
    ¬ IsPreconnected ({closedPoint B}ᶜ : Set (PrimeSpectrum B)) := by
  intro hconn
  let f : PrimeSpectrum B → PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B)
  let e := IsLocalization.AtPrime.primeSpectrumOrderIso B z.asIdeal
  have hef : ∀ x : PrimeSpectrum B, ((e x : PrimeSpectrum A)) = f x := fun _ => rfl
  have hfz : ∀ x : PrimeSpectrum B, f x ≤ z := fun x => hef x ▸ (e x).2
  have hfc : f (closedPoint B) = z :=
    PrimeSpectrum.ext (IsLocalization.AtPrime.under_maximalIdeal B z.asIdeal)
  have hsymm : ∀ (T : PrimeSpectrum A) (hT : T ≤ z), f (e.symm ⟨T, hT⟩) = T := fun T hT => by
    rw [← hef]; exact congrArg Subtype.val (e.apply_symm_apply ⟨T, hT⟩)
  have hcov : ({closedPoint B}ᶜ : Set (PrimeSpectrum B)) ⊆
      f ⁻¹' zeroLocus (I : Set A) ∪ f ⁻¹' zeroLocus (J : Set A) := fun x _ =>
    (Set.mem_union _ _ _).mpr <| (hIJ (f x) (hfz x)).imp
      (fun h => (mem_zeroLocus _ _).2 h) fun h => (mem_zeroLocus _ _).2 h
  have hdis : ({closedPoint B}ᶜ : Set (PrimeSpectrum B)) ∩
      (f ⁻¹' zeroLocus (I : Set A) ∩ f ⁻¹' zeroLocus (J : Set A)) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    obtain ⟨hxU, hxI, hxJ⟩ := hx
    have hsum : I + J ≤ (f x).asIdeal := by
      rw [Ideal.add_eq_sup, sup_le_iff]
      exact ⟨(mem_zeroLocus _ _).mp hxI, (mem_zeroLocus _ _).mp hxJ⟩
    have hfx : f x = z :=
      PrimeSpectrum.ext (le_antisymm (hfz x) (hz.2 ⟨(f x).2, hsum⟩ (hfz x)))
    exact hxU (e.injective (Subtype.ext (by simp only [hef, hfc, hfx])))
  have hPmem : e.symm ⟨P, hPz.le⟩ ∈ ({closedPoint B}ᶜ : Set (PrimeSpectrum B)) ∩
      f ⁻¹' zeroLocus (I : Set A) := by
    refine ⟨fun hx => hPz.ne (by rw [← hsymm P hPz.le, hx, hfc]), ?_⟩
    change f _ ∈ zeroLocus (I : Set A)
    rw [hsymm P hPz.le]
    exact (mem_zeroLocus _ _).2 hPI
  have hQmem : e.symm ⟨Q, hQz.le⟩ ∈ ({closedPoint B}ᶜ : Set (PrimeSpectrum B)) ∩
      f ⁻¹' zeroLocus (J : Set A) := by
    refine ⟨fun hx => hQz.ne (by rw [← hsymm Q hQz.le, hx, hfc]), ?_⟩
    change f _ ∈ zeroLocus (J : Set A)
    rw [hsymm Q hQz.le]
    exact (mem_zeroLocus _ _).2 hQJ
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hconn _ _
    ((isClosed_zeroLocus _).preimage (continuous_comap _))
    ((isClosed_zeroLocus _).preimage (continuous_comap _)) hcov hdis with h | h
  · exact Set.eq_empty_iff_forall_notMem.mp hdis _ ⟨hQmem.1, h hQmem.1, hQmem.2⟩
  · exact Set.eq_empty_iff_forall_notMem.mp hdis _ ⟨hPmem.1, hPmem.2, h hPmem.1⟩

/-- **Stacks Project, Tag 0FIW** (EGA IV, Corollary 5.10.9). Let `A` be a Noetherian local ring
which is catenary and satisfies Serre's condition `(S₂)`. Then `Spec(A)` is equidimensional. -/
@[stacks 0FIW, ega "IV 5.10.9"]
theorem equidimensional_of_isCatenary_of_propertySkRing_two (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (hcat : Ring.IsCatenary A)
    (hS₂ : PropertySkRing A 2) :
    Equidimensional (PrimeSpectrum A) := by
  classical
  refine specEquidimensional_iff_equidimensional.mp ?_
  by_contra hne
  -- The minimal primes of `A`, split by whether they compute the dimension of `A`.
  obtain ⟨mins, hmins⟩ : ∃ t : Finset (Ideal A), ∀ r, r ∈ t ↔ r ∈ minimalPrimes A :=
    ⟨(minimalPrimes.finite_of_isNoetherianRing A).toFinset, fun _ => Set.Finite.mem_toFinset _⟩
  obtain ⟨hi, hhimem⟩ : ∃ t : Finset (Ideal A), ∀ r, r ∈ t ↔
      r ∈ minimalPrimes A ∧ ringKrullDim (A ⧸ r) = ringKrullDim A :=
    ⟨mins.filter fun r => ringKrullDim (A ⧸ r) = ringKrullDim A,
      fun r => by rw [Finset.mem_filter, hmins]⟩
  obtain ⟨lo, hlomem⟩ : ∃ t : Finset (Ideal A), ∀ r, r ∈ t ↔
      r ∈ minimalPrimes A ∧ ringKrullDim (A ⧸ r) ≠ ringKrullDim A :=
    ⟨mins.filter fun r => ringKrullDim (A ⧸ r) ≠ ringKrullDim A,
      fun r => by rw [Finset.mem_filter, hmins]⟩
  -- Both families are nonempty: the first by `exists_mem_minimalPrimes_ringKrullDim_quotient_eq`,
  -- the second because otherwise `Spec A` is equidimensional.
  obtain ⟨p₀, hp₀, hp₀dim⟩ := exists_mem_minimalPrimes_ringKrullDim_quotient_eq A
  obtain ⟨r₁, hr₁⟩ : hi.Nonempty := ⟨p₀, (hhimem p₀).mpr ⟨hp₀, hp₀dim⟩⟩
  obtain ⟨r₂, hr₂⟩ : lo.Nonempty := by
    refine Finset.nonempty_iff_ne_empty.2 fun hempty => hne fun r hr s hs => ?_
    have key : ∀ t ∈ minimalPrimes A, ringKrullDim (A ⧸ t) = ringKrullDim A := by
      intro t ht
      by_contra hc
      exact absurd ((hlomem t).mpr ⟨ht, hc⟩) (by rw [hempty]; exact Finset.notMem_empty t)
    rw [key r hr, key s hs]
  have : r₁.IsPrime := ((hhimem r₁).mp hr₁).1.1.1
  have : r₂.IsPrime := ((hlomem r₂).mp hr₂).1.1.1
  -- `V(I) ∩ V(J)` contains the closed point, so it has a generic point `z`.
  have hIsum : hi.prod id + lo.prod id ≤ maximalIdeal A := by
    rw [Ideal.add_eq_sup, sup_le_iff]
    exact ⟨(finsetProd_le hi hr₁).trans (le_maximalIdeal_of_isPrime r₁),
      (finsetProd_le lo hr₂).trans (le_maximalIdeal_of_isPrime r₂)⟩
  obtain ⟨z, hzmin⟩ : ∃ z : PrimeSpectrum A,
      z.asIdeal ∈ (hi.prod id + lo.prod id).minimalPrimes := by
    obtain ⟨zI, hz, -⟩ := Ideal.exists_minimalPrimes_le
      (I := hi.prod id + lo.prod id) (J := maximalIdeal A) hIsum
    exact ⟨⟨zI, hz.1.1⟩, hz⟩
  obtain ⟨hzhi, hzlo⟩ : hi.prod id ≤ z.asIdeal ∧ lo.prod id ≤ z.asIdeal := by
    rw [← sup_le_iff, ← Ideal.add_eq_sup]; exact hzmin.1.2
  -- A minimal prime of each kind below `z`.
  have hbelow : ∀ (t : Finset (Ideal A)), (∀ r ∈ t, r ∈ minimalPrimes A) →
      t.prod id ≤ z.asIdeal → ∃ T : PrimeSpectrum A, T.asIdeal ∈ t ∧ T.asIdeal ≤ z.asIdeal := by
    intro t ht hle
    have hmem : z ∈ zeroLocus (↑(t.prod id) : Set A) := (mem_zeroLocus _ _).2 hle
    rw [zeroLocus_finsetProd] at hmem
    obtain ⟨r, hr, hrz⟩ := Set.mem_iUnion₂.mp hmem
    exact ⟨⟨r, (ht r hr).1.1⟩, hr, (mem_zeroLocus _ _).mp hrz⟩
  obtain ⟨P, hPmem, hPle⟩ := hbelow hi (fun r hr => ((hhimem r).mp hr).1) hzhi
  obtain ⟨Q, hQmem, hQle⟩ := hbelow lo (fun r hr => ((hlomem r).mp hr).1) hzlo
  have hPdim : ringKrullDim (A ⧸ P.asIdeal) = ringKrullDim A := ((hhimem _).mp hPmem).2
  have hQdim : ringKrullDim (A ⧸ Q.asIdeal) ≠ ringKrullDim A := ((hlomem _).mp hQmem).2
  have hdiff : ringKrullDim (A ⧸ P.asIdeal) ≠ ringKrullDim (A ⧸ Q.asIdeal) := by
    rw [hPdim]; exact hQdim.symm
  have hPQ : P ≠ Q := fun h => hdiff (by rw [h])
  -- Neither is equal to `z`, since the other one lies below `z` as well.
  have hstrict : ∀ {T S : PrimeSpectrum A}, T.asIdeal ∈ minimalPrimes A →
      T.asIdeal ≤ z.asIdeal → S.asIdeal ≤ z.asIdeal → T ≠ S → T < z := by
    intro T S hT hTz hSz hTS
    refine lt_of_le_of_ne hTz fun heq => hTS (PrimeSpectrum.ext ?_)
    have hST : S.asIdeal ≤ T.asIdeal := hSz.trans_eq (congrArg PrimeSpectrum.asIdeal heq).symm
    exact le_antisymm (hT.2 ⟨S.2, bot_le⟩ hST) hST
  have hPz : P < z := hstrict ((hhimem _).mp hPmem).1 hPle hQle hPQ
  have hQz : Q < z := hstrict ((hlomem _).mp hQmem).1 hQle hPle hPQ.symm
  -- Catenarity: `P ⋖ z` and `Q ⋖ z` cannot both hold, since the coheights of `P` and `Q` differ.
  have hnotcov : ¬ (P ⋖ z ∧ Q ⋖ z) := by
    rintro ⟨hPcov, hQcov⟩
    have hsat := _root_.isCatenaryRingSaturated_of_isCatenary hcat
    have hco : Order.coheight P = Order.coheight Q := by
      rw [coheight_covby_of_catenary hsat P z hPcov, coheight_covby_of_catenary hsat Q z hQcov]
    exact hdiff (by rw [← coheight_eq_ringKrullDim_quotient P,
      ← coheight_eq_ringKrullDim_quotient Q, hco])
  -- Hence there is a chain of length two below `z`, so `dim A_z ≥ 2`.
  obtain ⟨r, hr, hrz⟩ : ∃ r : PrimeSpectrum A, (P < r ∨ Q < r) ∧ r < z := by
    by_cases hPcov : P ⋖ z
    · obtain ⟨r, hQr, hrz⟩ :=
        exists_lt_lt_of_not_covBy hQz fun hQcov => hnotcov ⟨hPcov, hQcov⟩
      exact ⟨r, Or.inr hQr, hrz⟩
    · obtain ⟨r, hPr, hrz⟩ := exists_lt_lt_of_not_covBy hPz hPcov
      exact ⟨r, Or.inl hPr, hrz⟩
  have hheight : (2 : ℕ∞) ≤ Order.height z := by
    obtain ⟨s, hs⟩ : ∃ s : PrimeSpectrum A, s < r := by
      rcases hr with hPr | hQr
      · exact ⟨P, hPr⟩
      · exact ⟨Q, hQr⟩
    calc (2 : ℕ∞) ≤ Order.height s + 1 + 1 := by
          rw [add_assoc, one_add_one_eq_two]; exact le_add_self
      _ ≤ Order.height r + 1 := add_le_add (Order.height_add_one_le hs) le_rfl
      _ ≤ Order.height z := Order.height_add_one_le hrz
  -- `(S₂)` turns `dim A_z ≥ 2` into `depth A_z ≥ 2`, and Hartshorne's lemma applies.
  have hdimB : (2 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime z.asIdeal) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height z.asIdeal
      (Localization.AtPrime z.asIdeal), PrimeSpectrum.height_eq_orderHeight z]
    exact WithBot.coe_le_coe.mpr hheight
  have hdimB' : (2 : ℕ∞) ≤ (ringKrullDim (Localization.AtPrime z.asIdeal)).unbotD 0 :=
    WithBot.le_unbotD hdimB
  have hdepth : (2 : ℕ∞) ≤ Module.depth (Localization.AtPrime z.asIdeal)
      (maximalIdeal (Localization.AtPrime z.asIdeal)) (Localization.AtPrime z.asIdeal) := by
    rw [← ringDepth_eq_depth_maximalIdeal]
    exact le_trans (le_min (by norm_num) hdimB') (hS₂ z.asIdeal)
  refine not_isPreconnected_compl_closedPoint hzmin hPz hQz (finsetProd_le hi hPmem)
    (finsetProd_le lo hQmem) ?_ (Localization.AtPrime z.asIdeal)
    (Stacks.PuncturedSpectrum.isConnected_puncturedSpectrum_of_two_le_depth
      (Localization.AtPrime z.asIdeal) hdepth).2
  -- Every prime of `A` contains a minimal prime, hence contains `I` or contains `J`.
  intro x _
  obtain ⟨s, hs, hsle⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := x.asIdeal) bot_le
  by_cases hsdim : ringKrullDim (A ⧸ s) = ringKrullDim A
  · refine Or.inl ((mem_zeroLocus _ _).mp ?_)
    rw [zeroLocus_finsetProd]
    exact Set.mem_iUnion₂.mpr
      ⟨s, (hhimem s).mpr ⟨hs, hsdim⟩, (mem_zeroLocus _ _).2 hsle⟩
  · refine Or.inr ((mem_zeroLocus _ _).mp ?_)
    rw [zeroLocus_finsetProd]
    exact Set.mem_iUnion₂.mpr
      ⟨s, (hlomem s).mpr ⟨hs, hsdim⟩, (mem_zeroLocus _ _).2 hsle⟩

end Stacks.Equidimensional

end
