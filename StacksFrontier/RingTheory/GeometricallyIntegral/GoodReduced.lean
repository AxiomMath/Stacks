module

public import StacksFrontier.RingTheory.GeometricallyIntegral.SpreadOut

/-!
# The good half of the generic-fibre dichotomy is constructibility of the locus

`StacksFrontier.RingTheory.GeometricallyIntegral.SpreadOut` reduces Stacks 05FT to two statements
about a single generic fibre, the *good halves* of the dichotomy of Stacks 0577/0578 and of
Stacks 055A: over a Noetherian domain `D` with a finite type algebra `T`, if the generic fibre is
geometrically reduced (respectively geometrically irreducible) then some nonempty basic open of
`Spec D` is contained in `Algebra.geometricallyReducedFibreLocus D T` (respectively in
`Algebra.geometricallyIrreducibleFibreLocus D T`). The *bad* halves, where the generic fibre fails
the property, are proved there unconditionally.

A natural hope is that the good half is a formal consequence of the bad one: a constructible
subset of an irreducible space either contains a nonempty open or is not dense, so if the locus
were known to be constructible then the good half would follow from
`PrimeSpectrum.exists_ne_zero_basicOpen_subset_of_isConstructible`, the generic point of `Spec D`
belonging to every nonempty basic open. **This file shows that the hope is exactly circular.**
Constructibility of the locus is what the good half is *for*: it is derived from the two halves of
the dichotomy in `Algebra.isConstructible_fibreLocus`, through the criterion of Stacks 053Z, and
granted the bad half it is *equivalent* to the good half. So no amount of work with constructible
sets can produce the good half, and the remaining gap in Stacks 05FT is not an artifact of the
route this library takes through Stacks 053Z: the affine case of Stacks 0578 at the generic point
and the affine case of Stacks 0579 are, modulo the proved Stacks 0577, the same theorem.

## Main results

* `Algebra.exists_basicOpen_subset_fibreLocus_iff_isConstructible`: **the equivalence**, for an
  arbitrary iso-invariant property `P` of rings whose bad half is known. The good half of the
  generic-fibre dichotomy for `Algebra.fibreLocus _ _ P` over all Noetherian domains holds if and
  only if `Algebra.fibreLocus _ _ P` is constructible over all Noetherian rings.
* `Algebra.exists_basicOpen_subset_geometricallyReducedFibreLocus_iff_isConstructible`: that
  equivalence at `P = IsReduced`, whose bad half is the affine case of Stacks 0577 at the generic
  point and is proved in `StacksFrontier.RingTheory.GeometricallyIntegral.SpreadOut`. The two sides
  are the affine case of Stacks 0578 at the generic point and the affine case of Stacks 0579.
* `Algebra.mem_fibreLocus_bot_iff`: membership of the generic point in a fibre locus is the
  condition on the generic fibre that the bad half already uses, namely that `P (T ⊗[D] K)` holds
  for every field `K` into which `D` embeds.

## Implementation notes

The equivalence is stated as an `Iff` between two universally quantified statements rather than as
two implications, because that is the form in which it answers the question: the two sides are
interchangeable as hypotheses of `Algebra.projective_of_geometricallyIntegral_fibres_of_spreadOut`.
The forward implication needs the bad half (it is
`Algebra.isConstructible_geometricallyReducedFibreLocus_of_goodGeneric` in the reduced case); the
backward implication needs nothing at all beyond the generic point of the spectrum of a domain
lying in every nonempty basic open.

Only the direction "constructible implies good" is unconditional in `P`, and it is the direction
that disposes of the hope described above. The quantifier over all Noetherian domains cannot be
dropped from the left-hand side: Stacks 053Z is applied at the quotients `A ⧸ p`, so a single base
is not enough.

Nothing here carries a `@[stacks 0578]` or `@[stacks 0579]` attribute: what this file proves is
that the two affine statements are equivalent, not either of them. Both affine cases are proved in
`StacksFrontier.RingTheory.GeometricallyIntegral.ReducedFibreFromSmoothLocus`, by the argument of
the source through the smooth locus rather than through constructible sets — which is exactly
what the equivalence below says is unavoidable; the tags stay off there as well, both source
statements being about arbitrary morphisms of schemes. Those scheme-level statements are proved
in `StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibre.OpenLocus`, and that is where the
two tags sit:
`AlgebraicGeometry.exists_opens_nonempty_geometricallyReduced_morphismRestrict_of_finiteType`
carries `@[stacks 0578]` and
`AlgebraicGeometry.isLocallyConstructible_geometricallyReduced_fiber` carries `@[stacks 0579]`.

## References

* [Stacks Project, Tag 0578](https://stacks.math.columbia.edu/tag/0578)
* [Stacks Project, Tag 0579](https://stacks.math.columbia.edu/tag/0579)
* [Stacks Project, Tag 0577](https://stacks.math.columbia.edu/tag/0577)
* [Stacks Project, Tag 053Z](https://stacks.math.columbia.edu/tag/053Z)
* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
-/

@[expose] public section

open PrimeSpectrum Topology

open scoped TensorProduct

universe u

namespace Algebra

/-- **The generic point of a fibre locus, unfolded.** Over a domain `D` the generic point `(0)` of
`Spec D` lies in the fibre locus of a property `P` exactly when `P (T ⊗[D] K)` holds for every
field `K` over `D` into which `D` embeds, the condition `ker (D → K) = (0)` being injectivity of
`D → K`.

This is the hypothesis of the good half of the generic-fibre dichotomy, and it is the same
condition that the bad half negates in
`Algebra.exists_ne_zero_disjoint_geometricallyReducedFibreLocus`. -/
theorem mem_fibreLocus_bot_iff {D T : Type u} [CommRing D] [CommRing T] [Algebra D T]
    {P : ∀ (R : Type u) [CommRing R], Prop} (hbot : (⊥ : Ideal D).IsPrime) :
    (⟨⊥, hbot⟩ : PrimeSpectrum D) ∈ fibreLocus D T P ↔
      ∀ (K : Type u) [Field K] [Algebra D K], Function.Injective (algebraMap D K) →
        P (T ⊗[D] K) :=
  ⟨fun h K _ _ hinj => h K ((RingHom.injective_iff_ker_eq_bot _).mp hinj),
    fun h K _ _ hker => h K ((RingHom.injective_iff_ker_eq_bot _).mpr hker)⟩

/-- **The good half of the generic-fibre dichotomy is constructibility of the locus.** Let `P` be a
property of rings invariant under ring isomorphism whose *bad* half is known: whenever the generic
fibre of a finite type algebra over a Noetherian domain fails `P`, some nonempty basic open of the
base misses the fibre locus. Then the *good* half — a generic fibre satisfying `P` forces a
nonempty basic open inside the fibre locus — holds for all Noetherian domains if and only if the
fibre locus of a finite type algebra over a Noetherian ring is always constructible.

The forward implication is the criterion of Stacks 053Z, `Algebra.isConstructible_fibreLocus`,
whose hypothesis is the full dichotomy: the generic point either lies in the locus, where the good
half applies, or does not, where the bad half does.

The backward implication is the observation that makes the forward one circular. Over a domain the
zero ideal is prime and lies in every nonempty basic open, so a constructible locus containing it
contains a nonempty basic open, by
`PrimeSpectrum.exists_ne_zero_basicOpen_subset_of_isConstructible`. Constructibility of the locus
is therefore not a tool for proving the good half but a restatement of it. -/
theorem exists_basicOpen_subset_fibreLocus_iff_isConstructible
    {P : ∀ (R : Type u) [CommRing R], Prop}
    (hP : ∀ (R S : Type u) [CommRing R] [CommRing S], (R ≃+* S) → (P R ↔ P S))
    (hbad : ∀ (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T]
      [Algebra D T] [Algebra.FiniteType D T],
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∉ fibreLocus D T P →
        ∃ f : D, f ≠ 0 ∧
          Disjoint (basicOpen f : Set (PrimeSpectrum D)) (fibreLocus D T P)) :
    (∀ (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T] [Algebra D T]
        [Algebra.FiniteType D T],
        (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ fibreLocus D T P →
          ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆ fibreLocus D T P) ↔
      ∀ (A C : Type u) [CommRing A] [IsNoetherianRing A] [CommRing C] [Algebra A C]
        [Algebra.FiniteType A C], IsConstructible (fibreLocus A C P) := by
  constructor
  · intro hgood A C _ _ _ _ _
    refine isConstructible_fibreLocus hP (fun D T _ _ _ _ _ _ => ?_) A C
    by_cases hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ fibreLocus D T P
    · exact (hgood D T hgen).imp fun _ h => ⟨h.1, .inl h.2⟩
    · exact (hbad D T hgen).imp fun _ h => ⟨h.1, .inr h.2⟩
  · exact fun hconstr D T _ _ _ _ _ _ hgen =>
      exists_ne_zero_basicOpen_subset_of_isConstructible (hconstr D T) hgen

/-- **The affine case of Stacks 0578 at the generic point is the affine case of Stacks 0579.** The
good half of the generic-fibre dichotomy for geometric reducedness — over a Noetherian domain `D`
with a finite type algebra `T`, a geometrically reduced generic fibre forces a nonempty basic open
of `Spec D` inside `Algebra.geometricallyReducedFibreLocus D T` — holds for all Noetherian domains
if and only if that locus is constructible over every Noetherian ring.

This is `Algebra.exists_basicOpen_subset_fibreLocus_iff_isConstructible` at `P = IsReduced`, whose
bad half is `Algebra.exists_ne_zero_disjoint_geometricallyReducedFibreLocus`, the affine case of
Stacks 0577 at the generic point. The left-hand side is the affine case of Stacks 0578 at the
generic point and the right-hand side the affine case of Stacks 0579; the equivalence says that
proving the first via constructible sets is circular, and that neither is weaker than the other. -/
theorem exists_basicOpen_subset_geometricallyReducedFibreLocus_iff_isConstructible :
    (∀ (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T] [Algebra D T]
        [Algebra.FiniteType D T],
        (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyReducedFibreLocus D T →
          ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
            geometricallyReducedFibreLocus D T) ↔
      ∀ (A C : Type u) [CommRing A] [IsNoetherianRing A] [CommRing C] [Algebra A C]
        [Algebra.FiniteType A C], IsConstructible (geometricallyReducedFibreLocus A C) :=
  exists_basicOpen_subset_fibreLocus_iff_isConstructible (fun _ _ _ _ e => isReduced_congr e)
    fun _ _ _ _ _ _ _ _ hgen => exists_ne_zero_disjoint_geometricallyReducedFibreLocus hgen

end Algebra

end
