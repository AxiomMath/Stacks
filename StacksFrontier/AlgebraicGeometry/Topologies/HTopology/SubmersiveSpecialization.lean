module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.AlgebraicGeometry.Morphisms.Submersive
public import StacksFrontier.Topology.Specialization.Constructible

/-!
# Submersiveness produces specializations over a discrete valuation ring

A submersive morphism `g : W ⟶ S` cannot separate a point of the base from its generalizations:
if `s ∈ S` is a closed point which is not open, then some point of the fibre of `g` over `s` is
a specialization of a point of `W` lying over a *different* point of `S`. Indeed, were that not
so, the fibre over `s` would be stable under generalization; over a Noetherian `W` it is a
constructible closed set, so Stacks 0542 would make it open, and submersiveness would then make
`{s}` open.

Applied to the base change of a morphism of finite type along a map `Spec A ⟶ X` from the
spectrum of a discrete valuation ring, this is **step 4 of the proof of Stacks 0ETT (1) ⟹ (2)**:
"universal submersiveness yields a specialization `w' ⤳ w` lying over the generic and the closed
point". The Stacks proof uses it to see that the flattened family produced by the Raynaud–Gruson
blowup is surjective, and hence an fppf covering; nothing in this file depends on that blowup.

## Main results

* `AlgebraicGeometry.exists_specializes_of_submersive`: for a submersive morphism with Noetherian
  source, a point of the base which is closed but not open has a point of its fibre which is a
  specialization of a point outside that fibre.
* `AlgebraicGeometry.exists_specializes_closedPoint_of_universallySubmersive`: step 4 of the
  Stacks proof of 0ETT (1) ⟹ (2) — for a universally submersive morphism of finite type and a
  map from the spectrum of a discrete valuation ring into its target, the base change has a
  specialization whose generalization lies over the generic point and whose specialization lies
  over the closed point.

## Implementation notes

The first statement asks for `NoetherianSpace W` rather than `IsNoetherian W`: only the
topological consequence is used, through
`isOpen_of_stableUnderGeneralization_of_isConstructible` (Stacks 0542), and a closed subset of a
Noetherian space is constructible because its complement is an open compact set.

In the second statement the source of the base change is Noetherian because `Spec A` is — a
discrete valuation ring is a principal ideal domain, hence Noetherian — and the base change of
`g` is again of finite type and quasi-compact. That `Spec A` has no points besides the generic
and the closed one is `Ring.KrullDimLE.eq_bot_or_eq_top`, available because a discrete valuation
ring has Krull dimension at most one.

## References

* [Stacks Project, Tag 040H](https://stacks.math.columbia.edu/tag/040H)
* [Stacks Project, Tag 0542](https://stacks.math.columbia.edu/tag/0542)
* [Stacks Project, Tag 0CM2](https://stacks.math.columbia.edu/tag/0CM2)
* [Stacks Project, Tag 0ETT](https://stacks.math.columbia.edu/tag/0ETT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A submersive morphism cannot isolate the fibre over a non-open closed point.** If
`g : W ⟶ S` is submersive, `W` is a Noetherian scheme and `s : S` is a point whose singleton is
closed but not open, then the fibre of `g` over `s` contains a specialization of a point of `W`
which does not lie over `s`.

If it did not, that fibre would be stable under generalization. It is closed, and in a Noetherian
space a closed set is constructible — its complement is open and compact — so Stacks 0542 would
make it open; submersiveness is the statement that a subset of `S` whose preimage is open is
itself open, so `{s}` would be open. -/
theorem exists_specializes_of_submersive {W S : Scheme.{u}} {g : W ⟶ S} (hg : Submersive g)
    [NoetherianSpace W] {s : S} (hclosed : IsClosed ({s} : Set S))
    (hopen : ¬ IsOpen ({s} : Set S)) :
    ∃ w w' : W, g.base w = s ∧ g.base w' ≠ s ∧ w' ⤳ w := by
  by_contra hcon
  have hquot : Topology.IsQuotientMap g.base := (submersive_iff g).1 hg
  have _ : QuasiSeparatedSpace W := ⟨fun _ _ _ _ _ _ ↦ NoetherianSpace.isCompact _⟩
  have hfibre : IsClosed (g.base ⁻¹' {s}) := hclosed.preimage g.continuous
  have hcons : IsConstructible (g.base ⁻¹' {s}) :=
    isConstructible_compl.mp
      ((NoetherianSpace.isCompact ((g.base ⁻¹' {s})ᶜ)).isConstructible hfibre.isOpen_compl)
  have hgen : StableUnderGeneralization (g.base ⁻¹' {s}) := fun {w w'} hspec hw ↦ by
    by_contra hw'
    exact hcon ⟨w, w', hw, hw', hspec⟩
  exact hopen (hquot.isCoinducing.isOpen_preimage.mp
    (isOpen_of_stableUnderGeneralization_of_isConstructible W _ hcons hgen))

/-- **Step 4 of the proof of Stacks 0ETT (1) ⟹ (2).** Let `g : W ⟶ X` be a quasi-compact
morphism locally of finite type which is universally submersive, let `A` be a discrete valuation
ring and let `Spec A ⟶ X` be any morphism. Then the base change `W ×_X Spec A` carries a
specialization `w' ⤳ w` with `w'` over the generic point of `Spec A` and `w` over its closed
point.

The base change is submersive because `g` is universally submersive, and its source is a
Noetherian scheme because `Spec A` is one and the base change of `g` is again quasi-compact and
locally of finite type. The closed point of `Spec A` is closed, and it is not open: the generic
point specializes to it, so an open singleton would force the generic point to equal it, that is
the maximal ideal of `A` to be zero, which a discrete valuation ring forbids. So
`AlgebraicGeometry.exists_specializes_of_submersive` applies, and the point it produces outside
the closed fibre lies over the generic point because a discrete valuation ring has no primes
besides zero and its maximal ideal. -/
theorem exists_specializes_closedPoint_of_universallySubmersive {W X : Scheme.{u}} (g : W ⟶ X)
    [LocallyOfFiniteType g] [QuasiCompact g] (hg : UniversallySubmersive g) (A : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (a : Spec (CommRingCat.of A) ⟶ X) :
    ∃ w w' : (pullback g a : Scheme.{u}),
      (pullback.snd g a).base w = IsLocalRing.closedPoint A ∧
        (pullback.snd g a).base w' = genericPoint (Spec (CommRingCat.of A)) ∧ w' ⤳ w := by
  have _ : UniversallySubmersive.{u}.IsStableUnderBaseChange := by
    rw [universallySubmersive_eq]; infer_instance
  have hsub : Submersive (pullback.snd g a) :=
    submersive_of_universallySubmersive
      (MorphismProperty.of_isPullback (IsPullback.of_hasPullback g a) hg)
  have _ : IsLocallyNoetherian (pullback g a : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd g a)
  have _ : CompactSpace (pullback g a : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd g a)
  have _ : IsNoetherian (pullback g a : Scheme.{u}) := ⟨⟩
  -- the closed point of `Spec A` is closed but not open
  have hclosed : IsClosed ({IsLocalRing.closedPoint A} :
      Set (Spec (CommRingCat.of A))) := IsLocalRing.isClosed_singleton_closedPoint A
  have hnotopen : ¬ IsOpen ({IsLocalRing.closedPoint A} :
      Set (Spec (CommRingCat.of A))) := by
    intro hop
    have hmem : (⊥ : PrimeSpectrum A) ∈ ({IsLocalRing.closedPoint A} : Set _) :=
      ((PrimeSpectrum.le_iff_specializes _ _).mp bot_le).mem_open hop rfl
    exact IsDiscreteValuationRing.not_a_field A
      (congrArg PrimeSpectrum.asIdeal hmem).symm
  obtain ⟨w, w', hw, hw', hspec⟩ := exists_specializes_of_submersive hsub hclosed hnotopen
  refine ⟨w, w', hw, ?_, hspec⟩
  rcases IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top ((pullback.snd g a).base w') with h | h
  · rw [h, genericPoint_eq_bot_of_affine]
  · exact absurd h hw'

end AlgebraicGeometry

end
