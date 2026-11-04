module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.StructureSheafStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.WeaklyAssociated
public import StacksCore.Tactic.StacksAttribute

/-!
# Weakly associated points of a reduced scheme

The weakly associated points of a reduced scheme are precisely the generic points of its
irreducible components.

## Main results

* `AlgebraicGeometry.weaklyAssociatedPointsOfScheme_eq_genericPoints` identifies the weakly
  associated points of a reduced scheme with `AlgebraicGeometry.genericPoints`.

## Implementation notes

`AlgebraicGeometry.genericPoints X` is Mathlib's set of generic points of the irreducible
components of `X`. Both sides are computed pointwise: at a point of a reduced scheme the local
ring is a field exactly when the point is generic in a component, and the weakly associated
primes of a reduced ring are its minimal primes (Stacks tag 0EMA), which over a local ring
means the maximal ideal is the only prime.

The stalk of the structure sheaf, viewed as a module over itself, is identified with the local
ring by `AlgebraicGeometry.structureSheafStalkLinearEquiv`.

## References

* [Stacks Project, Tag 0EME](https://stacks.math.columbia.edu/tag/0EME)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- On a reduced scheme a point is generic in an irreducible component exactly when its local
ring is a field. -/
@[ega "IV 20.1.3.1" "partial", ega "IV 5.8.4" "special case", sga "3 VIA 2.5.4" "partial"]
private lemma mem_genericPoints_iff_isField_stalk (X : Scheme.{u}) [IsReduced X] (x : X) :
    x ∈ genericPoints X ↔ IsField (X.presheaf.stalk x) := by
  refine ⟨fun hx => isField_stalk_of_closure_mem_irreducibleComponents X x hx, fun hx => ?_⟩
  have : Subsingleton (Spec (X.presheaf.stalk x)) :=
    PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mpr hx
  have hmin : ∀ y : X, y ⤳ x → y = x := by
    intro y hy
    obtain ⟨z, rfl⟩ : y ∈ Set.range (X.fromSpecStalk x) := by rwa [Scheme.range_fromSpecStalk]
    rw [Subsingleton.elim z (IsLocalRing.closedPoint _), Scheme.fromSpecStalk_closedPoint]
  let C : irreducibleComponents X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  let η : genericPoints X := genericPoints.ofComponent C
  have hηx : η.1 ⤳ x := specializes_iff_mem_closure.mpr <|
    (genericPoints.isGenericPoint_ofComponent C).symm ▸ mem_irreducibleComponent
  simpa [hmin η.1 hηx] using η.2

/-- **Stacks Project, Tag 0EME.** The weakly associated points of a reduced scheme are exactly
the generic points of its irreducible components. -/
@[stacks 0EME]
theorem weaklyAssociatedPointsOfScheme_eq_genericPoints (X : Scheme.{u}) [IsReduced X] :
    Stacks.Divisors.schemeWeaklyAssociatedPoints X = genericPoints X := by
  ext x
  rw [Stacks.Divisors.mem_schemeWeaklyAssociatedPoints_iff, mem_genericPoints_iff_isField_stalk]
  rw [show Stacks.Divisors.IsWeaklyAssociatedPoint (SheafOfModules.unit X.ringCatSheaf) x ↔
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
        weaklyAssociatedPrimes (X.presheaf.stalk x) (X.presheaf.stalk x) from
    LinearEquiv.isWeaklyAssociatedPrime_iff (structureSheafStalkLinearEquiv X x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)), weakAss_eq_minimalPrimes0EMA]
  constructor
  · intro hm
    rw [← PrimeSpectrum.subsingleton_iff_isField_of_isReduced]
    refine ⟨fun p q => PrimeSpectrum.ext ?_⟩
    have h (p : PrimeSpectrum (X.presheaf.stalk x)) :
        p.asIdeal = IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
      le_antisymm (IsLocalRing.le_maximalIdeal p.2.ne_top)
        (hm.2 ⟨p.2, bot_le⟩ (IsLocalRing.le_maximalIdeal p.2.ne_top))
    exact (h p).trans (h q).symm
  · intro hf
    have hs : Subsingleton (PrimeSpectrum (X.presheaf.stalk x)) :=
      PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mpr hf
    exact ⟨⟨inferInstance, bot_le⟩, fun q hq _ ↦ (congrArg PrimeSpectrum.asIdeal
      (Subsingleton.elim (⟨q, hq.1⟩ : PrimeSpectrum _) (IsLocalRing.closedPoint _))).symm.le⟩

end AlgebraicGeometry
