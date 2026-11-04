module

public import StacksFrontier.Homology.PseudoCoherent.Characterization
public import StacksFrontier.Homology.PseudoCoherent.Relative.Defs

@[expose] public section

/-!
# Relative pseudo-coherence of summands

Let `A` be a finite-type algebra over a commutative ring `R`. Each summand of a relatively
`m`-pseudo-coherent binary biproduct in the derived category of `A`-modules is relatively
`m`-pseudo-coherent over `R`, and likewise for relative pseudo-coherence.

## Main results

* `PseudoCoherence.isRelativelyPseudoCoherentFrom_and_isRelativelyPseudoCoherent_of_biproduct`:
  both forms of relative pseudo-coherence pass from a binary biproduct to its two summands.

## Implementation notes

Complexes are represented by objects of the derived category.

## References

* [The Stacks Project, Lemma 15.82.8 (0676)](https://stacks.math.columbia.edu/tag/0676)
-/

open CategoryTheory CategoryTheory.Limits
open StacksDraft.PseudoCoherence

namespace PseudoCoherence

universe u

attribute [local instance] HasDerivedCategory.standard

/-- Each summand of a relatively `m`-pseudo-coherent binary biproduct is
relatively `m`-pseudo-coherent, and each summand of a relatively pseudo-coherent binary
biproduct is relatively pseudo-coherent. -/
@[stacks 0676]
public theorem isRelativelyPseudoCoherentFrom_and_isRelativelyPseudoCoherent_of_biproduct
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K L : DerivedCategory (ModuleCat.{u} A)) (m : ℤ) :
    (IsRelativelyPseudoCoherentFrom (R := R) (K ⊞ L) m →
      IsRelativelyPseudoCoherentFrom (R := R) K m ∧
        IsRelativelyPseudoCoherentFrom (R := R) L m) ∧
    (IsRelativelyPseudoCoherent (R := R) (K ⊞ L) →
      IsRelativelyPseudoCoherent (R := R) K ∧
        IsRelativelyPseudoCoherent (R := R) L) := by
  have fixed (degree : ℤ) (h : IsRelativelyPseudoCoherentFrom (R := R) (K ⊞ L) degree) :
      IsRelativelyPseudoCoherentFrom (R := R) K degree ∧
        IsRelativelyPseudoCoherentFrom (R := R) L degree := by
    refine forall_and.1 fun n ↦ forall_and.1 fun f ↦ forall_and.1 fun hf ↦ ?_
    let G := (ModuleCat.restrictScalars.{u} f.toRingHom).mapDerivedCategory
    have : PreservesFiniteBiproducts G := G.preservesFiniteBiproductsOfAdditive
    have : PreservesBinaryBiproducts G := preservesBinaryBiproducts_of_preservesBiproducts G
    exact (isPseudoCoherentFrom_and_pseudoCoherent_of_biproduct _ _ degree).1
      (isPseudoCoherentFrom_of_iso (h n f hf) (G.mapBiprod K L))
  exact ⟨fixed m, fun h ↦ forall_and.1 fun degree ↦ fixed degree (h degree)⟩

end PseudoCoherence
