module

public import StacksFrontier.Homology.PseudoCoherent.Relative.Noetherian
public import StacksFrontier.RingTheory.PseudoCoherentMap.Defs
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Finite-type ring maps out of a Noetherian ring

A finite-type algebra over a Noetherian commutative ring is a pseudo-coherent ring map.

## Main results

* `Algebra.PseudoCoherent.of_finiteType` (Stacks 067I).

## Implementation notes

The source states the result for a map of Noetherian rings; only the source needs to be
Noetherian, since a finite-type algebra over a Noetherian ring is Noetherian again. The proof is
the module case of Stacks 067F: over a Noetherian base, relative pseudo-coherence of an
`A`-module is its finiteness, and `B` is finite over itself.

## References

* [The Stacks Project, Lemma 15.83.2 (067I)](https://stacks.math.columbia.edu/tag/067I)
-/

open CategoryTheory

namespace Algebra.PseudoCoherent

universe u

/-- **Stacks 067I.** A finite-type ring map whose source is Noetherian is pseudo-coherent. -/
@[stacks 067I, sga "6 III 1.3" "third example, affine"]
public theorem of_finiteType
    (A : Type u) (B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FiniteType A B] :
    Algebra.PseudoCoherent A B := by
  let : HasDerivedCategory (ModuleCat.{u} B) := HasDerivedCategory.standard _
  exact Algebra.pseudoCoherent_iff_isModuleRelativelyPseudoCoherent.mpr
    ((PseudoCoherence.relativePseudoCoherent_iff_boundedAbove_finite_homology (R := A) (A := B)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)) 0 B).2.2.2
      inferInstance)

end Algebra.PseudoCoherent
