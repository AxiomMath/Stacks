module

public import StacksFrontier.Algebra.Homology.PseudoCoherentNakayamaModels
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularAnyModel
public import StacksFrontier.Homology.PseudoCoherent.Coherent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pseudo-coherence over a Noetherian ring in any derived-category model

Over a Noetherian ring `R`, an object of `D(R)` which is bounded above and all of whose
cohomology modules are finite is pseudo-coherent, [Stacks, Tag 066E].  The library proves this
at the standard model of the derived category
(`StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology`); this file
transports it to an arbitrary chosen model, in the form of
`StacksDraft.PseudoCoherence.IsPseudoCoherentIn`.  The comparison equivalence to the standard
model carries pseudo-coherence
(`StacksDraft.PseudoCoherence.isPseudoCoherentIn_iff_isPseudoCoherent`) and identifies the
cohomology functors (`StacksDraft.DerivedModel.modelEquivCompHomologyFunctorIso`).

## Main results

* `StacksDraft.PseudoCoherence.isPseudoCoherentIn_iff_boundedAbove_finite_homology` — over a
  Noetherian ring, in any model, pseudo-coherence is equivalent to being bounded above with finite
  cohomology modules.
* `StacksDraft.PseudoCoherence.isPseudoCoherentIn_of_boundedAbove_finite_homology` — the
  direction used.

## References

* [Stacks Project, Tag 066E](https://stacks.math.columbia.edu/tag/066E)
* [Stacks Project, Tag 064T](https://stacks.math.columbia.edu/tag/064T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w'

namespace StacksDraft.PseudoCoherence

open StacksDraft.DerivedModel

/-- **[Stacks, Tag 066E] in any model of the derived category.**  Over a Noetherian ring `R`, an
object `K` of a chosen model of `D(R)` is pseudo-coherent exactly when it is bounded above and all
its cohomology modules are finite `R`-modules. -/
@[sga "6 I 5.0" "more general"]
theorem isPseudoCoherentIn_iff_boundedAbove_finite_homology {R : Type u} [Ring R]
    [IsNoetherianRing R] [Small.{v} R] [h : HasDerivedCategory.{w'} (ModuleCat.{v} R)]
    (K : DerivedCategory (ModuleCat.{v} R)) :
    IsPseudoCoherentIn K ↔
      (∃ b : ℤ, ∀ i : ℤ, b < i →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) ∧
      ∀ i : ℤ, Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K) := by
  let e := fun i : ℤ ↦ (modelEquivCompHomologyFunctorIso h
    (HasDerivedCategory.standard (ModuleCat.{v} R)) i).app K
  refine (isPseudoCoherentIn_iff_isPseudoCoherent K (HasDerivedCategory.standard _)).trans
    ((pseudoCoherent_iff_boundedAbove_finite_homology
      ((modelEquiv h (HasDerivedCategory.standard (ModuleCat.{v} R))).functor.obj K) 0
      PUnit.{v + 1}).2.1.trans ?_)
  exact and_congr (exists_congr fun b ↦ forall₂_congr fun i _ ↦ (e i).isZero_iff)
    (forall_congr' fun i ↦ Module.Finite.equiv_iff (e i).toLinearEquiv)

/-- **Over a Noetherian ring, in any model of the derived category, an object which is bounded
above and has finite cohomology modules is pseudo-coherent**, [Stacks, Tag 066E]. -/
@[sga "6 I 5.0" "more general"]
theorem isPseudoCoherentIn_of_boundedAbove_finite_homology {R : Type u} [Ring R]
    [IsNoetherianRing R] [Small.{v} R] [HasDerivedCategory.{w'} (ModuleCat.{v} R)]
    (K : DerivedCategory (ModuleCat.{v} R))
    (hb : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K))
    (hf : ∀ i : ℤ, Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) :
    IsPseudoCoherentIn K :=
  (isPseudoCoherentIn_iff_boundedAbove_finite_homology K).2 ⟨hb, hf⟩

end StacksDraft.PseudoCoherence
