module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTriplePreparation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.PullbackIdealPower
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AffineSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ClosedSubschemeEquivalence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.Devissage
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.FullyFaithfulComplete

/-!
# Annihilation descends from the completion to the module, for a proper morphism

Let `A` be a Noetherian ring complete with respect to an ideal `I`, let `f : X ⟶ Spec A` be proper
and set `𝓘 = I · 𝒪_X`. If the `𝓘`-adic completion of a coherent `𝒪_X`-module `M` is killed by a
quasi-coherent ideal sheaf `𝒦` — every term `M / 𝓘 ⁿ⁺¹ M` is — then `M` itself is killed by `𝒦`.

## Main results

* `Stacks.Algebraization.idealPowerMultiple_eq_bot_of_isSystemAnnihilatedBy_completion_of_isProper`
  — the descent for a proper morphism to the spectrum of a complete Noetherian ring, with the
  hypothesis in the form `Stacks.Algebraization.IsSystemAnnihilatedBy`.

## References

* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0883](https://stacks.math.columbia.edu/tag/0883)
* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice
attribute [local instance] Stacks.Algebraization.zeroHomOfSheafOfModules

namespace Stacks.Algebraization

open Stacks.Cohomology.FormalFunctions

/-- **Annihilation descends from the completion to the module, for a proper morphism to the
spectrum of a complete Noetherian ring.** Let `A` be Noetherian and complete with respect to `I`,
let `f : X ⟶ Spec A` be proper and set `𝓘 = I · 𝒪_X`. A coherent `𝒪_X`-module whose `𝓘`-adic
completion is killed by a quasi-coherent ideal sheaf `𝒦` is killed by `𝒦`. -/
public theorem idealPowerMultiple_eq_bot_of_isSystemAnnihilatedBy_completion_of_isProper
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] (K : X.IdealSheafData) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∀ M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
      IsSystemAnnihilatedBy K
          (((completionFunctor X (baseIdealSheaf A I f)).obj M).obj) →
        idealPowerMultiple K 1 M.obj = ⊥ := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨hff⟩ := fullyFaithful_completionFunctor_of_isProper A I f
  exact fun M h => Stacks.Coherent.idealPowerMultiple_eq_bot_of_completion_eq_bot
    (baseIdealSheaf A I f) K hff M h

end Stacks.Algebraization

end
