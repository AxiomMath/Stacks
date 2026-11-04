module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationFromCoherence

/-!
# Coherence and finite presentation on a locally Noetherian algebraic space

A module on an algebraic space is **of finite presentation**,
`SheafOfModules.IsFinitePresentationOnSite`, when every object of the small étale site has a
covering on whose members the module is the cokernel of a map between finite coproducts of copies
of the structure sheaf (Stacks 03DL(7)). On a locally Noetherian algebraic space this is equivalent
to coherence.

## Main results

* `AlgebraicGeometry.Space.isCoherent_iff_isFinitePresentationOnSite`: a module on a locally
  Noetherian algebraic space is coherent if and only if it is of finite presentation.

## References

* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- A module on a locally Noetherian algebraic space is coherent if and only if it is an
`𝒪_F`-module of finite presentation. -/
@[stacks 07UB "conditions (1) and (3)"]
theorem isCoherent_iff_isFinitePresentationOnSite
    [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (M : Modules.{u, u} B S hS F hF) :
    IsCoherent B S hS F hF M ↔ M.IsFinitePresentationOnSite := by
  refine ⟨fun h => SheafOfModules.isFinitePresentationOnSite_of_isCoherentOnSite M
      h.toIsCoherentOnSite, fun h => ?_⟩
  let := h
  exact (isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType B S hS F hF M).2
    ⟨inferInstance,
      Stacks.SheafOfModules.presheafIsFiniteType_of_isFiniteTypeOnSite M inferInstance⟩

end AlgebraicGeometry.Space

end
