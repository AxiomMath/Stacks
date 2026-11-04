module

public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCriterion
public import StacksFrontier.AlgebraicGeometry.Curves.NodeDepthFittingIdealArbitraryField

/-!
# Nodal fibres of a morphism locally of finite presentation

Let `f : X ⟶ S` be locally of finite presentation and let `s ∈ S` be a point whose fibre `X_s` is
nonempty and equidimensional of dimension one. Then `X_s` has at worst nodal singularities over
the residue field `κ(s)` if and only if `X_s` is a local complete intersection over `κ(s)` and the
closed subscheme of `X_s` cut out by its relative singular ideal is unramified over `κ(s)`. This
is [Stacks, Tag 0C4E] over the field `κ(s)`, which need not be algebraically closed.

## Main results

* `Stacks.Curves.hasAtWorstNodalSingularities_fiber_iff`: [Stacks, Tag 0C4E] on the
  one-dimensional equidimensional fibres of a morphism locally of finite presentation.

## References

* [Stacks Project, Tag 0C4E](https://stacks.math.columbia.edu/tag/0C4E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.Curves

/-- **[Stacks, Tag 0C4E] on the fibres of a morphism locally of finite presentation.** Let
`f : X ⟶ S` be locally of finite presentation and `s : S` a point whose fibre is nonempty and
equidimensional of dimension one. Then the fibre has at worst nodal singularities over `κ(s)` if
and only if it is a local complete intersection over `κ(s)` and the closed subscheme cut out by
its relative singular ideal is unramified over `κ(s)`. -/
theorem hasAtWorstNodalSingularities_fiber_iff {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] :
    ∀ s : S, Nonempty (f.fiber s) → Equidimensional (f.fiber s) →
      topologicalKrullDim (f.fiber s) = (1 : WithBot ℕ∞) →
      letI : (f.fiber s).Over (Spec (.of (S.residueField s))) :=
        ⟨f.fiberToSpecResidueField s⟩
      (HasAtWorstNodalSingularities (S.residueField s) (f.fiber s) ↔
        IsLocalCompleteIntersectionOverField (f.fiberToSpecResidueField s) ∧
          Unramified ((relativeSingularIdeal (f.fiberToSpecResidueField s)).subschemeι ≫
            f.fiberToSpecResidueField s)) := by
  have : LocallyOfFiniteType f := inferInstance
  intro s _ hequi hdim
  let : (f.fiber s).Over (Spec (.of (S.residueField s))) := ⟨f.fiberToSpecResidueField s⟩
  have : LocallyOfFiniteType (f.fiber s ↘ Spec (.of (S.residueField s))) := by
    show LocallyOfFiniteType (f.fiberToSpecResidueField s)
    show LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField s))
    infer_instance
  exact hasAtWorstNodalSingularities_iff_lci_and_unramified_relativeSingularIdeal
    (S.residueField s) (f.fiber s) hequi hdim

end Stacks.Curves

end
