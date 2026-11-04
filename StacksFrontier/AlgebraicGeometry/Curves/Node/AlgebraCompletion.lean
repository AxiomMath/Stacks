module

public import StacksFrontier.AlgebraicGeometry.Curves.Node.Algebra
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Completion
import all StacksFrontier.AlgebraicGeometry.Curves.Node.Algebra

/-!
# Nodality is insensitive to completion

A Nagata local algebra over a field is nodal exactly when its completion at the maximal ideal
is nodal. A Noetherian local algebra over a field is nodal whenever its completion is.

## Main results

* `Stacks.Curves.isNodalAlgebra_adicCompletion_iff` — a Nagata local algebra over a field is
  nodal if and only if its completion is.
* `Stacks.Curves.isNodalAlgebra_of_isNodalAlgebra_adicCompletion` — the direction that needs no
  Nagata hypothesis.

## References

* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
* [Stacks Project, Tag 0C49](https://stacks.math.columbia.edu/tag/0C49)
* [Stacks Project, Tag 07NZ](https://stacks.math.columbia.edu/tag/07NZ)
-/

@[expose] public section

namespace Stacks.Curves

open IsLocalRing

universe u v

/-- Nodality of the completion implies nodality of the ring. -/
public theorem isNodalAlgebra_of_isNodalAlgebra_adicCompletion
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k A] (h : IsNodalAlgebra k (AdicCompletion (maximalIdeal A) A)) :
    IsNodalAlgebra k A := by
  obtain ⟨hsep, hred, hnodal⟩ := h
  refine ⟨isSeparableExtension_of_algEquiv (residueFieldAlgEquiv_adicCompletion k A).symm hsep,
    isReduced_of_isReduced_maximalIdeal_completion A hred,
    hasNodalQuadraticRelation_of_adicCompletion A hnodal⟩

/-- Nodality of the ring implies nodality of the completion, for a Nagata ring. -/
public theorem isNodalAlgebra_adicCompletion_of_isNodalAlgebra
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]
    (hA : IsNagataRing A) (h : IsNodalAlgebra k A) :
    IsNodalAlgebra k (AdicCompletion (maximalIdeal A) A) := by
  let : IsNoetherianRing A := hA.1
  obtain ⟨hsep, hred, hnodal⟩ := h
  refine ⟨isSeparableExtension_of_algEquiv (residueFieldAlgEquiv_adicCompletion k A) hsep,
    IsLocalRing.isReduced_adicCompletion_maximalIdeal_of_isNagataRing hA,
    hasNodalQuadraticRelation_adicCompletion A hnodal⟩

/-- A Nagata local algebra over a field is nodal if and only if its completion at the maximal
ideal is nodal. -/
public theorem isNodalAlgebra_adicCompletion_iff
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]
    (hA : IsNagataRing A) :
    IsNodalAlgebra k A ↔ IsNodalAlgebra k (AdicCompletion (maximalIdeal A) A) :=
  have : IsNoetherianRing A := hA.1
  ⟨isNodalAlgebra_adicCompletion_of_isNodalAlgebra k A hA,
    isNodalAlgebra_of_isNodalAlgebra_adicCompletion k A⟩

end Stacks.Curves

end
