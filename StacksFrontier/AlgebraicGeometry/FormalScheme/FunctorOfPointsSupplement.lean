module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPoints

/-!
# Monotonicity of the size bound on formal schemes

The size condition `IsSizeBoundedFormalScheme κ` on a locally topologically ringed space is
monotone in the cardinal `κ`.

## Main results

* `AlgebraicGeometry.IsSizeBoundedFormalScheme.mono`: if `X` satisfies the size condition for
  `κ` and `κ ≤ κ'`, then it satisfies the size condition for `κ'`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits

open scoped Topology

universe u

namespace TopCommRingCat

end TopCommRingCat

namespace AlgebraicGeometry

open TopologicalRing

section Spf

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

variable {P : Ideal A → Prop} [IsWeakIdealSystem A P]

end Spf

/-- Enlarging the cutoff weakens the size condition of Stacks 0AI1: the charts witnessing it
for `κ` witness it for every `κ' ≥ κ`, `Sch_κ` being contained in `Sch_κ'`. -/
theorem IsSizeBoundedFormalScheme.mono {κ κ' : Cardinal.{u}} {X : LTRS.{u}}
    (hX : IsSizeBoundedFormalScheme κ X) (hκ : κ ≤ κ') :
    IsSizeBoundedFormalScheme κ' X := fun x => by
  obtain ⟨U, hxU, A, hlin, hadm, hsize, he⟩ := hX x
  exact ⟨U, hxU, A, hlin, hadm, fun I => (hsize I).trans_le hκ, he⟩

end AlgebraicGeometry
