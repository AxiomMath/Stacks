module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowUp

/-!
# Positive order on the exceptional divisor

An ideal sheaf contained in the centre of a blowup has positive order along the exceptional
divisor whenever that order is maximal. The exceptional divisor is the inverse-image ideal
sheaf `AlgebraicGeometry.exceptionalIdeal` of the centre, and the negative twists are its
powers; the order is specified by its defining inclusion together with its maximality.

## Main results

* `Stacks.Blowup.Colength.pos_order_of_le_center` — the largest exponent of the exceptional
  ideal containing the pulled-back ideal is positive.

## Implementation notes

The statement is for ideal sheaves on an arbitrary scheme: the regular local surface and the
containment between powers of its maximal ideal that the source carries are unnecessary for
positivity.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace Stacks.Blowup.Colength

/-- The maximal order of an ideal sheaf contained in the centre of a blowup is positive
along the exceptional divisor. -/
@[stacks 0AGT "positive_order"]
public theorem pos_order_of_le_center
    {X : Scheme} (M J : X.IdealSheafData) (d : ℕ)
    (hJ : J ≤ M)
    (horder :
      let E := exceptionalIdeal M
      (J.comap (blowUpToBase M) ≤ E ^ d) ∧
        (∀ e : ℕ, J.comap (blowUpToBase M) ≤ E ^ e → e ≤ d)) :
    0 < d :=
  horder.2 1 (by rw [pow_one]; exact Scheme.IdealSheafData.comap_mono (blowUpToBase M) hJ)

end Stacks.Blowup.Colength

end
