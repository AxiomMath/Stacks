module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.StandardChart
public import StacksFrontier.RingTheory.Blowup.Basic

/-!
# Reducedness of a blowup

A blowup inherits reducedness from the scheme it blows up. This is read off the standard affine
charts `Spec Γ(X, U)[I(U)/a]`: the affine blowup algebra is a subring of a localization of
`Γ(X, U)`, so it is reduced whenever `Γ(X, U)` is.

## Main results

* `AlgebraicGeometry.isReduced_blowUpAffineChartRing`: the affine blowup algebra of a reduced
  ring is reduced.
* `AlgebraicGeometry.isReduced_blowUp`: **Stacks Tag 0808.**

## Implementation notes

Reducedness is local on the cover of Stacks tag 0804,
`AlgebraicGeometry.blowUpAffineChartCover`.

## References

* [Stacks Project, Tag 0808](https://stacks.math.columbia.edu/tag/0808)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The affine blowup algebra of a reduced ring is reduced: it is a subring of a localization
of that ring, and a localization of a reduced ring is reduced. -/
theorem isReduced_blowUpAffineChartRing (U : X.affineOpens) (a : I.ideal U)
    [_root_.IsReduced (X.presheaf.obj (.op U.1))] :
    _root_.IsReduced (blowUpAffineChartRing I U a) := by
  have : _root_.IsReduced (Localization.Away (a : X.presheaf.obj (.op U.1))) := inferInstance
  rw [isReduced_iff_forall_pow_eq_zero]
  intro z n hn hzn
  exact Subtype.ext ((isReduced_iff_forall_pow_eq_zero.mp inferInstance) z.1 n hn
    (congrArg Subtype.val hzn))

/-- **Stacks Project, Tag 0808.** The blowup of a reduced scheme in a quasi-coherent ideal is
reduced. -/
@[stacks 0808, instance]
theorem isReduced_blowUp [IsReduced X] : IsReduced (blowUp I) := by
  rw [IsReduced.iff_of_openCover _ (blowUpAffineChartCover I)]
  intro j
  have hU : _root_.IsReduced (X.presheaf.obj (.op j.1.1)) :=
    (affine_isReduced_iff (.of (X.presheaf.obj (.op j.1.1)))).mp
      (isReduced_of_isOpenImmersion j.1.2.isoSpec.inv)
  exact (affine_isReduced_iff (.of (blowUpAffineChartRing I j.1 j.2))).mpr
    (isReduced_blowUpAffineChartRing I j.1 j.2)

end AlgebraicGeometry

end
