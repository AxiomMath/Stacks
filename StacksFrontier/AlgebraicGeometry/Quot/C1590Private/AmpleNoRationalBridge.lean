module

public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.AmpleNoRationalTail
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.DualizingSheafPullback
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.BaseChangeUnion
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleCurve.Basic

/-!
# A nodal curve with ample dualizing sheaf has no rational bridge

Let `X` be a proper scheme of dimension one over a field `k` with `H⁰(X, 𝒪_X) = k` and
at-worst-nodal singularities. If `ω_X` is ample, then `X` has no rational bridge: on a rational
bridge `C` the dualizing sheaf is trivial (Stacks 0E64, 0C6M), so it has degree zero there, while
the pullback of an ample invertible module along the affine morphism `C ⟶ X` has positive degree
(Stacks 0B40).

This is the half of Stacks 0E3P for rational bridges, in the converse direction.

## Main results

* `AlgebraicGeometry.C1590Private.not_isRationalBridge_of_isAmple_dualizingSheafOverField`.

## References

* [Stacks Project, Tag 0E3P](https://stacks.math.columbia.edu/tag/0E3P)
* [Stacks Project, Tag 0E64](https://stacks.math.columbia.edu/tag/0E64)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.C1590Private

universe u

/-- **A nodal curve with ample dualizing sheaf has no rational bridge.** -/
theorem not_isRationalBridge_of_isAmple_dualizingSheafOverField (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))]
    (hL : Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))))
    (C : X.IdealSheafData) : ¬ IsRationalBridge k X C := by
  intro hC
  have : IsIntegral C.subscheme := hC.fst
  have hCdim := Stacks.Curves.topologicalKrullDim_subscheme_eq_one_of_isRationalBridge k X hdim hC
  obtain ⟨e⟩ := nonempty_pullback_dualizingSheafOverField_iso_unit_of_isRationalBridge hdim
    hnodal C hC
  let fC : C.subscheme ⟶ Spec (.of k) := C.subschemeι ≫ (X ↘ Spec (.of k))
  have hpos := invertibleCurveDegree_pullback_pos_of_isAmple_of_isAffineHom k fC hCdim
    C.subschemeι _ hL
  let : SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback C.subschemeι).obj
        (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) :=
    Stacks.Modules.isInvertible_pullback C.subschemeι _
  rw [invertibleCurveDegree_eq_of_iso k fC hCdim.le e,
    invertibleCurveDegree_unit_eq_zero k fC hCdim.le] at hpos
  exact lt_irrefl 0 hpos

end AlgebraicGeometry.C1590Private

end
