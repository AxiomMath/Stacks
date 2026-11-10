module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.CohenMacaulayDimensionFormula
public import StacksFrontier.RingTheory.Smooth.RegularRing

/-!
# The dimension formula for a smooth morphism

For a smooth morphism of locally Noetherian schemes the dimension of the source at a point is the
dimension of the target at its image plus the dimension of the fibre at that point:
`dim_x(X) = dim_{f x}(Y) + dim_x(X_{f x})`.

The proof is the source's. A smooth morphism is flat and locally of finite presentation, and its
fibres are smooth over a field, hence regular and therefore Cohen-Macaulay; so the source is cut
into open pieces on which the fibre dimension is a constant `d` (Tag 02NM), and on such a piece
the formula is the dimension formula for a flat morphism of relative dimension `d` (Tag 0AFE).
Both steps are packaged by the Cohen-Macaulay dimension formula of Tag 0AFG, which this file
specializes.

## Main results

* `AlgebraicGeometry.isCohenMacaulay_fiber_of_smooth`: the fibres of a smooth morphism are
  Cohen-Macaulay.
* `AlgebraicGeometry.topologicalKrullDimAt_eq_add_topologicalKrullDimAt_fiber_of_smooth` is
  **Stacks Tag 0AFF**: the local dimension formula for a smooth morphism.

## Implementation notes

The fibre dimension at `x` is the local topological Krull dimension of the scheme-theoretic fibre
`f.fiber (f x)` at the point `f.asFiber x`, matching the spelling of Tags 0AFE and 0AFG; all three
dimensions take values in `WithBot ℕ∞`.

Cohen-Macaulayness of the fibres is obtained ring-theoretically: on an affine chart of a scheme
smooth over a field the ring of sections is smooth over that field, hence regular by
`Algebra.isRegularRing_of_smooth`, and a regular local ring is Cohen-Macaulay.

## References

* [Stacks Project, Tag 0AFF](https://stacks.math.columbia.edu/tag/0AFF)
* [Stacks Project, Tag 0AFG](https://stacks.math.columbia.edu/tag/0AFG)
* [Stacks Project, Tag 0AFE](https://stacks.math.columbia.edu/tag/0AFE)
* [Stacks Project, Tag 02NM](https://stacks.math.columbia.edu/tag/02NM)
* [Stacks Project, Tag 07NF](https://stacks.math.columbia.edu/tag/07NF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A scheme smooth over a field is Cohen-Macaulay: on an affine chart its ring of sections is a
smooth algebra over the field, hence regular, and a regular local ring is Cohen-Macaulay. -/
@[ega "IV 17.5.8" "(ii), special case"]
private theorem isCohenMacaulay_of_smooth_over_field {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [Smooth p] : IsCohenMacaulay X := by
  rw [isCohenMacaulay_iff]
  intro x
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  let A := Γ(Spec (.of k), ⊤)
  let B := Γ(X, U)
  let e : A ≃+* k := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
  let : IsRegularRing A := IsRegularRing.of_ringEquiv e.symm
  let : Algebra A B := (p.appLE ⊤ U le_top).hom.toAlgebra
  let : Algebra.Smooth A B := p.smooth_appLE (isAffineOpen_top _) hU le_top
  let : IsRegularRing B := Algebra.isRegularRing_of_smooth A B
  refine ⟨⟨U, hU⟩, hx, inferInstance, ?_⟩
  rw [isCohenMacaulayRing_iff]
  intro q _
  let R := Localization.AtPrime q
  have hne : IsLocalRing.maximalIdeal R • (⊤ : Submodule R R) ≠ ⊤ := by
    simpa using (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  have hd : localRingDepth R = Module.depth R (IsLocalRing.maximalIdeal R) R := by
    rw [localRingDepth, Module.depth, ite_eq_right hne]
    exact le_antisymm (iSup_le fun s => le_iSup₂_of_le s.val s.property le_rfl)
      (iSup_le fun rs => iSup_le fun hrs => le_iSup_of_le ⟨rs, hrs⟩ le_rfl)
  change (localRingDepth R : WithBot ℕ∞) = ringKrullDim R
  rw [hd]
  exact_mod_cast
    (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay R).2

/-- Every scheme-theoretic fibre of a smooth morphism is Cohen-Macaulay, being smooth over the
residue field of its base point. -/
public theorem isCohenMacaulay_fiber_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (y : Y) : IsCohenMacaulay (f.fiber y) :=
  have hf : Smooth (f.fiberToSpecResidueField y) :=
    inferInstanceAs (Smooth (pullback.snd f (Y.fromSpecResidueField y)))
  @isCohenMacaulay_of_smooth_over_field (Y.residueField y) _ (f.fiber y)
    (f.fiberToSpecResidueField y) hf

/-- **Stacks Project, Tag 0AFF.** For a smooth morphism of locally Noetherian schemes the
dimension of the source at a point is the dimension of the target at its image plus the dimension
of the fibre at that point. -/
@[stacks 0AFF]
public theorem topologicalKrullDimAt_eq_add_topologicalKrullDimAt_fiber_of_smooth
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) [Smooth f]
    (x : X) :
    topologicalKrullDimAt X x =
      topologicalKrullDimAt Y (f x) +
        topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) :=
  topologicalKrullDimAt_eq_add_topologicalKrullDimAt_fiber f
    (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f)
    ((isCohenMacaulay_iff_flat_and_fibers f
        (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f)).mpr
      ⟨inferInstance, isCohenMacaulay_fiber_of_smooth f⟩) x

end AlgebraicGeometry

end
