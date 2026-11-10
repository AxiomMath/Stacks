module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Deformation.Diagram
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Cartesian
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.UniversalHomeomorphism

/-!
# Properties preserved by an infinitesimal deformation of schemes

In a cartesian finite-order deformation diagram, the morphism `f` of closed subschemes and the
morphism `f'` of ambient schemes share every property on the list of Stacks Tag 06AG.

For the topological and separation properties this holds for an arbitrary morphism of
thickenings — no cartesian, finite-order or flatness hypothesis is needed — so the statements
are those of Stacks Tag 09ZV, recorded against this tag as well. Local finite type, local
quasi-finiteness and properness use the cartesian squares and the finite order of the base
thickening, and are the statements of Stacks Tag 09ZW read off the diagram.

## Main results

* `Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.locallyOfFiniteType_iff`
* `Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.locallyQuasiFinite_iff`
* `Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.isProper_iff`

## Implementation notes

Following Stacks Tag 01TD, local quasi-finiteness is spelled as the conjunction of Mathlib's
`AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.LocallyQuasiFinite`.

The cartesian square relating `f` and `f'` is extracted from the diagram by pasting: the source
square is cartesian over the base thickening, and factoring it through the target square
exhibits `f` as the base change of `f'` along the target thickening.

## References

* [Stacks Project, Tag 06AG](https://stacks.math.columbia.edu/tag/06AG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.Thickenings

universe u

/-- Two maps of topological spaces conjugate by homeomorphisms have homeomorphic fibres, so one
has discrete fibres exactly when the other does. -/
private theorem discreteFibers_iff_of_homeomorph
    {X X' S S' : Type*} [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace S] [TopologicalSpace S']
    (f : X → S) (f' : X' → S') (eX : X ≃ₜ X') (eS : S ≃ₜ S')
    (hcomm : ∀ x, eS (f x) = f' (eX x)) :
    (∀ y, IsDiscrete (f ⁻¹' {y})) ↔ ∀ y', IsDiscrete (f' ⁻¹' {y'}) := by
  constructor
  · intro h y'
    convert (h (eS.symm y')).preimage eX.symm.continuous.continuousOn eX.symm.injective using 1
    ext x
    simpa [Homeomorph.coe_toEquiv, Homeomorph.coe_symm_toEquiv, hcomm] using
      (eS.toEquiv.eq_symm_apply (x := y') (y := f (eX.symm x))).symm
  · intro h y
    convert (h (eS y)).preimage eX.continuous.continuousOn eX.injective using 1
    ext x
    simp [← hcomm x, eS.injective.eq_iff]

namespace CartesianFiniteOrderDeformationDiagram

/-- Local finite type is invariant under a cartesian finite-order deformation. -/
@[stacks 06AG "locally_finite_type"]
theorem locallyOfFiniteType_iff (D : CartesianFiniteOrderDeformationDiagram.{u}) :
    LocallyOfFiniteType D.f ↔ LocallyOfFiniteType D.f' :=
  locallyOfFiniteType_iff_of_isFiniteOrderThickening
    D.iX D.iY D.f D.f'
    (isFiniteOrderThickening_isStableUnderBaseChange.of_isPullback
      D.Y_cartesian.flip D.iS_finiteOrder)
    (IsPullback.of_bot
      (by simpa only [D.f_over_S, D.f'_over_S'] using D.X_cartesian)
      D.f_thickening_comm.symm D.Y_cartesian)

/-- Local quasi-finiteness is invariant under a cartesian finite-order deformation with flat
enlarged source. -/
@[stacks 06AG "locally_quasi_finite"]
theorem locallyQuasiFinite_iff (D : CartesianFiniteOrderDeformationDiagram.{u}) :
    (LocallyOfFiniteType D.f ∧ LocallyQuasiFinite D.f) ↔
      (LocallyOfFiniteType D.f' ∧ LocallyQuasiFinite D.f') := by
  let hX' := (show IsHomeomorph D.iX from MorphismProperty.universally_le _ _
    (IsThickening.universalHomeomorphism D.iX_thickening).universally_isHomeomorph).homeomorph
  let hY' := (show IsHomeomorph D.iY from MorphismProperty.universally_le _ _
    (IsThickening.universalHomeomorphism D.iY_thickening).universally_isHomeomorph).homeomorph
  have hcomm (x : D.X) : hY' (D.f x) = D.f' (hX' x) := by
    change D.iY (D.f x) = D.f' (D.iX x)
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun g : D.X ⟶ D.Y' => g x) D.f_thickening_comm
  have hfib := discreteFibers_iff_of_homeomorph D.f D.f' hX' hY' hcomm
  have hft := locallyOfFiniteType_iff D
  constructor
  · rintro ⟨_, hqff⟩
    have := hft.mp ‹_›
    exact ⟨this, (locallyQuasiFinite_iff_isDiscrete_preimage_singleton (f := D.f')).2
      (hfib.mp ((locallyQuasiFinite_iff_isDiscrete_preimage_singleton (f := D.f)).1 hqff))⟩
  · rintro ⟨_, hqff'⟩
    have := hft.mpr ‹_›
    exact ⟨this, (locallyQuasiFinite_iff_isDiscrete_preimage_singleton (f := D.f)).2
      (hfib.mpr ((locallyQuasiFinite_iff_isDiscrete_preimage_singleton (f := D.f')).1 hqff'))⟩

/-- Properness is invariant under a cartesian finite-order deformation. -/
@[stacks 06AG "proper"]
theorem isProper_iff (d : CartesianFiniteOrderDeformationDiagram.{u}) :
    IsProper d.f ↔ IsProper d.f' := by
  let φ : Arrow.mk d.iX ⟶ Arrow.mk d.iY := Arrow.homMk d.f d.f' d.f_thickening_comm
  have hsep : IsSeparated d.f ↔ IsSeparated d.f' :=
    isSeparated_left_iff_right d.iX_thickening d.iY_thickening φ
  have huc : UniversallyClosed d.f ↔ UniversallyClosed d.f' :=
    universallyClosed_left_iff_right φ d.iX_thickening d.iY_thickening
  rw [AlgebraicGeometry.isProper_iff, AlgebraicGeometry.isProper_iff, hsep, huc,
    locallyOfFiniteType_iff d]

end CartesianFiniteOrderDeformationDiagram

end Stacks.Thickenings

add_to_stacks 06AG "quasi_compact" Stacks.Thickenings.quasiCompact_left_iff_right
add_to_stacks 06AG "separated" Stacks.Thickenings.isSeparated_left_iff_right
add_to_stacks 06AG "separated" Stacks.Thickenings.quasiSeparated_left_iff_right
add_to_stacks 06AG "surjective" Stacks.Thickenings.surjective_left_iff_right
add_to_stacks 06AG "universally_closed" Stacks.Thickenings.universallyClosed_left_iff_right
add_to_stacks 06AG "universally_injective" Stacks.Thickenings.universallyInjective_left_iff_right
add_to_stacks 06AG "universally_open" Stacks.Thickenings.universallyOpen_left_iff_right

end
