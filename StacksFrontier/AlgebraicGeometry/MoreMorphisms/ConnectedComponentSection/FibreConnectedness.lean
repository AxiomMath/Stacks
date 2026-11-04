module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.MultisectionPullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Section
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedPoint

/-!
# Geometric connectedness of the fibres met by a section

Tag 057I has to transport geometric connectedness between the fibres of a morphism, the fibres
of its base changes, and the fibres of the restriction of the morphism to an open subscheme.
The three transports, together with the identification of the sectioned locus `X⁰` of
`AlgebraicGeometry.ConnectedAlongSection` inside a single fibre, are collected here.

## Main results

* `AlgebraicGeometry.ConnectedComponentSection.geometricallyReduced_of_fibers` upgrades fibrewise
  geometric reducedness to geometric reducedness of the morphism.
* `AlgebraicGeometry.ConnectedComponentSection.pullback_fiber_geometricallyConnected` and
  `AlgebraicGeometry.ConnectedComponentSection.geometricallyConnected_of_pullback_fiber` move
  geometric connectedness of a fibre across a cartesian square, in both directions.
* `AlgebraicGeometry.ConnectedComponentSection.sectioned_locus_fiber_connected`: the trace of
  `X⁰` on a fibre is connected, being the connected component selected by the section.
* `AlgebraicGeometry.ConnectedComponentSection.sectioned_open_fiber_geometricallyConnected`: an
  open subscheme whose trace on a fibre is exactly that connected component, and which contains the
  section there, has geometrically connected fibre.

## Implementation notes

Both transports across a cartesian square run through
`AlgebraicGeometry.geometricallyConnected_iff_baseChange_fieldExtension` (Tag 054N) for the
residue field extension, after replacing the chosen limit pullback of the fibres by the given
cartesian square via `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`. The last result
instead uses the rational-point criterion
`AlgebraicGeometry.geometricallyConnected_of_connectedSpace_of_section` (Tag 04KV): the section
supplies a rational point of the fibre, and connectedness of the fibre as a space comes from
the identification of its underlying set with a connected component.

## References

* [Stacks Project, Tag 057I](https://stacks.math.columbia.edu/tag/057I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry.ConnectedComponentSection

/-- A morphism all of whose fibres are geometrically reduced is geometrically reduced. -/
theorem geometricallyReduced_of_fibers {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ y : Y, GeometricallyReduced (f.fiberToSpecResidueField y)) :
    GeometricallyReduced f := by
  rw [GeometricallyReduced.eq_geometrically, geometrically_iff_forall_fiberToSpecResidueField]
  exact fun y ↦ GeometricallyReduced.eq_geometrically ▸ h y

/-- In a cartesian square, the fibre of the left-hand vertical map over `y` is geometrically
connected iff the fibre of the right-hand vertical map over `g y` is. -/
theorem geometricallyConnected_fiber_iff_of_isPullback
    {P X Y Z : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback a b f g) (y : Y) :
    GeometricallyConnected (b.fiberToSpecResidueField y) ↔
      GeometricallyConnected (f.fiberToSpecResidueField (g y)) := by
  let : Algebra (Z.residueField (g y)) (Y.residueField y) :=
    (g.residueFieldMap y).hom.toAlgebra
  have hpb := isPullback_fiberToSpecResidueField_of_isPullback h y
  have e : Arrow.mk (b.fiberToSpecResidueField y) ≅
      Arrow.mk (pullback.snd (f.fiberToSpecResidueField (g y))
        (Spec.map (g.residueFieldMap y))) :=
    Arrow.isoMk' _ _ hpb.isoPullback (Iso.refl _)
      (hpb.isoPullback_hom_snd.trans (Category.comp_id _).symm)
  rw [geometricallyConnected_iff_baseChange_fieldExtension (Z.residueField (g y))
    (Y.residueField y) (f.fiberToSpecResidueField (g y)), GeometricallyConnected.eq_geometrically]
  exact MorphismProperty.arrow_mk_iso_iff (P := geometrically (ConnectedSpace ·)) e

/-- Geometric connectedness of a fibre of `f` passes to the corresponding fibre of the base
change of `f` along `g`. -/
theorem pullback_fiber_geometricallyConnected {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Z ⟶ Y) (z : Z)
    (hconn : GeometricallyConnected (f.fiberToSpecResidueField (g z))) :
    GeometricallyConnected ((pullback.snd f g).fiberToSpecResidueField z) :=
  (geometricallyConnected_fiber_iff_of_isPullback (IsPullback.of_hasPullback f g) z).2 hconn

/-- If a square is cartesian and a fibre of its right-hand vertical map is geometrically
connected, so is the corresponding fibre of its left-hand vertical map. -/
theorem geometricallyConnected_of_pullback_fiber
    {P X Y Z : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback a b f g) (y : Y)
    (hc : GeometricallyConnected (b.fiberToSpecResidueField y)) :
    GeometricallyConnected (f.fiberToSpecResidueField (g y)) :=
  (geometricallyConnected_fiber_iff_of_isPullback h y).1 hc

/-- The trace of the sectioned locus `X⁰` on a fibre is connected. -/
theorem sectioned_locus_fiber_connected
    (D : ConnectedAlongSection.{u}) (z : D.Y) :
    _root_.IsConnected ((D.f.fiberι z) ⁻¹' D.locus) := by
  rw [D.fiberι_preimage_locus]
  exact isConnected_connectedComponent

/-- An open subscheme `O` whose trace on the fibre over `z` is exactly the trace of the
sectioned locus `X⁰`, and which contains the value of the section at `z`, has geometrically
connected fibre over `z`. -/
theorem sectioned_open_fiber_geometricallyConnected
    (D : ConnectedAlongSection.{u}) (O : D.X.Opens) (z : D.Y)
    (hO : (D.f.fiberι z) ⁻¹' (O : Set D.X) = (D.f.fiberι z) ⁻¹' D.locus)
    (hs : D.s z ∈ (O : Set D.X)) :
    GeometricallyConnected ((O.ι ≫ D.f).fiberToSpecResidueField z) := by
  let j := pullback.map (O.ι ≫ D.f) (D.Y.fromSpecResidueField z)
    D.f (D.Y.fromSpecResidueField z) O.ι (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hrange : Set.range j = (D.f.fiberι z) ⁻¹' D.locus := by
    rw [open_fiber_comparison_range D.f O z, hO]
  have : ConnectedSpace ((O.ι ≫ D.f).fiber z) :=
    connectedSpace_of_isEmbedding_range_connected j
      (open_fiber_comparison_isOpenEmbedding D.f O z).isEmbedding
      (hrange ▸ sectioned_locus_fiber_connected D z)
  have ha : Set.range (D.Y.fromSpecResidueField z ≫ D.s) ⊆ Set.range O.ι := by
    rintro x ⟨w, rfl⟩
    rw [O.range_ι]
    simpa [Scheme.Hom.comp_apply] using hs
  let aO : Spec (D.Y.residueField z) ⟶ O := IsOpenImmersion.lift O.ι _ ha
  have hfac : aO ≫ (O.ι ≫ D.f) = D.Y.fromSpecResidueField z := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, D.section_fac,
      Category.comp_id]
  let sec : Spec (D.Y.residueField z) ⟶ (O.ι ≫ D.f).fiber z :=
    pullback.lift aO (𝟙 _) (by simpa using hfac)
  exact geometricallyConnected_of_connectedSpace_of_section
    ((O.ι ≫ D.f).fiberToSpecResidueField z) sec (pullback.lift_snd _ _ _)

end AlgebraicGeometry.ConnectedComponentSection

end
