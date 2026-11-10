module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Section
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The locus of connected components meeting a section, topologically

Let `f : X ⟶ Y` be a morphism of schemes with a section `s`, as in Stacks 055L, and let
`X⁰ ⊆ X` be the union of the connected components of the fibres of `f` which contain the
corresponding value of `s`. The definition of `X⁰` in
`AlgebraicGeometry.ConnectedAlongSection.locus` goes through the scheme-theoretic fibres. This
file identifies it with a purely topological construction: `X⁰` is the union, over the points
`y` of `Y`, of the connected component of `s y` inside the subspace `f ⁻¹' {y}` of `X`.

## Main results

* `AlgebraicGeometry.ConnectedAlongSection.locus_eq_iUnion_connectedComponentIn` is the
  topological description of `X⁰`.
* `AlgebraicGeometry.ConnectedAlongSection.locus_inter_preimage` says that `X⁰` meets the fibre
  over `y` exactly in the connected component of `s y` in that fibre.
* `AlgebraicGeometry.ConnectedAlongSection.locus_eq_univ_iff` says that `X⁰` is everything
  precisely when every fibre of `f` is preconnected.
* `AlgebraicGeometry.isReduced_fiber_opens_ι_comp` transfers reducedness of a fibre to the
  restriction of the morphism to an open subscheme of the source.

## References

* [Stacks Project, Tag 055L](https://stacks.math.columbia.edu/tag/055L)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/-- A homeomorphism carries the connected component of a point onto the connected component
of its image. -/
theorem Homeomorph.image_connectedComponent {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (e : α ≃ₜ β) (x : α) :
    e '' connectedComponent x = connectedComponent (e x) := by
  refine subset_antisymm (e.continuous.image_connectedComponent_subset x) ?_
  have h := e.symm.continuous.image_connectedComponent_subset (e x)
  rw [e.symm_apply_apply] at h
  intro z hz
  exact ⟨e.symm z, h ⟨z, hz, rfl⟩, e.apply_symm_apply z⟩

namespace AlgebraicGeometry

namespace ConnectedAlongSection

/-- The value of the section at `y` lies in the fibre over `y`. -/
theorem section_mem_preimage (D : ConnectedAlongSection.{u}) (y : D.Y) :
    D.s y ∈ D.f ⁻¹' {y} := by
  change D.f (D.s y) = y
  rw [← Scheme.Hom.comp_apply, D.section_fac]
  rfl

/-- **The topological description of `X⁰`.** The union of the connected components of the
scheme-theoretic fibres containing the section is the union, over the points `y` of the base,
of the connected component of `s y` in the subspace `f ⁻¹' {y}` of `X`. -/
@[ega "IV 15.6.5", ega "IV 15.6.8", ega "IV 9.7.12"]
theorem locus_eq_iUnion_connectedComponentIn (D : ConnectedAlongSection.{u}) :
    D.locus = ⋃ y : D.Y, connectedComponentIn (D.f ⁻¹' {y}) (D.s y) := by
  refine Set.iUnion_congr fun y => ?_
  rw [connectedComponentIn_eq_image (D.section_mem_preimage y)]
  have h : ((D.f.fiberHomeo y) (D.sectionPoint y)) = ⟨D.s y, D.section_mem_preimage y⟩ := by
    apply Subtype.ext; simp
  rw [fiberComponent, ← h, ← Homeomorph.image_connectedComponent, ← Set.image_comp]
  rfl

/-- `X⁰` meets the fibre over `y` exactly in the connected component of `s y` in that fibre. -/
theorem locus_inter_preimage (D : ConnectedAlongSection.{u}) (y : D.Y) :
    D.locus ∩ D.f ⁻¹' {y} = connectedComponentIn (D.f ⁻¹' {y}) (D.s y) := by
  rw [locus_eq_iUnion_connectedComponentIn, Set.iUnion_inter]
  refine subset_antisymm (Set.iUnion_subset fun z => ?_) ?_
  · rintro x ⟨hx, hxy⟩
    have hz : z = y := by
      have hzx := connectedComponentIn_subset (D.f ⁻¹' {z}) (D.s z) hx
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hzx hxy
      rw [← hzx, ← hxy]
    subst hz
    exact hx
  · exact fun x hx => Set.mem_iUnion.2 ⟨y, hx, connectedComponentIn_subset _ _ hx⟩

/-- The section takes its values in `X⁰`; in particular `X⁰` is nonempty as soon as the base
is. -/
theorem section_mem_locus (D : ConnectedAlongSection.{u}) (y : D.Y) : D.s y ∈ D.locus := by
  rw [locus_eq_iUnion_connectedComponentIn]
  exact Set.mem_iUnion.2 ⟨y, mem_connectedComponentIn (D.section_mem_preimage y)⟩

/-- `X⁰` is all of `X` precisely when every fibre of `f` is preconnected. -/
theorem locus_eq_univ_iff (D : ConnectedAlongSection.{u}) :
    D.locus = Set.univ ↔ ∀ y : D.Y, _root_.IsPreconnected (D.f ⁻¹' {y}) := by
  constructor
  · intro h y
    have := D.locus_inter_preimage y
    rw [h, Set.univ_inter] at this
    rw [this]
    exact isPreconnected_connectedComponentIn
  · refine fun h => Set.eq_univ_of_forall fun x => ?_
    have := (h (D.f x)).subset_connectedComponentIn (D.section_mem_preimage _) subset_rfl
    rw [← D.locus_inter_preimage (D.f x)] at this
    exact (this rfl).1

end ConnectedAlongSection

/-- If the fibre of `f : X ⟶ Y` over `y` is reduced, then so is the fibre over `y` of the
restriction of `f` to an open subscheme `U` of `X`. -/
theorem isReduced_fiber_opens_ι_comp {X Y : Scheme.{u}} (U : X.Opens) (f : X ⟶ Y) (y : Y)
    [AlgebraicGeometry.IsReduced (f.fiber y)] :
    AlgebraicGeometry.IsReduced ((U.ι ≫ f).fiber y) := by
  have e₁ : (U.ι ≫ f).fiber y ≅ Limits.pullback U.ι (f.fiberι y) :=
    (Limits.pullbackRightPullbackFstIso f (Y.fromSpecResidueField y) U.ι).symm
  have e₂ : Limits.pullback U.ι (f.fiberι y) ≅ (f.fiberι y ⁻¹ᵁ U).toScheme :=
    (Limits.pullbackSymmetry _ _).trans (pullbackRestrictIsoRestrict (f.fiberι y) U)
  exact ObjectProperty.prop_of_iso (P := fun Z : Scheme.{u} => AlgebraicGeometry.IsReduced Z)
    (e₁.trans e₂).symm inferInstance

end AlgebraicGeometry

end
