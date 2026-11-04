module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksCore.Tactic.StacksAttribute

/-!
# Connected components of fibres meeting a section

Let `f : X ⟶ Y` be a morphism of schemes with a specified section `s`. For each point `y : Y`,
the section determines a point of the scheme-theoretic fibre of `f` at `y`. We write `X⁰_y` for
the connected component of the fibre containing this point, and `X⁰` for the union of their
images in `X`.

## Main definitions

* `AlgebraicGeometry.ConnectedAlongSection` is a morphism of schemes equipped with a specified
  section.
* `AlgebraicGeometry.ConnectedAlongSection.sectionPoint` is the point induced by the section in
  a fibre.
* `AlgebraicGeometry.ConnectedAlongSection.fiberComponent` is the connected component `X⁰_y`.
* `AlgebraicGeometry.ConnectedAlongSection.locus` is the union `X⁰` inside `X`.

## Main results

* `AlgebraicGeometry.ConnectedAlongSection.fiberι_sectionPoint` identifies the fibre point with
  the value of the section in the source.
* `AlgebraicGeometry.ConnectedAlongSection.sectionPoint_mem_fiberComponent` records that the
  chosen point belongs to its connected component.
* `AlgebraicGeometry.ConnectedAlongSection.mem_locus` characterizes membership in `X⁰`.
* `AlgebraicGeometry.ConnectedAlongSection.fiberι_preimage_locus` identifies the trace of `X⁰`
  on a fibre with the connected component selected there by the section.

## Implementation notes

`ConnectedAlongSection` records exactly the morphisms `f` and `s` and the section equation. The
component `fiberComponent y` is a subset of the scheme-theoretic fibre `f.fiber y`. In the
definition of `locus`, it is mapped into `X` by the canonical morphism `f.fiberι y` before the
union over all `y` is taken.

## References

* [Stacks Project, Tag 055L](https://stacks.math.columbia.edu/tag/055L)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 055L (standing data).** A morphism of schemes together with a
specified section. -/
@[stacks 055L "the sectioned morphism"] structure ConnectedAlongSection where
  /-- The source scheme. -/
  X : Scheme.{u}
  /-- The target scheme. -/
  Y : Scheme.{u}
  /-- The morphism whose fibrewise connected components are considered. -/
  f : X ⟶ Y
  /-- The specified section of `f`. -/
  s : Y ⟶ X
  /-- The section equation. -/
  section_fac : s ≫ f = 𝟙 Y

namespace ConnectedAlongSection

/-- The point of the fibre over `y` determined by the section. -/
noncomputable def sectionPoint (D : ConnectedAlongSection) (y : D.Y) : D.f.fiber y :=
  (D.f.fiberHomeo y).symm ⟨D.s y, by
    change D.f (D.s y) = y
    rw [← Scheme.Hom.comp_apply, D.section_fac]
    rfl⟩

/-- **Stacks Project, Tag 055L (the fibrewise component).** The connected component of the
fibre over `y` which contains the point supplied by the section. -/
@[stacks 055L "the component X⁰_y", ega "IV 15.6.5", ega "IV 15.6.8"]
noncomputable def fiberComponent (D : ConnectedAlongSection) (y : D.Y) : Set (D.f.fiber y) :=
  connectedComponent (D.sectionPoint y)

/-- **Stacks Project, Tag 055L (the union).** The subset `X⁰ ⊆ X` obtained by taking, for
every `y : Y`, the image in `X` of the connected component `X⁰_y`. -/
@[stacks 055L "the union X⁰", ega "IV 15.6.4"]
noncomputable def locus (D : ConnectedAlongSection) : Set D.X :=
  ⋃ y, D.f.fiberι y '' D.fiberComponent y

/-- Mapping the point selected in the fibre back to `X` gives the value of the section. -/
@[simp] theorem fiberι_sectionPoint (D : ConnectedAlongSection) (y : D.Y) :
    D.f.fiberι y (D.sectionPoint y) = D.s y := D.f.fiberι_fiberHomeo_symm y _

/-- The point selected by the section belongs to the corresponding connected component. -/
theorem sectionPoint_mem_fiberComponent (D : ConnectedAlongSection) (y : D.Y) :
    D.sectionPoint y ∈ D.fiberComponent y := mem_connectedComponent

/-- A point belongs to `X⁰` precisely when it is the image of a point in one of the selected
connected components of the fibres. -/
theorem mem_locus (D : ConnectedAlongSection) (x : D.X) : x ∈ D.locus ↔
    ∃ (y : D.Y) (z : D.f.fiber y), z ∈ D.fiberComponent y ∧ D.f.fiberι y z = x := by
  simp [locus]

/-- The trace of the locus `X⁰` on the fibre over `y` is the connected component of that fibre
selected by the section. -/
theorem fiberι_preimage_locus (D : ConnectedAlongSection) (y : D.Y) :
    (D.f.fiberι y) ⁻¹' D.locus = D.fiberComponent y := by
  ext z
  rw [Set.mem_preimage, D.mem_locus]
  refine ⟨?_, fun hz => ⟨y, z, hz, rfl⟩⟩
  rintro ⟨y', z', hz', heq⟩
  obtain rfl : y' = y := by
    have hy : D.f (D.f.fiberι y' z') = y' := (D.f.fiberHomeo y' z').2
    rw [heq] at hy
    exact hy.symm.trans (D.f.fiberHomeo y z).2
  obtain rfl := (D.f.fiberι y').isEmbedding.injective heq
  exact hz'

end ConnectedAlongSection

end AlgebraicGeometry

end
