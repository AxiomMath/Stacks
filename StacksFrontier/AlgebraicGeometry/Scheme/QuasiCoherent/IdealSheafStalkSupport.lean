module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FibreStalkBridges

/-!
# The support of a quasi-coherent ideal sheaf is where its stalk is proper

Let `X` be a scheme and let `I` be a quasi-coherent sheaf of ideals on `X`, presented by its
affine-local ideal data `AlgebraicGeometry.Scheme.IdealSheafData`. Its support is the closed
subset cut out by `I`, and its stalk at a point `x` is the ideal
`AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal I x` of the local ring `𝒪_{X,x}`. This file
proves that the two determine each other pointwise: `x` lies outside the support exactly when
the stalk `I_x` is the unit ideal.

Equivalently: `𝒪_{V(I),x} = 𝒪_{X,x}/I_x` is the zero ring exactly for `x` off the closed
subscheme cut out by `I`. This is what turns a statement about two ideal sheaves agreeing away
from a closed set into a statement about their stalks, which is how such conditions are recorded
when the quotient `I/J` has no sheaf-level name.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support`: off the support
  the stalk is the unit ideal.
* `AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal_le_maximalIdeal_of_mem_support`: on the
  support the stalk is contained in the maximal ideal.
* `AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal_eq_top_iff`: the two together, as a
  characterization of the support.
* `AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal_eq_of_notMem_support`: two ideal sheaves
  have the same stalk at every point outside the union of their supports.

## Implementation notes

Both directions go through `AlgebraicGeometry.Scheme.mem_basicOpen`, which says that a section
is invertible in a local ring exactly at the points of its basic open set, together with
`AlgebraicGeometry.Scheme.IdealSheafData.mem_support_iff`, which describes the support as the
intersection of the zero loci of the ideals on all affine opens.

Off the support some ideal has a section not vanishing at `x`; its germ is then a unit of
`𝒪_{X,x}` lying in `I_x`, which forces `I_x = ⊤`. On the support every section of every ideal
on every affine neighbourhood of `x` vanishes at `x`, so every germ is a non-unit, hence lies in
the maximal ideal; the stalk is a supremum of images of such ideals and so is contained in the
maximal ideal, which is proper.

The point `x` of the affine open is produced by `AlgebraicGeometry.Scheme.basicOpen_le`: a
section's basic open set is contained in the open it is a section over, so membership of `x` in
the affine neighbourhood comes for free and is not a hypothesis.

No `@[stacks]` attribute is attached: this is a statement about Mathlib's representation of a
quasi-coherent sheaf of ideals, not a formalization of a tagged result.

## References

* [Stacks Project, Tag 01QX](https://stacks.math.columbia.edu/tag/01QX), quasi-coherent sheaves
  of ideals and the closed subschemes they cut out.
* [Stacks Project, Tag 01IN](https://stacks.math.columbia.edu/tag/01IN), the closed subscheme
  structure on the support.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **Off the support the stalk of an ideal sheaf is the unit ideal.** If `x` is not in the
support then some ideal of `I` has a section whose germ at `x` is a unit, and that germ lies in
`I_x`. -/
theorem stalkIdeal_eq_top_of_notMem_support {x : X} (hx : x ∉ I.support) :
    I.stalkIdeal x = ⊤ := by
  rw [mem_support_iff] at hx
  obtain ⟨U, hU⟩ := not_forall.mp hx
  rw [X.mem_zeroLocus_iff] at hU
  obtain ⟨a, ha, hxa⟩ := by simpa using not_forall.mp hU
  have hxU : x ∈ U.1 := X.basicOpen_le a hxa
  exact Ideal.eq_top_of_isUnit_mem _ (I.germ_mem_stalkIdeal U hxU ha)
    ((X.mem_basicOpen a x hxU).mp hxa)

/-- **On the support the stalk of an ideal sheaf is a proper ideal.** If `x` is in the support
then every section of every ideal of `I` vanishes at `x`, so every germ is a non-unit of the
local ring `𝒪_{X,x}` and the whole stalk lies in the maximal ideal. -/
theorem stalkIdeal_le_maximalIdeal_of_mem_support {x : X} (hx : x ∈ I.support) :
    I.stalkIdeal x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  refine iSup_le fun U => Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
  rw [mem_support_iff] at hx
  have hxa : x ∉ X.basicOpen a := by
    simpa using (X.mem_zeroLocus_iff (I.ideal U.1) x).mp (hx U.1) a ha
  refine IsLocalRing.mem_maximalIdeal _ |>.mpr (mem_nonunits_iff.mpr fun hu => hxa ?_)
  exact (X.mem_basicOpen a x U.2).mpr hu

/-- **The support of an ideal sheaf is exactly where its stalk is not the unit ideal.** -/
theorem stalkIdeal_eq_top_iff {x : X} : I.stalkIdeal x = ⊤ ↔ x ∉ I.support := by
  refine ⟨fun h hx => ?_, I.stalkIdeal_eq_top_of_notMem_support⟩
  exact (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk x)).ne_top
    (top_le_iff.mp (h ▸ I.stalkIdeal_le_maximalIdeal_of_mem_support hx))

/-- Two ideal sheaves have the same stalk at every point outside the union of their supports:
both stalks are the unit ideal there. -/
theorem stalkIdeal_eq_of_notMem_support (J : X.IdealSheafData) {x : X}
    (hI : x ∉ I.support) (hJ : x ∉ J.support) :
    I.stalkIdeal x = J.stalkIdeal x :=
  (I.stalkIdeal_eq_top_of_notMem_support hI).trans
    (J.stalkIdeal_eq_top_of_notMem_support hJ).symm

end AlgebraicGeometry.Scheme.IdealSheafData
