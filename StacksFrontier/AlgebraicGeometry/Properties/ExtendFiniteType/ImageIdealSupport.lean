module

public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.QuasiCompactOpenIdeal

/-!
# The vanishing locus of the image of a morphism to the structure sheaf

`AlgebraicGeometry.idealSheafDataOfHom A φ` is the quasi-coherent sheaf of ideals which is the
image of a morphism `φ : A ⟶ 𝒪_X` out of a quasi-coherent module.  This file computes its
vanishing locus: a point lies outside it exactly when some section of `A`, over some open, has
a value under `φ` which does not vanish there.

## Main results

* `AlgebraicGeometry.notMem_support_idealSheafDataOfHom_iff`: the pointwise criterion.
* `AlgebraicGeometry.coe_support_idealSheafDataOfHom`: the same as an equality of sets, the
  vanishing locus being the complement of the union of the basic opens of the values of `φ`.
* `AlgebraicGeometry.notMem_support_idealSheafDataOfHom_of_mem_basicOpen` and
  `AlgebraicGeometry.exists_mem_basicOpen_of_notMem_support_idealSheafDataOfHom`: the two
  directions on their own.

## Implementation notes

The criterion quantifies over an arbitrary open `W` and a section of `A` over it, not over an
affine open.  Both forms are proved at once: the affine opens form a basis, so a value that
does not vanish at `x` may be restricted to an affine open containing `x` without vanishing
there (`AlgebraicGeometry.Scheme.basicOpen_res`), and conversely the affine open produced by the
criterion on `AlgebraicGeometry.Scheme.IdealSheafData.mem_support_iff_of_mem` is an open.

For the sheaf of ideals cut out by a global section of an invertible module, the vanishing locus
is computed in
`AlgebraicGeometry.Scheme.Modules.coe_support_idealSheafDataOfHom_evalGlobalHom`.

## References

* [Stacks Project, Tag 0F89](https://stacks.math.columbia.edu/tag/0F89)
* [Stacks Project, Tag 01PH](https://stacks.math.columbia.edu/tag/01PH)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPowerColimit

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- A point at which some value of `φ` does not vanish is outside the vanishing locus of the
image of `φ`. -/
theorem notMem_support_idealSheafDataOfHom_of_mem_basicOpen (A : X.Modules)
    [A.IsQuasicoherent] (φ : A ⟶ structureModule X) {x : X} {W : X.Opens} (a : Γ(A, W))
    (hx : x ∈ X.basicOpen (structureAppₗ φ W a)) :
    x ∉ (idealSheafDataOfHom A φ).support := by
  obtain ⟨V, hVaff, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hx
  have hVW' : V ≤ W := le_trans hVW (X.basicOpen_le _)
  have hmem : x ∈ X.basicOpen (structureAppₗ φ V (A.presheaf.map (homOfLE hVW').op a)) := by
    rw [← map_structureAppₗ φ hVW' a, Scheme.basicOpen_res]
    exact ⟨hxV, hx⟩
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hVaff⟩) hxV]
  exact fun hzero => (Scheme.mem_zeroLocus_iff _ _ _).mp hzero
    (structureAppₗ φ V (A.presheaf.map (homOfLE hVW').op a))
    ⟨A.presheaf.map (homOfLE hVW').op a, rfl⟩ hmem

/-- Outside the vanishing locus of the image of `φ` some value of `φ` does not vanish. -/
theorem exists_mem_basicOpen_of_notMem_support_idealSheafDataOfHom (A : X.Modules)
    [A.IsQuasicoherent] (φ : A ⟶ structureModule X) {x : X}
    (hx : x ∉ (idealSheafDataOfHom A φ).support) :
    ∃ (W : X.Opens) (a : Γ(A, W)), x ∈ X.basicOpen (structureAppₗ φ W a) := by
  obtain ⟨V, hVaff, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hVaff⟩) hxV,
    Scheme.mem_zeroLocus_iff] at hx
  push Not at hx
  obtain ⟨_, ⟨a, rfl⟩, hxy⟩ := hx
  exact ⟨V, a, hxy⟩

/-- **The vanishing locus of the image of a morphism to the structure sheaf.** A point lies
outside it exactly when some section of the source, over some open, has a value under the
morphism which does not vanish at that point. -/
theorem notMem_support_idealSheafDataOfHom_iff (A : X.Modules) [A.IsQuasicoherent]
    (φ : A ⟶ structureModule X) (x : X) :
    x ∉ (idealSheafDataOfHom A φ).support ↔
      ∃ (W : X.Opens) (a : Γ(A, W)), x ∈ X.basicOpen (structureAppₗ φ W a) :=
  ⟨exists_mem_basicOpen_of_notMem_support_idealSheafDataOfHom A φ,
    fun ⟨_, a, hx⟩ => notMem_support_idealSheafDataOfHom_of_mem_basicOpen A φ a hx⟩

/-- The vanishing locus of the image of `φ` is the complement of the union of the basic opens
of the values of `φ`. -/
theorem coe_support_idealSheafDataOfHom (A : X.Modules) [A.IsQuasicoherent]
    (φ : A ⟶ structureModule X) :
    (((idealSheafDataOfHom A φ).support : Closeds X) : Set X)
      = (⋃ (W : X.Opens) (a : Γ(A, W)), (X.basicOpen (structureAppₗ φ W a) : Set X))ᶜ := by
  ext x
  simpa only [Set.mem_compl_iff, Set.mem_iUnion, not_exists, SetLike.mem_coe] using
    (notMem_support_idealSheafDataOfHom_iff A φ x).not_right

end AlgebraicGeometry

end
