module

public import Mathlib.AlgebraicGeometry.Properties
public import StacksFrontier.AlgebraicGeometry.Meromorphic.TotalQuotientSheafSections

/-!
# A ratio of germs on an integral base is a meromorphic function near the point

The penultimate paragraph of [Stacks, Tag 0BD7] produces, at a point `x` of `X`, two nonzero
elements `g` and `r` of the local ring `𝒪_{Y, φ(x)}` of the base, and then works with the
meromorphic function `r / g` on a neighbourhood of `φ(x)`. This file performs that passage: the
two germs are spread to sections on one affine neighbourhood, and the denominator becomes a
unit of the total quotient sheaf there, so the ratio exists as a section of `𝒦_Y`.

Integrality of `Y` is what makes the denominator usable. A section of `𝒪_Y` is invertible in
`𝒦_Y` exactly when its germ at *every* point of its open set is a nonzerodivisor, and a nonzero
germ at the one point `φ(x)` says nothing about the other points in general. On an integral
scheme it does: on an affine open the denominator submonoid is the nonzerodivisors of the ring
of sections (`AlgebraicGeometry.submonoidPresheafOfStalk_obj_eq_nonZeroDivisors`), that ring is
a domain, and a section with a nonzero germ is nonzero.

## Main results

* `AlgebraicGeometry.mem_submonoidPresheafOfStalk_of_germ_ne_zero`: on an affine open of an
  integral scheme a section with one nonzero germ is a denominator of the total quotient
  presheaf.
* `AlgebraicGeometry.exists_isAffineOpen_nhds_mul_toTotalQuotientSheaf_eq`: two germs at a point
  of an integral scheme, the first nonzero, are the germs of sections `g'`, `r'` on one affine
  neighbourhood for which the ratio `r' / g'` exists in `𝒦_Y` there.

## Implementation notes

The neighbourhood is taken affine, and the two germs are spread over a *common* one, because
both are needed at once: affineness identifies the denominator submonoid, and a common open is
what makes the quotient a single section.

`TopCat.Presheaf.germ_exist` is a deprecated alias; the current spellings are
`TopCat.Presheaf.exists_germ_eq` and, for a section inside a prescribed neighbourhood,
`TopCat.Presheaf.exists_le_germ_eq`.

No tag attribute: [Stacks, Tag 0BD7] has no statement about one point of the base.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 02AR](https://stacks.math.columbia.edu/tag/02AR)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite

open scoped nonZeroDivisors

namespace AlgebraicGeometry

variable (Y : Scheme.{u}) [AlgebraicGeometry.IsIntegral Y]

/-- On an integral scheme a section over an open with one nonzero germ is a nonzerodivisor. -/
private theorem mem_nonZeroDivisors_of_germ_ne_zero {W : Y.Opens} {y : Y} (hyW : y ∈ W)
    (g : Γ(Y, W)) (hg : Y.presheaf.germ W y hyW g ≠ 0) : g ∈ (Γ(Y, W))⁰ := by
  have : Nonempty W := ⟨⟨y, hyW⟩⟩
  have : IsDomain Γ(Y, W) := IsIntegral.component_integral W
  exact mem_nonZeroDivisors_of_ne_zero fun h0 => hg (by rw [h0, map_zero])

/-- **On an integral scheme a section of an affine open with one nonzero germ is a
denominator.** The ring of sections is a domain, so the section is a nonzerodivisor, and on an
affine open the denominator submonoid of the total quotient presheaf is exactly the
nonzerodivisors. -/
theorem mem_submonoidPresheafOfStalk_of_germ_ne_zero {W : Y.Opens} (hW : IsAffineOpen W) {y : Y}
    (hyW : y ∈ W) (g : Γ(Y, W)) (hg : Y.presheaf.germ W y hyW g ≠ 0) :
    g ∈ (Y.presheaf.submonoidPresheafOfStalk fun z => (Y.presheaf.stalk z)⁰).obj (op W) := by
  rw [submonoidPresheafOfStalk_obj_eq_nonZeroDivisors Y W hW]
  exact mem_nonZeroDivisors_of_germ_ne_zero Y hyW g hg

/-- **A ratio of two germs is a section of `𝒦_Y` near the point.** Two elements of the local
ring at `y`, the first nonzero, are the germs of sections `g'`, `r'` of `𝒪_Y` on one affine
neighbourhood of `y`, with `g'` a nonzerodivisor there whose image in `𝒦_Y` is invertible; the
section `q` is the quotient `r' / g'`. -/
theorem exists_isAffineOpen_nhds_mul_toTotalQuotientSheaf_eq {y : Y}
    (g r : Y.presheaf.stalk y) (hg : g ≠ 0) :
    ∃ (W : Y.Opens) (hyW : y ∈ W), IsAffineOpen W ∧
      ∃ (g' r' : Γ(Y, W)) (q : Y.totalQuotientSheaf.presheaf.obj (op W)),
        Y.presheaf.germ W y hyW g' = g ∧ Y.presheaf.germ W y hyW r' = r ∧
          g' ∈ (Γ(Y, W))⁰ ∧
            q * Y.toTotalQuotientSheaf.hom.app (op W) g' =
              Y.toTotalQuotientSheaf.hom.app (op W) r' := by
  obtain ⟨W₁, hyW₁, g₁, hg₁⟩ := Y.presheaf.exists_germ_eq g
  obtain ⟨W₂, hW₂₁, hyW₂, r₂, hr₂⟩ := Y.presheaf.exists_le_germ_eq r hyW₁
  obtain ⟨W, hWaff, hyW, hWW₂⟩ := exists_isAffineOpen_mem_and_subset hyW₂
  obtain ⟨g', r', hgW, hrW⟩ : ∃ g' r' : Γ(Y, W),
      Y.presheaf.germ W y hyW g' = g ∧ Y.presheaf.germ W y hyW r' = r :=
    ⟨Y.presheaf.map (homOfLE ((hWW₂ : W ≤ W₂).trans hW₂₁)).op g₁,
      Y.presheaf.map (homOfLE (hWW₂ : W ≤ W₂)).op r₂,
      (TopCat.Presheaf.germ_res_apply Y.presheaf _ y hyW g₁).trans hg₁,
      (TopCat.Presheaf.germ_res_apply Y.presheaf _ y hyW r₂).trans hr₂⟩
  have hnz : g' ∈ (Γ(Y, W))⁰ := mem_nonZeroDivisors_of_germ_ne_zero Y hyW g' (by rwa [hgW])
  have hunit : IsUnit (Y.toTotalQuotientSheaf.hom.app (op W) g') := by
    rw [Scheme.toTotalQuotientSheaf_app_apply]
    exact (isUnit_toTotalQuotientPresheaf_app Y.presheaf
      (by rwa [submonoidPresheafOfStalk_obj_eq_nonZeroDivisors Y W hWaff])).map
      ((toSheafify (Opens.grothendieckTopology Y)
        Y.presheaf.totalQuotientPresheaf).app (op W)).hom
  obtain ⟨u, hu⟩ := hunit
  refine ⟨W, hyW, hWaff, g', r', (↑u⁻¹ : Y.totalQuotientSheaf.presheaf.obj (op W)) *
      Y.toTotalQuotientSheaf.hom.app (op W) r', hgW, hrW, hnz, ?_⟩
  rw [← hu, mul_comm (↑u⁻¹ : Y.totalQuotientSheaf.presheaf.obj (op W)), mul_assoc,
    u.inv_mul, mul_one]

end AlgebraicGeometry

end
