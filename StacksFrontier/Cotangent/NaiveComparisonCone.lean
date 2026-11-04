module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import StacksFrontier.Cotangent.ConormalLowDegree

/-!
# The truncation at `-1` of the cone of `𝒥/𝒥² ⟶ Ω`

Let `A → B` be a ring map. Remark 08R7 observes that `Lπ_!(𝒥/𝒥² → Ω)` and `Lπ_!(Ω) = L_{B/A}`
have the same truncation `τ_{≥ -1}`, because `H₀(C_{B/A}, 𝒥/𝒥²)` and `H₁(C_{B/A}, 𝒥/𝒥²)` vanish.
This file carries that step on the standard resolution, where by Tag 08PS the two lower shrieks
are the complexes `Stacks.Cotangent.conormalComplex` and `CommAlgCat.cotangentComplex`: the
two-term complex of sheaves is replaced by the mapping cone of the map
`Stacks.Cotangent.conormalToCotangentComplex` of the two, and the statement becomes that the
cone inclusion of `L_{B/A}` is an isomorphism after `τ_{≥ -1}`.

## Main definitions

* `Stacks.Cotangent.cotangentCone`: the mapping cone of `𝒥/𝒥² ⟶ Ω` on the standard resolution.

## Main results

* `Stacks.Cotangent.isIso_truncGE_map_inr`: the cone inclusion `L_{B/A} ⟶ cone` becomes an
  isomorphism after `τ_{≥ -1}`.
* `Stacks.Cotangent.truncGEConeIso`: that isomorphism,
  `τ_{≥ -1} L_{B/A} ≅ τ_{≥ -1} cone`.

## Implementation notes

For a complex `K` in degrees `≤ 0` the two-term complex `(K → L)` of the source and the mapping
cone of `K ⟶ L` have the same truncation `τ_{≥ -1}`; the cone is used because the distinguished
triangle it sits in is what `CategoryTheory.Triangulated.TStructure.isIso₂_truncGE_map_of_isLE`
consumes. That lemma needs exactly `Stacks.Cotangent.isLE_conormalComplex`, the vanishing of the
conormal cohomology in degrees `0` and `-1`.

## References

* [Stacks Project, Tag 08R7](https://stacks.math.columbia.edu/tag/08R7)
* [Stacks Project, Tag 08PS](https://stacks.math.columbia.edu/tag/08PS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u v

namespace Stacks.Cotangent

open CommAlgCat

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)

/-- The mapping cone of the map `𝒥/𝒥² ⟶ Ω` of complexes on the standard resolution. Its
truncation `τ_{≥ -1}` is that of `L_{B/A}`. -/
abbrev cotangentCone : CochainComplex (ModuleCat.{max u v} B) ℤ :=
  CochainComplex.mappingCone (conormalToCotangentComplex A B)

/-- The inclusion of `L_{B/A}` into the cone. -/
abbrev cotangentConeInr : cotangentComplex A B ⟶ cotangentCone A B :=
  CochainComplex.mappingCone.inr (conormalToCotangentComplex A B)

/-- **The cone inclusion is an isomorphism after `τ_{≥ -1}`.** This is the step
`τ_{≥ -1} Lπ_!(𝒥/𝒥² → Ω) = τ_{≥ -1} L_{B/A}` of Remark 08R7, carried on the standard
resolution: the third term of the distinguished triangle is the conormal complex, which lies in
`D^{≤ -2}(B)`. -/
theorem isIso_truncGE_map_inr :
    IsIso ((DerivedCategory.TStructure.t.truncGE (-1)).map
      (DerivedCategory.Q.map (cotangentConeInr A B))) := by
  have : (conormalComplex A B).IsLE (-2) := isLE_conormalComplex A B
  exact DerivedCategory.TStructure.t.isIso₂_truncGE_map_of_isLE
    (DerivedCategory.Q.mapTriangle.obj
      (CochainComplex.mappingCone.triangle (conormalToCotangentComplex A B)))
    (DerivedCategory.mappingCone_triangle_distinguished _) (-2) (-1) (by norm_num)
    (inferInstance :
      DerivedCategory.TStructure.t.IsLE (DerivedCategory.Q.obj (conormalComplex A B)) (-2))

/-- **`τ_{≥ -1} L_{B/A} ≅ τ_{≥ -1} (𝒥/𝒥² → Ω)`**, the identification of Remark 08R7 on the
standard resolution. -/
def truncGEConeIso :
    (DerivedCategory.TStructure.t.truncGE (-1)).obj
        (DerivedCategory.Q.obj (cotangentComplex A B)) ≅
      (DerivedCategory.TStructure.t.truncGE (-1)).obj
        (DerivedCategory.Q.obj (cotangentCone A B)) :=
  haveI := isIso_truncGE_map_inr A B
  asIso ((DerivedCategory.TStructure.t.truncGE (-1)).map
    (DerivedCategory.Q.map (cotangentConeInr A B)))

end Stacks.Cotangent

end
